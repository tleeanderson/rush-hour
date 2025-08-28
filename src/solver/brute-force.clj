(ns rush-hour.solver.brute-force
  (:require [rush-hour.base.board :as board]))

(defn movable-vehs
  "Given board-veh, invokes move-all-vehicles by default and
   returns [[vehicle-key [m1 m2 m3...]]...]. every [m1 m2 m3...]
   is guaranteed to be non empty."
  ([board-veh] (movable-vehs board-veh board/move-all-vehicles))
  ([board-veh
    move-av-func] (vec (filter (fn [[ck moves]]
                                 (not (empty? moves)))
                               (move-av-func board-veh)))))

(defn vec-to-map
  "Takes in [[k1 v] [k2 v]] and returns {:k1 v :k2 v}."
  [in-vec]
  (reduce (fn [agg [k v]]
            (assoc agg k v)) {} in-vec))

(defn coords-to-moves
  "Takes in [[p1] [p2]...] and returns {[p1 p2]...} as each
   pair of points is a move."
  ([coords]
   (coords-to-moves coords set))
  ([coords out-func]
   (out-func (mapv #(vec %) (partition 2 coords)))))

(defn freed-vehs
  "Returns a {:k1 :k2 :k3...} which represents the vehicles that
   are freed to move from an old state to a new state. new-moves
   and old-moves are the moves from the old and new states respectively."
  ([new-moves old-moves]
   (freed-vehs new-moves old-moves vec-to-map))
  ([new-moves old-moves vtm-func]
   (clojure.set/difference (set (keys (vtm-func new-moves)))
                           (set (keys (vtm-func old-moves))))))

(defn freed-locs
  "Returns a {:k1 :k2 :k3...} which represents vehicles that can move
   across two states, but can move to a different spot in the new state.
   new-moves and old-moves are the moves from the old and new states
   respectively."
  ([new-moves old-moves veh-mov-key]
   (freed-locs new-moves old-moves veh-mov-key vec-to-map coords-to-moves))
  ([new-moves old-moves veh-mov-key vtm-func ctm-func]
   (let [[nm om] (map #(vtm-func %) [new-moves old-moves])]
     (clojure.set/difference (set (filter some? (map (fn [k]
                          (when (not (empty? (apply clojure.set/difference (map #(ctm-func (k %)) [nm om]))))
                            k)) (clojure.set/intersection (set (keys nm)) (set (keys om)))))) #{veh-mov-key}))))

(defn optimal-moves
  "Uses freed-vehs and freed-locs among others to compute the optimal-moves
   in a given state (i.e. board-veh). The obj-k's moves are left alone as
   those are handled elsewhere. Shape of result is [[k [m1 m2 m3...]]...]."
  ([board-veh obj-k]
   (optimal-moves board-veh
                  (movable-vehs board-veh)
                  movable-vehs
                  board/invoke-move
                  freed-vehs
                  freed-locs
                  board/end-state?
                  obj-k))
  ([board-veh
    moves
    move-av-func
    inv-move-func
    fvs-func
    fl-func
    es-func
    obj-k]
   (filter (fn [[ck mvs]]
             (not (empty? mvs)))
           (map (fn [[ck ms]]
                  [ck (if (= ck obj-k)
                        (vec ms)
                        (vec (apply concat
                                  (filter (fn [[sp ep]]
                                            (let [n-bv (inv-move-func board-veh ck [sp ep])
                                                  new-moves (move-av-func n-bv)
                                                  end? (es-func n-bv obj-k)]
                                              (or (> (apply + (map #(count %) [(fvs-func new-moves moves)
                                                                               (fl-func new-moves moves ck)])) 0) end?)))
                                          (partition 2 ms)))))]) moves))))
(defn compress-moves
  "Provides the meaning of equality between two moves by hashing their freed-vehs and freed-locs
   sets. The last move is taken for a given vehicle. By default, the last move of obj-k is taken
   as this has produced the best results so far. Shape of return is [[k [m1 m2 m3...]]...]."
  ([board-veh obj-k]
   (compress-moves board-veh (optimal-moves board-veh obj-k) movable-vehs freed-vehs freed-locs board/invoke-move obj-k))
  ([board-veh moves move-av-func fv-func fl-func inv-move-func obj-k]
   (map (fn [[ck mvs]]
          [ck (if (= ck obj-k)
                (vec (take-last 2 mvs))
                (vec (apply concat (vals (reduce (fn [agg mvs]
                                                   (assoc agg [(second mvs) (last mvs)] (first mvs)))
                                                 {} (map (fn [mv]
                                                           (let [n-bv (inv-move-func board-veh ck mv)
                                                                 n-moves (move-av-func n-bv)]
                                                             [mv (fv-func n-moves board-veh)
                                                              (fl-func n-moves board-veh ck)]))
                                                         (partition 2 mvs)))))))]) moves)))

(defn flatten-moves
  "Takes in [[ck [m1 m2 m3...]]...] and returns [[ck m1] [ck m2] [ck m3]...]."
  [moves]
  (apply concat (map (fn [[ck mvs]]
                       (let [ms (partition 2 mvs)]
                         (map (fn [k m]
                                [k (vec m)]) (take (count ms) (repeat ck)) ms))) moves)))

(defn enumerate-paths
  "Returns all of the paths whose depth is equal to or less than the depth
   of the first path found. Shape of return is [[p1] [p2] [p3]...]."
  ([board-veh obj-k]
   (enumerate-paths board-veh (flatten-moves (compress-moves board-veh obj-k)) board/end-state?
                    compress-moves flatten-moves board/invoke-move obj-k [] #{} #{board-veh} 0 Integer/MAX_VALUE))
  ([board-veh moves es-func? gen-moves-func flat-func inv-move-func obj-k curr-path all-paths traveled
    depth max-depth]
   (if (> depth max-depth)
     [all-paths max-depth]
     (if (es-func? board-veh obj-k)
       (do
         (println "hit end state, depth: " depth)
         [(conj all-paths curr-path) depth])
       ((fn [[[ck mp] & res] trav cp aps md]
          (if (nil? ck)
            [aps md]
            (let [n-bv (inv-move-func board-veh ck mp)]
              (if (contains? trav n-bv)
                (recur res trav cp aps md)
                (let [[n-aps nd] (enumerate-paths n-bv (flat-func (gen-moves-func n-bv obj-k)) es-func?
                                             gen-moves-func flat-func inv-move-func obj-k (conj cp [ck mp])
                                             aps (conj trav n-bv) (inc depth) md)]
                  (recur res trav cp (clojure.set/union aps n-aps) nd))))))
        moves traveled curr-path all-paths max-depth)))))


(defn bf-enumerate-paths
  ([board-veh obj-k]
   (bf-enumerate-paths board-veh (flatten-moves (compress-moves board-veh obj-k)) board/end-state?
                       compress-moves flatten-moves board/invoke-move obj-k [] #{} #{board-veh} 0 Integer/MAX_VALUE))
  ([board-veh moves es-func? gen-moves-func flat-func inv-move-func obj-k curr-path all-paths traveled
    depth max-depth]
   (let [frontier (set (map (fn [[ck mp :as mv]]
                              [mv (inv-move-func board-veh ck mp)]) moves))
         n-trv (clojure.set/union traveled (map #(second %) frontier))
         end-boards (set (filter #(es-func? (second %) :unused)
                                 frontier))
         non-end-boards (clojure.set/difference frontier end-boards)
         aps-with-ebs [(clojure.set/union all-paths (set (map (fn [[mv _]]
                                                                (conj curr-path mv)) end-boards))) depth]]
     ((fn [[[[ck mp :as mv] n-bv] & res] trav cp aps md]
        (if (nil? ck)
          [aps md]
          (let [[n-aps nd] (bf-enumerate-paths n-bv (flat-func (gen-moves-func n-bv obj-k)) es-func?
                                               gen-moves-func flat-func inv-move-func obj-k (conj cp [ck mp])
                                               aps (conj trav n-bv) (inc depth) max-depth)]
            (recur res trav cp (clojure.set/union aps n-aps) nd))))
      non-end-boards traveled curr-path all-paths max-depth))
   ))
