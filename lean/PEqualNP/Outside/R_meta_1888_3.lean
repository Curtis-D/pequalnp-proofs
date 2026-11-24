import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1888_3
    (relabel : ∀ (n : ℕ) (σ : Fin n → Fin n) (C : Circuit), FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ ∀ (x : Fin n → Bool) (b : Bool),
        D.eval (List.ofFn x ++ [b]) = C.eval (List.ofFn (x ∘ σ) ++ [b]))
    (binary : let F := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
    ∀ C : Circuit, FanInTwo C → (∀ x, C.eval (List.ofFn x) = F x) →
      15 ≤ C.gates.countP (fun g => g.op.eval [true]))
    (canonical : let F := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
        14 ≤ C.gates.countP (fun g => g.op.eval [true]) →
        (∀ i : Fin 10, ∃ g ∈ C.gates, i.val ∈ g.inputs) →
        ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) ≠ F x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro D σ fan size
  obtain ⟨C, fc, sc, eq⟩ := relabel 10 σ D fan
  let F := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  change ∃ x, D.eval (List.ofFn (x ∘ σ) ++ [x 0 || x 2]) ≠ F x
  apply Classical.byContradiction
  intro h
  have computes (x : Fin 10 → Bool) : C.eval (List.ofFn x ++ [x 0 || x 2]) = F x := by
    rw [eq x]
    exact Classical.byContradiction (fun different => h ⟨x, different⟩)
  have occurrence : ∀ i : Fin 10, ∃ g ∈ C.gates, i.val ∈ g.inputs := by
    let seed (i j : Fin 10) : Bool := ([36, 1, 129, 4, 8, 1, 2, 4, 8, 16] : List ℕ).getD i.val 0 |>.testBit j.val
    let augmented (i j : Fin 10) : Bool := decide (j = i) || seed i j
    have sensitivity : ∀ i : Fin 10, F (seed i) ≠ F (augmented i) ∧
        (seed i 0 || seed i 2) = (augmented i 0 || augmented i 2) := by decide +kernel
    have singletonFalse : ∀ i : Fin 10, F (fun j => decide (j = i)) = false := by decide +kernel
    intro i
    have earlier (gs : List Gate) (w : List Bool) (h : i.val < w.length) :
        (Circuit.mk gs i.val).eval w = w.getD i.val false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        change (Circuit.mk gs i.val).eval (w ++ [_]) = _
        rw [ih _ (by simp; omega)]
        exact List.getD_append _ _ _ _ h
    have output : C.output ≠ i.val := by
      intro h
      let z : Fin 10 → Bool := fun j => decide (j = i)
      have hcomp := computes z
      change (Circuit.mk C.gates C.output).eval _ = _ at hcomp
      rw [h, earlier C.gates _ (by simp; omega), List.getD_append _ _ _ _ (by simp)] at hcomp
      have far := singletonFalse i
      change F z = false at far
      change (List.ofFn z).getD i.val false = F z at hcomp
      rw [far] at hcomp
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt] at hcomp
      change decide (i = i) = false at hcomp
      simpa using hcomp
    by_contra missing
    have propagate (gs : List Gate) (a b : List Bool) (len : a.length = b.length)
        (agree : ∀ k : ℕ, k ≠ i.val → a.getD k false = b.getD k false)
        (unread : ∀ g ∈ gs, i.val ∉ g.inputs) :
        (Circuit.mk gs C.output).eval a = (Circuit.mk gs C.output).eval b := by
      induction gs generalizing a b with
      | nil => exact agree C.output output
      | cons g gs ih =>
        have pins : g.inputs.map (fun k => a.getD k false) = g.inputs.map (fun k => b.getD k false) := by
          apply List.map_congr_left
          intro k mem
          exact agree k (fun h => unread g List.mem_cons_self (h ▸ mem))
        change (Circuit.mk gs C.output).eval (a ++ [g.op.eval _]) =
            (Circuit.mk gs C.output).eval (b ++ [g.op.eval _])
        rw [pins]
        apply ih _ _ (by simp [len]) _ (fun t ht => unread t (List.mem_cons_of_mem _ ht))
        intro k other
        by_cases low : k < a.length
        · rw [List.getD_append _ _ _ _ low, List.getD_append _ _ _ _ (len ▸ low)]
          exact agree k other
        · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_not_gt low),
            List.getElem?_append_right (len ▸ Nat.le_of_not_gt low), len]
    have same := propagate C.gates (List.ofFn (seed i) ++ [seed i 0 || seed i 2])
      (List.ofFn (augmented i) ++ [augmented i 0 || augmented i 2]) (by simp) (by
        intro k other
        rw [(sensitivity i).2]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn, List.getElem?_ofFn]
        by_cases hk : k < 10
        · have d : (⟨k,hk⟩ : Fin 10) ≠ i := fun h => other (congrArg Fin.val h)
          simp [hk, augmented, d]
        · simp [hk]) (fun g hg hi => missing ⟨g, hg, hi⟩)
    change C.eval _ = C.eval _ at same
    rw [computes, computes] at same
    exact (sensitivity i).1 same

  let g : Gate := ⟨.or, [0, 2]⟩
  let whole : Circuit := ⟨g :: C.gates, C.output⟩
  have fwhole : FanInTwo whole := by
    intro a mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact ⟨by simp [g], by decide⟩
    · exact fc a mem
  have ew (x : Fin 10 → Bool) : whole.eval (List.ofFn x) = F x := by
    have first : g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false) = (x 0 || x 2) := by
      have evalOr (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
        cases a <;> cases b <;> rfl
      change GateOp.or.eval [(List.ofFn x).getD 0 false, (List.ofFn x).getD 2 false] = _
      rw [evalOr]
      simp [List.getD_eq_getElem?_getD]
    change C.eval (List.ofFn x ++ [g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false)]) = F x
    rw [first]
    exact computes x
  have low := binary whole fwhole ew
  have cnt : (g :: C.gates).countP (fun a => a.op.eval [true]) =
      C.gates.countP (fun a => a.op.eval [true]) + 1 := by
    rw [List.countP_cons]
    rfl
  change 15 ≤ (g :: C.gates).countP (fun a => a.op.eval [true]) at low
  rw [cnt] at low
  obtain ⟨x, different⟩ := canonical C fc (sc.trans_le size) (by omega) occurrence
  exact different (computes x)
