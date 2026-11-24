import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1940_1
  (binary : let F := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    ∀ C : Circuit, FanInTwo C → (∀ x, C.eval (List.ofFn x) = F x) →
      13 ≤ C.gates.countP (fun g => g.op.eval [true]))
  (monotone : let F := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    ∀ (i : Fin 11) (D : Circuit), FanInTwo D → D.size = 13 →
      (∀ g ∈ D.gates, g.op ≠ .not) → ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [!(x 0)]
        D.eval (w ++ [!(w.getD i.val false)]) ≠ F x) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  classical
  intro pins hp D hf hs
  let F := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let w (x : Fin 9 → Bool) := List.ofFn x ++ [!(x 0)]
  let suffix (x : Fin 9 → Bool) := w x ++ [GateOp.not.eval (pins.map fun i => (w x).getD i false)]
  change ∃ x, D.eval (suffix x) ≠ F x
  apply Classical.byContradiction
  intro h
  have he (x : Fin 9 → Bool) : D.eval (suffix x) = F x :=
    Classical.byContradiction (fun hn => h ⟨x, hn⟩)
  let firstG : Gate := ⟨.not, [0]⟩
  let secondG : Gate := ⟨.not, pins⟩
  let C : Circuit := ⟨firstG :: secondG :: D.gates, D.output⟩
  have hfan : FanInTwo C := by
    intro g hg
    change g ∈ firstG :: secondG :: D.gates at hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · exact ⟨by simp [firstG], by decide⟩
    · exact ⟨by simp [secondG], hp⟩
    · exact hf g hg
  have hfull (x : Fin 9 → Bool) : C.eval (List.ofFn x) = F x := by
    exact he x
  have lower := binary C hfan hfull
  have counted : 13 ≤ D.gates.countP (fun g => g.op.eval [true]) := by
    have off : GateOp.not.eval [true] = false := rfl
    simpa only [C, firstG, secondG, List.countP_cons, off,
      Bool.false_eq_true, ite_false, Nat.add_zero, Nat.zero_add] using lower
  change D.gates.length ≤ 13 at hs
  have upper : D.gates.countP (fun g => g.op.eval [true]) ≤ D.gates.length :=
    List.countP_le_length
  have hsize : D.size = 13 := by change D.gates.length = 13; omega
  have noNot (g : Gate) (hg : g ∈ D.gates) (hn : g.op = .not) : False := by
    have bad : ∃ a ∈ D.gates, a.op.eval [true] = false := ⟨g, hg, by rw [hn]; rfl⟩
    have less := List.countP_lt_length_iff.mpr bad
    omega
  let i : Fin 11 := ⟨min (pins.headD 10) 10, by omega⟩
  obtain ⟨x, different⟩ := monotone i D hf hsize noNot
  have hw : (w x).length = 10 := by simp [w]
  have normalize : GateOp.not.eval (pins.map fun j => (w x).getD j false) = !((w x).getD i.val false) := by
    cases pins with
    | nil =>
      change (!false) = !((w x).getD 10 false)
      rw [List.getD_eq_default _ _ (by omega)]
    | cons j js =>
      change (!((w x).getD j false)) = !((w x).getD (min j 10) false)
      by_cases hj : j ≤ 10
      · rw [Nat.min_eq_left hj]
      · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ (show (w x).length ≤ j by omega),
          List.getD_eq_default _ _ (show (w x).length ≤ 10 by omega)]
  apply different
  simpa only [suffix, normalize] using he x
