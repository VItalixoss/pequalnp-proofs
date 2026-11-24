import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3250_271
    (unmasked :
      let f := fun x : Fin 9 → Bool => ([1, 11, 21, 31, 36, 5, 15, 25, 35, 52, 62, 77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))
      let W := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x, C.eval (W x) ≠ f x)
    (orCase :
      let f := fun x : Fin 9 → Bool => ([1, 11, 21, 31, 36, 5, 15, 25, 35, 52, 62, 77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))
      let W := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
      ∀ (j : Fin 9) (C : Circuit) (k : ℕ),
        let w := fun x => (C.wires (W x)).getD k false
        let m := fun x => x j || w x
        j ≠ 0 → j ≠ 6 → FanInTwo C → C.size ≤ 13 → 10 ≤ k → k < 10 + C.size →
        (∀ g ∈ C.gates.take (k + 1 - 10), j.val ∉ g.inputs) →
        (∀ x, f (Function.update x j false) ≠ f (Function.update x j true) →
          w (Function.update x j false) = !true) →
        (∃ x, m x ≠ x j) →
        ∃ x, m x = x j ∧ C.eval (W x) ≠ f x)
    (andCase :
      let f := fun x : Fin 9 → Bool => ([1, 11, 21, 31, 36, 5, 15, 25, 35, 52, 62, 77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))
      let W := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
      ∀ (j : Fin 9) (C : Circuit) (k : ℕ),
        let w := fun x => (C.wires (W x)).getD k false
        let m := fun x => x j && w x
        j ≠ 0 → j ≠ 6 → FanInTwo C → C.size ≤ 13 → 10 ≤ k → k < 10 + C.size →
        (∀ g ∈ C.gates.take (k + 1 - 10), j.val ∉ g.inputs) →
        (∀ x, f (Function.update x j false) ≠ f (Function.update x j true) →
          w (Function.update x j false) = !false) →
        (∃ x, m x ≠ x j) →
        ∃ x, m x = x j ∧ C.eval (W x) ≠ f x)
    : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ) (x6 : Bool),   x2 ≠ (0 : Fin (9 : ℕ)) →     x2 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 < x4 →               x4 ≤ (10 : ℕ) + x3.size →                 (∀ x14 ∈ List.take (x4 - (10 : ℕ)) x3.gates, ↑x2 ∉ x14.inputs) →                   (∀ (x15 : Fin (9 : ℕ) → Bool),                       have x16 : Fin (9 : ℕ) → Bool := Function.update x15 x2 Bool.false;                       x1 x16 ≠ x1 (Function.update x15 x2 Bool.true) → (x3.wires (List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))])).getD x5 Bool.false = !x6) →                     ∃ (x16 : Fin (9 : ℕ) → Bool),                       have x17 : List Bool := List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))];                       have x18 : Bool := (x3.wires x17).getD x5 Bool.false;                       x3.eval (x17.set (↑x2) (if x6 = Bool.true then x16 x2 || x18 else x16 x2 && x18)) ≠ x1 x16 := by
  let inputWires (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 6]
  let control (C : Circuit) (k : ℕ) (x : Fin 9 → Bool) :=
    (C.wires (inputWires x)).getD k false
  dsimp only
  intro j C cut k pol h0 h6 hfan hsize hk hkc hcut hread hinactive
  let f : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => ([1, 11, 21, 31, 36, 5, 15, 25, 35, 52, 62, 77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))
  change ∀ x, f (Function.update x j false) ≠ f (Function.update x j true) →
    control C k (Function.update x j false) = !pol at hinactive
  change ∃ x, C.eval ((inputWires x).set j.val
    (if pol = true then x j || control C k x else x j && control C k x)) ≠ f x
  let forceVal (x : Fin 9 → Bool) :=
    if pol = true then x j || control C k x else x j && control C k x
  change ∃ x, C.eval ((inputWires x).set j.val (forceVal x)) ≠ f x
  have hadm : ∀ g ∈ C.gates.take (k + 1 - 10), j.val ∉ g.inputs := by
    intro g hg
    apply hread g
    exact List.mem_of_mem_take (by
      rw [List.take_take, Nat.min_eq_left (by omega)]
      exact hg : g ∈ (C.gates.take (cut - 10)).take (k + 1 - 10))
  have htest : ∃ x, forceVal x = x j ∧ C.eval (inputWires x) ≠ f x := by
    by_cases h : ∃ x, forceVal x ≠ x j
    · cases pol
      · exact andCase j C k h0 h6 hfan hsize hk (by omega) hadm hinactive h
      · exact orCase j C k h0 h6 hfan hsize hk (by omega) hadm hinactive h
    · obtain ⟨x, hx⟩ := unmasked C hfan hsize
      exact ⟨x, by simpa using not_exists.mp h x, hx⟩
  obtain ⟨x, hx, hbad⟩ := htest
  refine ⟨x, ?_⟩
  rw [hx]
  have hj : j.val < (inputWires x).length := by
    have := j.isLt
    simp [inputWires]
    omega
  have hv : (inputWires x)[j.val]'hj = x j := by
    unfold inputWires
    rw [List.getElem_append_left (by simp), List.getElem_ofFn]
  rw [← hv, List.set_getElem_self]
  exact hbad
