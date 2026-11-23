import Mathlib.Logic.Relation
import Mathlib.Tactic.SplitIfs
import PEqualNP.Defs

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def runWires (gs : List Gate) (init : List Bool) : List Bool :=
  gs.foldl stepWire init

private lemma getD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then b
      else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < w.length
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right h1]
    by_cases h2 : i = w.length
    · subst h2
      rw [ite_eq_left rfl, List.getElem?_append_right (le_refl _)]
      simp
    · rw [ite_eq_right h2, List.getElem?_eq_none]
      · rfl
      · simp only [List.length_append, List.length_singleton]
        omega

private lemma getD_of_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) :
    w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

private lemma runWires_getD_prefix (gs : List Gate) (init : List Bool) (i : ℕ)
    (hi : i < init.length) :
    (runWires gs init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    change (runWires gs (stepWire init g)).getD i false = init.getD i false
    have hlt : i < (stepWire init g).length := by
      simp only [stepWire, List.length_append, List.length_singleton]
      omega
    rw [ih (stepWire init g) hlt, stepWire, getD_append_singleton, ite_eq_left hi]

private lemma runWires_getD_gate (gs : List Gate) (init : List Bool) (j : ℕ)
    (hj : j < gs.length) :
    (runWires gs init).getD (init.length + j) false =
      (gs[j]).op.eval
        ((gs[j]).inputs.map fun i =>
          if i < init.length + j then (runWires gs init).getD i false else false) := by
  induction gs generalizing init j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      change (runWires gs (stepWire init g)).getD (init.length + 0) false =
        g.op.eval (g.inputs.map fun i =>
          if i < init.length + 0 then (runWires gs (stepWire init g)).getD i false else false)
      have hlen : init.length < (stepWire init g).length := by
        simp only [stepWire, List.length_append, List.length_singleton]
        omega
      rw [Nat.add_zero, runWires_getD_prefix gs (stepWire init g) init.length hlen]
      have hhead : (stepWire init g).getD init.length false =
          g.op.eval (g.inputs.map fun i => init.getD i false) := by
        rw [stepWire, getD_append_singleton, ite_eq_right (lt_irrefl _), ite_eq_left rfl]
      rw [hhead]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length
      · rw [ite_eq_left hi]
        have hi' : i < (stepWire init g).length := by
          simp only [stepWire, List.length_append, List.length_singleton]
          omega
        rw [runWires_getD_prefix gs (stepWire init g) i hi', stepWire,
          getD_append_singleton, ite_eq_left hi]
      · rw [ite_eq_right hi, getD_of_ge init i (not_lt.mp hi)]
    | succ k =>
      have hk : k < gs.length := by simpa using hj
      have hidx : init.length + (k + 1) = (stepWire init g).length + k := by
        simp only [stepWire, List.length_append, List.length_singleton]
        omega
      change (runWires gs (stepWire init g)).getD (init.length + (k + 1)) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
          if i < init.length + (k + 1) then (runWires gs (stepWire init g)).getD i false else false)
      rw [hidx]
      exact ih (stepWire init g) k hk

private lemma runWires_length (gs : List Gate) (w : List Bool) :
    (runWires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [runWires]
  | cons g gs ih =>
    change (runWires gs (stepWire w g)).length = _
    rw [ih]
    simp [stepWire, Nat.add_comm, Nat.add_left_comm]

private lemma inputValue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  change (runWires C.gates (List.ofFn x)).getD i false = _
  rw [runWires_getD_prefix _ _ _ (by simpa)]
  simp [List.getD_eq_getElem?_getD, hi]

private lemma gateValue (n j : ℕ) (C : Circuit) (g : Gate)
    (hg : C.gates[j]? = some g) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun b =>
        if b < n + j then (C.wires (List.ofFn x)).getD b false else false) := by
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp hg
  have h := runWires_getD_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn, hget] at h
  exact h

private def reads (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  ∃ (k : ℕ) (e : Gate), a = n + k ∧ C.gates[k]? = some e ∧ b ∈ e.inputs ∧ b < a

private lemma monotoneWire (n : ℕ) (C : Circuit) (i : ℕ)
    (hc : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      Relation.ReflTransGen (reads n C) i (n + j) →
      g.op = GateOp.and ∨ g.op = GateOp.or)
    (x x' : Fin n → Bool) (hxx : ∀ q, x q = true → x' q = true)
    (a : ℕ) (ha : Relation.ReflTransGen (reads n C) i a) :
    (C.wires (List.ofFn x)).getD a false = true →
      (C.wires (List.ofFn x')).getD a false = true := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    by_cases hinput : a < n
    · rw [inputValue C x a hinput, inputValue C x' a hinput]
      exact hxx _
    · let j := a - n
      have eq : a = n + j := by dsimp [j]; omega
      cases hg : C.gates[j]? with
      | none =>
        intro hv
        have hj := List.getElem?_eq_none_iff.mp hg
        change (runWires C.gates (List.ofFn x)).getD a false = true at hv
        rw [getD_of_ge _ _ (by rw [runWires_length, List.length_ofFn]; omega)] at hv
        cases hv
      | some g =>
        have hmono (b : ℕ) (hb : b ∈ g.inputs) :
            (if b < n + j then (C.wires (List.ofFn x)).getD b false else false) = true →
            (if b < n + j then (C.wires (List.ofFn x')).getD b false else false) = true := by
          split_ifs with hba
          · exact ih b (by omega) (ha.tail ⟨j, g, eq, hg, hb, by omega⟩)
          · simp
        have hop := hc j g hg (eq ▸ ha)
        rw [eq, gateValue n j C g hg x, gateValue n j C g hg x']
        rcases hop with hop | hop
        · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map]
          intro hv b hb
          obtain ⟨w, hw, rfl⟩ := hb
          exact hmono w hw (hv _ ⟨w, hw, rfl⟩)
        · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map]
          rintro ⟨_, ⟨w, hw, rfl⟩, hv⟩
          exact ⟨_, ⟨w, hw, rfl⟩, hmono w hw hv⟩

private lemma gateMono (n : ℕ) (C : Circuit)
    (hc : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : ℕ) (x y : Fin n → Bool) (hxy : ∀ q, x q = true → y q = true) :
    (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn y)).getD w false = true := by
  apply monotoneWire n C w _ x y hxy w .refl
  intro j g hg _
  exact (hc g (List.mem_of_getElem? hg)).1

private noncomputable def pins (C : Circuit) (Q : Finset ℕ) : Finset (ℕ × ℕ) :=
  Q.biUnion fun j => ((C.gates[j]?.map Gate.inputs).getD []).toFinset.image (Prod.mk j)

private lemma pinMem (C : Circuit) (Q : Finset ℕ) (j w : ℕ) :
    (j, w) ∈ pins C Q ↔ j ∈ Q ∧ ∃ g, C.gates[j]? = some g ∧ w ∈ g.inputs := by
  simp only [pins, Finset.mem_biUnion, Finset.mem_image, List.mem_toFinset, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, e, f⟩
    subst a
    subst b
    exact ⟨ha, by cases h : C.gates[j]? <;> simp_all⟩
  · rintro ⟨hj, g, hg, hw⟩
    exact ⟨j, hj, w, by simpa [hg], rfl, rfl⟩

private lemma pinCount (C : Circuit) (Q : Finset ℕ)
    (hc : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    (pins C Q).card ≤ 2 * Q.card := by
  unfold pins
  rw [Nat.mul_comm]
  apply Finset.card_biUnion_le_card_mul Q _ 2
  intro j _
  refine Finset.card_image_le.trans ?_
  cases hg : C.gates[j]? with
  | none => simp
  | some g =>
    simpa [hg, (hc g (List.mem_of_getElem? hg)).2] using g.inputs.toFinset_card_le

private lemma exitCount (n r : ℕ) (C : Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool)
    (hc : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hr : r ∈ Q)
    (hp : ∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g, C.gates[j']? = some g ∧ n + j ∈ g.inputs) :
    ((pins C Q).filter fun p => p.2 < n + p.1 ∧ ψ p.2 = true ∧
      p.2 ∉ Q.image (n + ·)).card ≤ Q.card + 1 := by
  classical
  let P := pins C Q
  let E := P.filter fun p => p.2 < n + p.1 ∧ ψ p.2 = true ∧ p.2 ∉ Q.image (n + ·)
  have select (j : ℕ) (hj : j ∈ Q.erase r) :
      ∃ a : ℕ, (a, n + j) ∈ P \ E := by
    obtain ⟨a, haq, _, g, hg, hw⟩ := hp j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
    refine ⟨a, Finset.mem_sdiff.mpr ⟨(pinMem C Q a (n+j)).mpr ⟨haq, g, hg, hw⟩, ?_⟩⟩
    intro he
    exact (Finset.mem_filter.mp he).2.2.2 (Finset.mem_image.mpr ⟨j, Finset.mem_of_mem_erase hj, rfl⟩)
  let f (j : ℕ) := if hj : j ∈ Q.erase r then ((select j hj).choose, n+j) else (0, n+j)
  have hle : (Q.erase r).card ≤ (P \ E).card := by
    apply Finset.card_le_card_of_injOn f
    · intro j hj
      change j ∈ Q.erase r at hj
      dsimp only [f]
      rw [dite_eq_left hj]
      exact (select j hj).choose_spec
    · intro a ha b hb eq
      change a ∈ Q.erase r at ha
      change b ∈ Q.erase r at hb
      have h := congrArg Prod.snd eq
      dsimp only [f] at h
      rw [dite_eq_left ha, dite_eq_left hb] at h
      simpa using h
  have hP := pinCount C Q hc
  have hE : E ⊆ P := Finset.filter_subset _ _
  rw [Finset.card_sdiff_of_subset hE, Finset.card_erase_of_mem hr] at hle
  have := Finset.card_le_card hE
  have := Finset.card_pos.mpr (show Q.Nonempty from ⟨r, hr⟩)
  change E.card ≤ Q.card + 1
  change P.card ≤ 2 * Q.card at hP
  omega


theorem L_meta_693 : ∀ (n k r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD (n + r) false = false) → r ∈ Q → (∀ j ∈ Q, j < C.size) → (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) → (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) → (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = true → ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S) → ψ (n + r) = true → k ≤ Q.card := by
  classical
  intro n k r S C Q ψ hc hpromise hr hvalid hparent hlabel hout hroot
  let E := (pins C Q).filter fun p => p.2 < n + p.1 ∧ ψ p.2 = true ∧
    p.2 ∉ Q.image (n + ·)
  have available (p : E) : ∃ a : Fin n, a ∉ S ∧
      (C.wires (List.ofFn (fun q : Fin n => decide (q = a)))).getD p.val.2 false = true := by
    have hm := (Finset.mem_filter.mp p.property).2
    have hbad := hout p.val.2 (fun j hj eq => hm.2.2 (Finset.mem_image.mpr ⟨j, hj, eq.symm⟩)) hm.2.1
    by_contra h
    apply hbad
    intro a ha
    exact Classical.byContradiction fun haS => h ⟨a, haS, (Finset.mem_filter.mp ha).2⟩
  let T := E.attach.image fun p => (available p).choose
  let x : Fin n → Bool := fun a => decide (a ∈ T)
  have hT : T.card ≤ Q.card + 1 := by
    calc
      T.card ≤ E.attach.card := Finset.card_image_le
      _ = E.card := Finset.card_attach
      _ ≤ Q.card + 1 := exitCount n r C Q ψ hc hr hparent
  have hmiss : ∀ a ∈ S, x a = false := by
    intro a ha
    simp only [x, decide_eq_false_iff_not]
    intro h
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h
    exact (available p).choose_spec.1 ha
  have exitTrue (j w : ℕ) (hm : (j, w) ∈ E) :
      (C.wires (List.ofFn x)).getD w false = true := by
    let p : E := ⟨(j,w), hm⟩
    apply gateMono n C hc w (fun q => decide (q = (available p).choose)) x
    · intro q h
      have eq := of_decide_eq_true h
      subst q
      exact decide_eq_true (Finset.mem_image.mpr ⟨p, Finset.mem_attach E p, rfl⟩)
    · exact (available p).choose_spec.2
  have inside : ∀ j ∈ Q, ψ (n+j) = true →
      (C.wires (List.ofFn x)).getD (n+j) false = true := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj ht
      have hjlt : j < C.gates.length := hvalid j hj
      let g := C.gates[j]
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
      have args (w : ℕ) (hw : w ∈ g.inputs) :
          (if w < n+j then ψ w else false) = true →
          (if w < n+j then (C.wires (List.ofFn x)).getD w false else false) = true := by
        by_cases hlt : w < n+j
        · simp only [ite_eq_left hlt]
          intro htrue
          by_cases hq : ∃ a ∈ Q, w = n+a
          · obtain ⟨a, ha, rfl⟩ := hq
            exact ih a (by omega) ha htrue
          · exact exitTrue j w (Finset.mem_filter.mpr
              ⟨(pinMem C Q j w).mpr ⟨hj, g, hg, hw⟩, hlt, htrue,
                fun hmem => by
                  obtain ⟨a, ha, eq⟩ := Finset.mem_image.mp hmem
                  exact hq ⟨a, ha, eq.symm⟩⟩)
        · simp [hlt]
      rw [hlabel j hj g hg] at ht
      rw [gateValue n j C g hg x]
      rcases (hc g (List.mem_of_getElem? hg)).1 with hop | hop
      · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map] at ht ⊢
        rintro _ ⟨w, hw, rfl⟩
        exact args w hw (ht _ ⟨w, hw, rfl⟩)
      · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map] at ht ⊢
        obtain ⟨_, ⟨w, hw, rfl⟩, ht⟩ := ht
        exact ⟨_, ⟨w, hw, rfl⟩, args w hw ht⟩
  by_contra! hk
  have hsmall : (Finset.univ.filter fun q : Fin n => x q = true).card ≤ k := by
    have eq : (Finset.univ.filter fun q : Fin n => x q = true) = T := by
      ext q
      simp [x]
    rw [eq]
    omega
  have h := inside r hr hroot
  rw [hpromise x hsmall hmiss] at h
  cases h

end PEqualNP.Outside
