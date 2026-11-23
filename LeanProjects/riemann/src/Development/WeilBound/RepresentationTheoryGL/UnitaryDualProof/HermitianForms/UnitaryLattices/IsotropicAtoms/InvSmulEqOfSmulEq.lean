import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.IsotropicAtoms.FinSumFinEquivSymmDite
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.IsotropicAtoms.ChartRestriction

noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Atom

open PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Subs

variable {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)

def stabSub (v : V) : AddSubgroup (Fin (m + 1) → k) where
  carrier := {x | π (colEl k m N h x) v = v}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [colEl_add, map_mul, Module.End.mul_apply, hb, ha]
  zero_mem' := by simp [colEl_zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, ← colEl_add, neg_add_cancel, colEl_zero, map_one, Module.End.one_apply]

variable (k) in

def charSub {n : ℕ} (ψ : AddChar k Circle) (ξ : Fin n → k) : AddSubgroup (Fin n → k) where
  carrier := {x | ψ (ξ ⬝ᵥ x) = 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [dotProduct_add, AddChar.map_add_eq_mul, ha, hb, one_mul]
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [dotProduct_neg, AddChar.map_neg_eq_inv, ha, inv_one]

variable (k) in

def annSub {n : ℕ} (ψ : AddChar k Circle) (A : AddSubgroup (Fin n → k)) : AddSubgroup (Fin n → k) where
  carrier := {ξ | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1}
  add_mem' {a b} ha hb := by
    intro x hx
    rw [add_dotProduct, AddChar.map_add_eq_mul, ha x hx, hb x hx, one_mul]
  zero_mem' := by intro x _; simp
  neg_mem' {a} ha := by
    intro x hx
    rw [neg_dotProduct, AddChar.map_neg_eq_inv, ha x hx, inv_one]

end Subs

section Api

variable {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
  (ψ : AddChar k Circle)

theorem inv_smul_eq_of_smul_eq_alt {M : Type} [AddCommGroup M] [Module ℂ M] {a b : ℂ} {x y : M} (ha : a ≠ 0) (hb : b ≠ 0)
    (hk : b • x = a • y) : a⁻¹ • x = b⁻¹ • y := by
  rw [← inv_smul_smul₀ hb x, hk, smul_smul, smul_smul]
  congr 1
  field_simp

theorem transversal_neg {X : Type} [AddCommGroup X] [DecidableEq X] {A H : AddSubgroup X} {T : Finset X}
    (hT : ∀ t ∈ T, t ∈ A) (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) :
    (∀ t ∈ T.image Neg.neg, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T.image Neg.neg ∧ a - t ∈ H := by
  refine ⟨fun t ht => ?_, fun a ha => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact A.neg_mem (hT s hs)
  · obtain ⟨s, ⟨hs, hs'⟩, hu⟩ := hTr (-a) (A.neg_mem ha)
    refine ⟨-s, ⟨Finset.mem_image_of_mem _ hs, ?_⟩, ?_⟩
    · have := H.neg_mem hs'
      rwa [show -(-a - s) = a - -s by abel] at this
    · rintro t ⟨ht, ht'⟩
      obtain ⟨s', hs'', rfl⟩ := Finset.mem_image.mp ht
      have := hu s' ⟨hs'', by
        have := H.neg_mem ht'
        rwa [show -(a - -s') = -a - s' by abel] at this⟩
      rw [this]

theorem conj_psi (y : k) : starRingEnd ℂ ((ψ y : Circle) : ℂ) = ((ψ (-y) : Circle) : ℂ) := by
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

theorem avgF_add {ξ : Fin (m + 1) → k} {v : V} (a b : Fin (m + 1) → k) (hb : π (colEl k m N h b) v = v)
    (hb' : ψ (ξ ⬝ᵥ b) = 1) :
    (starRingEnd ℂ ((ψ (ξ ⬝ᵥ (a + b)) : Circle) : ℂ)) • π (colEl k m N h (a + b)) v =
      (starRingEnd ℂ ((ψ (ξ ⬝ᵥ a) : Circle) : ℂ)) • π (colEl k m N h a) v := by
  rw [dotProduct_add, AddChar.map_add_eq_mul, hb', mul_one, colEl_add, map_mul, Module.End.mul_apply, hb]

theorem isOpen_stabSub (hπ : IsSmooth π) (v : V) : IsOpen (stabSub h π v : Set (Fin (m + 1) → k)) := by
  exact (hπ v).preimage (continuous_colEl m N h)

theorem isOpen_charSub (hψ : Continuous ψ) {n : ℕ} (ξ : Fin n → k) : IsOpen (charSub k ψ ξ : Set (Fin n → k)) := by
  have hc : Continuous fun x : Fin n → k => ξ ⬝ᵥ x := continuous_const.dotProduct continuous_id
  exact (isOpen_ker_char ψ hψ).preimage hc

theorem isLat_comap {n : ℕ} (g : GL (Fin (n + 1)) k) {A : AddSubgroup (Fin (n + 1) → k)} (hA : IsLat A) :
    IsLat (A.comap (Matrix.mulVecLin (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k)).toAddMonoidHom) := by
  exact comap_lat (n + 1) _ (Units.isUnit g) A hA.1 hA.2

theorem avg_eq {ξ : Fin (m + 1) → k} {A : AddSubgroup (Fin (m + 1) → k)} {v : V}
    {p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)} (hp : AvgData ψ h π ξ A v p) :
    avg ψ h π ξ A v = ((p.2.card : ℂ)⁻¹) •
      ∑ t ∈ p.2, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v := by
  have hd : ∃ p, AvgData ψ h π ξ A v p := ⟨p, hp⟩
  rw [avg, dif_pos hd]
  obtain ⟨hq1, hq2, hq3, hq4, hq5, hq6⟩ := hd.choose_spec
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hp
  have key := card_smul_sum_eq hq1 hp1 hq5 hq6 hp5 hp6
    (fun t => (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v)
    (fun a b hb => avgF_add h π ψ a b (hq3 b hb) (hq4 b hb)) (fun a b hb => avgF_add h π ψ a b (hp3 b hb) (hp4 b hb))
  have hcq : (hd.choose.2.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (transversal_nonempty hq6).card_pos.ne'
  have hcp : (p.2.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (transversal_nonempty hp6).card_pos.ne'
  exact inv_smul_eq_of_smul_eq_alt hcq hcp key

theorem exists_avgData_of (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v : V)
    (U : AddSubgroup (Fin (m + 1) → k)) (hU : IsOpen (U : Set (Fin (m + 1) → k))) (hUA : U ≤ A)
    (hUv : U ≤ stabSub h π v) (hUξ : U ≤ charSub k ψ ξ) : ∃ T, AvgData ψ h π ξ A v (U, T) := by
  obtain ⟨T, hT, hTr⟩ := exists_transversal A U hA.1 hU hUA
  exact ⟨T, hUA, hU, fun a ha => hUv ha, fun a ha => hUξ ha, hT, hTr⟩

theorem exists_avgData (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) (v : V) (U : AddSubgroup (Fin (m + 1) → k)) (hU : IsOpen (U : Set (Fin (m + 1) → k))) :
    ∃ p, AvgData ψ h π ξ A v p ∧ p.1 ≤ U := by
  obtain ⟨T, hT⟩ := exists_avgData_of h π ψ ξ hA v (U ⊓ A ⊓ stabSub h π v ⊓ charSub k ψ ξ)
    (by
      simp only [AddSubgroup.coe_inf]
      exact ((hU.inter hA.2).inter (isOpen_stabSub h π hπ v)).inter (isOpen_charSub ψ hψ ξ))
    (inf_le_left.trans (inf_le_left.trans inf_le_right)) (inf_le_left.trans inf_le_right) inf_le_right
  exact ⟨_, hT, inf_le_left.trans (inf_le_left.trans inf_le_left)⟩

theorem avgData_of_fix {ξ : Fin (m + 1) → k} {A : AddSubgroup (Fin (m + 1) → k)} {v w : V}
    {p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)} (hp : AvgData ψ h π ξ A v p)
    (hw : ∀ a ∈ p.1, π (colEl k m N h a) w = w) : AvgData ψ h π ξ A w p :=
  ⟨hp.1, hp.2.1, hw, hp.2.2.2⟩

theorem exists_avgData₂ (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k)
    {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v w : V) :
    ∃ p, AvgData ψ h π ξ A v p ∧ AvgData ψ h π ξ A w p := by
  obtain ⟨p, hp, hpU⟩ := exists_avgData h π ψ hψ hπ ξ hA v (stabSub h π w) (isOpen_stabSub h π hπ w)
  exact ⟨p, hp, avgData_of_fix h π ψ hp (fun a ha => hpU ha)⟩

theorem avg_add (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) (v w : V) : avg ψ h π ξ A (v + w) = avg ψ h π ξ A v + avg ψ h π ξ A w := by
  obtain ⟨p, hp, hpw⟩ := exists_avgData₂ h π ψ hψ hπ ξ hA v w
  have hpvw : AvgData ψ h π ξ A (v + w) p :=
    avgData_of_fix h π ψ hp (fun a ha => by rw [map_add, hp.2.2.1 a ha, hpw.2.2.1 a ha])
  rw [avg_eq h π ψ hpvw, avg_eq h π ψ hp, avg_eq h π ψ hpw, ← smul_add, ← Finset.sum_add_distrib]
  simp only [map_add, smul_add]

theorem avg_smul (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) (c : ℂ) (v : V) : avg ψ h π ξ A (c • v) = c • avg ψ h π ξ A v := by
  obtain ⟨p, hp, -⟩ := exists_avgData h π ψ hψ hπ ξ hA v (stabSub h π v) (isOpen_stabSub h π hπ v)
  have hpc : AvgData ψ h π ξ A (c • v) p :=
    avgData_of_fix h π ψ hp (fun a ha => by rw [map_smul, hp.2.2.1 a ha])
  rw [avg_eq h π ψ hpc, avg_eq h π ψ hp, smul_comm c]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, smul_comm]

theorem colEl_comm_avg' (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k)
    {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (a : Fin (m + 1) → k) (v : V) :
    π (colEl k m N h a) (avg ψ h π ξ A v) = avg ψ h π ξ A (π (colEl k m N h a) v) := by
  obtain ⟨p, hp, hpw⟩ := exists_avgData₂ h π ψ hψ hπ ξ hA v (π (colEl k m N h a) v)
  rw [avg_eq h π ψ hp, avg_eq h π ψ hpw, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have e : π (colEl k m N h a) (π (colEl k m N h t) v) = π (colEl k m N h t) (π (colEl k m N h a) v) := by
    rw [← Module.End.mul_apply, ← map_mul, ← colEl_add, add_comm, colEl_add, map_mul, Module.End.mul_apply]
  rw [map_smul, e]

theorem avg_colEl (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) {a : Fin (m + 1) → k} (ha : a ∈ A) (v : V) :
    avg ψ h π ξ A (π (colEl k m N h a) v) = ((ψ (ξ ⬝ᵥ a) : Circle) : ℂ) • avg ψ h π ξ A v := by
  obtain ⟨p, hp, hpw⟩ := exists_avgData₂ h π ψ hψ hπ ξ hA v (π (colEl k m N h a) v)
  have hs := sum_transversal_add hp.1 hp.2.2.2.2.1 hp.2.2.2.2.2
    (fun t => (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v)
    (fun x y hy => avgF_add h π ψ x y (hp.2.2.1 y hy) (hp.2.2.2.1 y hy)) ha
  have e : ∀ t, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) (π (colEl k m N h a) v) =
      ((ψ (ξ ⬝ᵥ a) : Circle) : ℂ) •
        ((starRingEnd ℂ ((ψ (ξ ⬝ᵥ (t + a)) : Circle) : ℂ)) • π (colEl k m N h (t + a)) v) := by
    intro t
    rw [colEl_add, map_mul, Module.End.mul_apply, smul_smul]
    congr 1
    rw [conj_psi, conj_psi, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, dotProduct_add]
    congr 2
    ring
  rw [avg_eq h π ψ hpw, avg_eq h π ψ hp, Finset.sum_congr rfl (fun t _ => e t), ← Finset.smul_sum, hs, smul_comm]

theorem colEl_avg (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) {a : Fin (m + 1) → k} (ha : a ∈ A) (v : V) :
    π (colEl k m N h a) (avg ψ h π ξ A v) = ((ψ (ξ ⬝ᵥ a) : Circle) : ℂ) • avg ψ h π ξ A v := by
  rw [colEl_comm_avg' h π ψ hψ hπ ξ hA a v, avg_colEl h π ψ hψ hπ ξ hA ha v]

open Classical in
theorem char_sum {ξ η : Fin (m + 1) → k} {A : AddSubgroup (Fin (m + 1) → k)} {v : V}
    {p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)} (hp : AvgData ψ h π ξ A v p)
    (hη : ∀ a ∈ p.1, ψ (η ⬝ᵥ a) = 1) :
    ((p.2.card : ℂ)⁻¹) * ∑ t ∈ p.2, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) * ((ψ (η ⬝ᵥ t) : Circle) : ℂ) =
      if ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = ψ (η ⬝ᵥ a) then 1 else 0 := by
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hp
  have e : ∀ t, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) * ((ψ (η ⬝ᵥ t) : Circle) : ℂ) =
      ((ψ ((η - ξ) ⬝ᵥ t) : Circle) : ℂ) := by
    intro t
    rw [conj_psi, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, sub_dotProduct]
    congr 2
    ring
  simp only [e]
  have hc : (p.2.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (transversal_nonempty hp6).card_pos.ne'
  split_ifs with hA
  · have h1 : ∀ t ∈ p.2, ((ψ ((η - ξ) ⬝ᵥ t) : Circle) : ℂ) = 1 := by
      intro t ht
      rw [sub_dotProduct, AddChar.map_sub_eq_div, hA t (hp5 t ht), div_self', Circle.coe_one]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hc]
  · push Not at hA
    obtain ⟨a, ha, hne⟩ := hA
    have hz : ∑ t ∈ p.2, ((ψ ((η - ξ) ⬝ᵥ t) : Circle) : ℂ) = 0 := by
      refine sum_transversal_char hp1 hp5 hp6 (fun t => ((ψ ((η - ξ) ⬝ᵥ t) : Circle) : ℂ)) ?_ ?_ ha ?_
      · intro x y
        rw [dotProduct_add, AddChar.map_add_eq_mul, Circle.coe_mul]
      · intro x hx
        rw [sub_dotProduct, AddChar.map_sub_eq_div, hη x hx, hp4 x hx, div_one, Circle.coe_one]
      · intro H
        apply hne
        have H2 : ψ ((η - ξ) ⬝ᵥ a) = 1 := by
          rw [← Circle.coe_inj, Circle.coe_one]
          exact H
        rw [sub_dotProduct, AddChar.map_sub_eq_div] at H2
        exact (div_eq_one.mp H2).symm
    rw [hz, mul_zero]

open Classical in

theorem avg_eigen (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ η : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) (v : V) (hv : ∀ a ∈ A, π (colEl k m N h a) v = ((ψ (η ⬝ᵥ a) : Circle) : ℂ) • v) :
    avg ψ h π ξ A v = if ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = ψ (η ⬝ᵥ a) then v else 0 := by
  obtain ⟨p, hp, hpU⟩ := exists_avgData h π ψ hψ hπ ξ hA v (charSub k ψ η) (isOpen_charSub ψ hψ η)
  have hs := char_sum h π ψ hp (fun a ha => hpU ha)
  rw [avg_eq h π ψ hp]
  have e : ∀ t ∈ p.2, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v =
      ((starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) * ((ψ (η ⬝ᵥ t) : Circle) : ℂ)) • v := by
    intro t ht
    rw [hv t (hp.2.2.2.2.1 t ht), smul_smul]
  rw [Finset.sum_congr rfl e, ← Finset.sum_smul, smul_smul, hs]
  split_ifs <;> simp

theorem avg_zero' (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) : avg ψ h π ξ A 0 = 0 := by
  have := avg_smul h π ψ hψ hπ ξ hA 0 0
  simpa using this

theorem avg_sum' (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) {ι : Type} (s : Finset ι) (f : ι → V) :
    avg ψ h π ξ A (∑ i ∈ s, f i) = ∑ i ∈ s, avg ψ h π ξ A (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, avg_zero' h π ψ hψ hπ ξ hA]
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, avg_add h π ψ hψ hπ ξ hA, ih]

open Classical in

theorem avg_avg (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ η : Fin (m + 1) → k) {A A' : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) (hA' : IsLat A') (hAA' : A ≤ A') (v : V) :
    avg ψ h π η A' (avg ψ h π ξ A v) = if ∀ a ∈ A, ψ (η ⬝ᵥ a) = ψ (ξ ⬝ᵥ a) then avg ψ h π η A' v else 0 := by
  obtain ⟨p, hp, hpU⟩ := exists_avgData h π ψ hψ hπ ξ hA v (charSub k ψ η) (isOpen_charSub ψ hψ η)
  have hs := char_sum h π ψ hp (fun a ha => hpU ha)
  rw [avg_eq h π ψ hp, avg_smul h π ψ hψ hπ η hA', avg_sum' h π ψ hψ hπ η hA']
  have e : ∀ t ∈ p.2, avg ψ h π η A' ((starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v) =
      ((starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) * ((ψ (η ⬝ᵥ t) : Circle) : ℂ)) • avg ψ h π η A' v := by
    intro t ht
    rw [avg_smul h π ψ hψ hπ η hA', avg_colEl h π ψ hψ hπ η hA' (hAA' (hp.2.2.2.2.1 t ht)), smul_smul]
  rw [Finset.sum_congr rfl e, ← Finset.sum_smul, smul_smul, hs]
  by_cases hc : ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = ψ (η ⬝ᵥ a)
  · rw [if_pos hc, if_pos (fun a ha => (hc a ha).symm), one_smul]
  · rw [if_neg hc, if_neg (fun H => hc (fun a ha => (H a ha).symm)), zero_smul]

theorem form_avg (hψ : Continuous ψ) (hπ : IsSmooth π) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hB : ∀ x v w, B (π (colEl k m N h x) v) (π (colEl k m N h x) w) = B v w) (ξ : Fin (m + 1) → k)
    {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v w : V) :
    B (avg ψ h π ξ A v) w = B v (avg ψ h π ξ A w) := by
  classical
  obtain ⟨p, hp, hpw⟩ := exists_avgData₂ h π ψ hψ hπ ξ hA v w
  rw [avg_eq h π ψ hp, avg_eq h π ψ hpw]
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hp
  obtain ⟨hT', hTr'⟩ := transversal_neg hp5 hp6
  have hF : ∀ a, ∀ b ∈ p.1, ((ψ (ξ ⬝ᵥ (a + b)) : Circle) : ℂ) * B v (π (colEl k m N h (a + b)) w) =
      ((ψ (ξ ⬝ᵥ a) : Circle) : ℂ) * B v (π (colEl k m N h a) w) := by
    intro a b hb
    rw [dotProduct_add, AddChar.map_add_eq_mul, hp4 b hb, mul_one, colEl_add, map_mul, Module.End.mul_apply,
      hpw.2.2.1 b hb]
  have key := card_smul_sum_eq hp1 hp1 hp5 hp6 hT' hTr'
    (fun s => ((ψ (ξ ⬝ᵥ s) : Circle) : ℂ) * B v (π (colEl k m N h s) w)) hF hF
  rw [Finset.card_image_of_injective _ neg_injective, Finset.sum_image (fun x _ y _ hxy => neg_injective hxy)] at key
  have hc : (p.2.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (transversal_nonempty hp6).card_pos.ne'
  have key' := smul_right_injective ℂ hc key
  simp only [map_smul, map_smulₛₗ, map_sum, LinearMap.smul_apply, LinearMap.sum_apply,
    smul_eq_mul, map_inv₀, map_natCast, starRingEnd_self_apply]
  congr 1
  refine (Finset.sum_congr rfl fun t _ => ?_).trans key'.symm
  show _ = ((ψ (ξ ⬝ᵥ (-t)) : Circle) : ℂ) * B v (π (colEl k m N h (-t)) w)
  have hv : π (colEl k m N h (-t)) (π (colEl k m N h t) v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, ← colEl_add, neg_add_cancel, colEl_zero, map_one, Module.End.one_apply]
  rw [conj_psi, dotProduct_neg, ← hB (-t) (π (colEl k m N h t) v) w, hv]

theorem avg_conj (hψ : Continuous ψ) (hπ : IsSmooth π) (g : GL (Fin (m + 1)) k) (ξ : Fin (m + 1) → k)
    {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (u : V) :
    avg ψ h π ξ (A.comap (Matrix.mulVecLin ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom)
        (π (blkAt k (m + 1) N (by omega) g) u) =
      π (blkAt k (m + 1) N (by omega) g) (avg ψ h π (Matrix.vecMul ξ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) A u) := by
  classical
  obtain ⟨p, hp, -⟩ := exists_avgData h π ψ hψ hπ (Matrix.vecMul ξ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) hA u
    (stabSub h π u) (isOpen_stabSub h π hπ u)
  have hp0 := hp
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hp0
  have hgg : ∀ x : Fin (m + 1) → k, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ
      (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hgg' : ∀ x : Fin (m + 1) → k, ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ
      ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hinj : Function.Injective (fun x : Fin (m + 1) → k => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) := by
    intro x y hxy
    have := congrArg (fun z => ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ z) hxy
    simpa only [hgg'] using this
  have hcomm : ∀ (y : Fin (m + 1) → k) (w : V),
      π (colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ y)) (π (blkAt k (m + 1) N (by omega) g) w) =
        π (blkAt k (m + 1) N (by omega) g) (π (colEl k m N h y) w) := by
    intro y w
    rw [← Module.End.mul_apply, ← map_mul, ← blkAt_mul_colEl, map_mul, Module.End.mul_apply]
  have hq : AvgData ψ h π ξ
      (A.comap (Matrix.mulVecLin ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom)
      (π (blkAt k (m + 1) N (by omega) g) u)
      (p.1.comap (Matrix.mulVecLin ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toAddMonoidHom,
        p.2.image (fun x => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact hp1 hx
    · rw [AddSubgroup.coe_comap]
      exact hp2.preimage (Continuous.matrix_mulVec continuous_const continuous_id)
    · intro x hx
      have := hcomm (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) u
      rw [hgg] at this
      rw [this, hp3 (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) hx]
    · intro x hx
      have := hp4 (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) hx
      rwa [← Matrix.dotProduct_mulVec, hgg] at this
    · intro t ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      change ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ
        ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ s) ∈ A
      rw [hgg']
      exact hp5 s hs
    · intro a ha
      obtain ⟨s, ⟨hs, hs'⟩, hu⟩ := hp6 _ ha
      refine ⟨(g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ s, ⟨Finset.mem_image_of_mem _ hs, ?_⟩, ?_⟩
      · change ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ
          (a - (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ s) ∈ p.1
        rw [Matrix.mulVec_sub, hgg']
        exact hs'
      · rintro t ⟨ht, ht'⟩
        obtain ⟨s', hs'', rfl⟩ := Finset.mem_image.mp ht
        change ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ
          (a - (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ s') ∈ p.1 at ht'
        rw [Matrix.mulVec_sub, hgg'] at ht'
        rw [hu s' ⟨hs'', ht'⟩]
  rw [avg_eq h π ψ hq, avg_eq h π ψ hp, Finset.card_image_of_injective _ hinj,
    Finset.sum_image (fun x _ y _ hxy => hinj hxy), map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, hcomm, Matrix.dotProduct_mulVec]

theorem continuous_one_char : Continuous (⇑(1 : AddChar k Circle)) := by
  have : ⇑(1 : AddChar k Circle) = fun _ => 1 := funext fun x => AddChar.one_apply x
  rw [this]
  exact continuous_const

theorem avg_zero_char (ξ0 : Fin (m + 1) → k) (hξ0 : ξ0 = 0) (A : AddSubgroup (Fin (m + 1) → k)) (v : V) :
    avg ψ h π ξ0 A v = avg (1 : AddChar k Circle) h π 0 A v := by
  subst hξ0
  have hiff : ∀ p, AvgData ψ h π 0 A v p ↔ AvgData 1 h π 0 A v p := by
    intro p
    constructor
    · rintro ⟨a, b, c, -, e, f⟩
      exact ⟨a, b, c, fun x _ => by simp, e, f⟩
    · rintro ⟨a, b, c, -, e, f⟩
      exact ⟨a, b, c, fun x _ => by simp, e, f⟩
  by_cases hd : ∃ p, AvgData ψ h π 0 A v p
  · obtain ⟨p, hp⟩ := hd
    rw [avg_eq h π ψ hp, avg_eq h π 1 ((hiff p).mp hp)]
    simp only [zero_dotProduct, AddChar.map_zero_eq_one]
  · have hd' : ¬ ∃ p, AvgData 1 h π 0 A v p := fun ⟨p, hp⟩ => hd ⟨p, (hiff p).mpr hp⟩
    rw [avg, avg, dif_neg hd, dif_neg hd']

theorem avg_congr_char (hψ : Continuous ψ) (hπ : IsSmooth π) {ξ ξ' : Fin (m + 1) → k} {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) (hξ : ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = ψ (ξ' ⬝ᵥ a)) (v : V) :
    avg ψ h π ξ A v = avg ψ h π ξ' A v := by
  obtain ⟨p, hp, hpU⟩ := exists_avgData h π ψ hψ hπ ξ hA v (charSub k ψ ξ') (isOpen_charSub ψ hψ ξ')
  have hp' : AvgData ψ h π ξ' A v p := ⟨hp.1, hp.2.1, hp.2.2.1, fun a ha => hpU ha, hp.2.2.2.2⟩
  rw [avg_eq h π ψ hp, avg_eq h π ψ hp']
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hξ t (hp.2.2.2.2.1 t ht)]

theorem colEl_comm_avg (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : IsLat A) (a : Fin (m + 1) → k) (v : V) :
    π (colEl k m N h a) (avg ψ h π ξ A v) = avg ψ h π ξ A (π (colEl k m N h a) v) :=
  colEl_comm_avg' h π ψ hψ hπ ξ hA a v

end Api

end PositivityTheory.RgUd.Form.U.Atom
