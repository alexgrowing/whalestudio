import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HermOrthBasis

open Matrix

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_add_left (a b y : Fin n → E) : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_sub_left (a b y : Fin n → E) : hf L Hm (a - b) y = hf L Hm a y - hf L Hm b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

theorem hf_smul_left (c : E) (a y : Fin n → E) : hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_add_right (a y z : Fin n → E) : hf L Hm a (y + z) = hf L Hm a y + hf L Hm a z := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_right (c : E) (a y : Fin n → E) :
    hf L Hm a (c • y) = L.cj c * hf L Hm a y := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_sum_left {m : ℕ} (c : Fin m → E) (x : Fin m → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ b, c b • x b) y = ∑ b, c b * hf L Hm (x b) y := by
  induction' (Finset.univ : Finset (Fin m)) using Finset.induction_on with a s ha ih
  · simp [hf]
  · rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_left, hf_smul_left, ih]

theorem cj_hf (hH : IsHerm L Hm) (a b : Fin n → E) : L.cj (hf L Hm a b) = hf L Hm b a := by
  simp only [hf, map_sum, map_mul, L.cj_cj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : L.cj (Hm j i) = Hm i j := congrFun (congrFun hH i) j
  rw [this]; ring

theorem mem_perp_span {m : ℕ} (x : Fin m → Fin n → E) (v : Fin n → E) :
    v ∈ perp L Hm (Submodule.span E (Set.range x)) ↔ ∀ a, hf L Hm v (x a) = 0 := by
  refine ⟨fun h a => h _ (Submodule.subset_span ⟨a, rfl⟩), fun h y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact h a
  | zero => simp [hf]
  | add y z _ _ hy hz => rw [hf_add_right, hy, hz, add_zero]
  | smul c y _ hy => rw [hf_smul_right, hy, mul_zero]

theorem gram_mulVec {m : ℕ} (x : Fin m → Fin n → E) (c : Fin m → E) (a : Fin m) :
    (gramT L Hm x *ᵥ c) a = hf L Hm (∑ b, c b • x b) (x a) := by
  rw [hf_sum_left]
  simp [gramT, mulVec, dotProduct, mul_comm]

theorem coeff_eq_zero {m : ℕ} (x : Fin m → Fin n → E) (hx : IsUnit (gramT L Hm x).det)
    (c : Fin m → E) (h : ∀ a, hf L Hm (∑ b, c b • x b) (x a) = 0) : c = 0 := by
  have h1 : gramT L Hm x *ᵥ c = 0 := funext fun a => (gram_mulVec L Hm x c a).trans (h a)
  have h2 := congrArg (fun v => (gramT L Hm x)⁻¹ *ᵥ v) h1
  simpa only [mulVec_mulVec, nonsing_inv_mul _ hx, one_mulVec, mulVec_zero] using h2

theorem isCompl_perp {m : ℕ} (x : Fin m → Fin n → E) (hx : IsUnit (gramT L Hm x).det) :
    IsCompl (Submodule.span E (Set.range x)) (perp L Hm (Submodule.span E (Set.range x))) := by
  refine ⟨Submodule.disjoint_def.2 fun v hv hv' => ?_, codisjoint_iff.2 (eq_top_iff.2 fun v _ => ?_)⟩
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
    rw [coeff_eq_zero L Hm x hx c ((mem_perp_span L Hm x _).1 hv')]
    simp
  · let c := (gramT L Hm x)⁻¹ *ᵥ fun a => hf L Hm v (x a)
    refine Submodule.mem_sup.2 ⟨∑ b, c b • x b,
      (Submodule.mem_span_range_iff_exists_fun E).2 ⟨c, rfl⟩, v - ∑ b, c b • x b,
      (mem_perp_span L Hm x _).2 fun a => ?_, by abel⟩
    rw [hf_sub_left, ← gram_mulVec, mulVec_mulVec, mul_nonsing_inv _ hx, one_mulVec, sub_self]

include L in
theorem nontrivial_alg : Nontrivial E :=
  Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)

theorem le_of_gram {m : ℕ} (x : Fin m → Fin n → E) (hx : IsUnit (gramT L Hm x).det) : m ≤ n := by
  haveI := nontrivial_alg L
  have hli : LinearIndependent E x := Fintype.linearIndependent_iff.2 fun c hc a =>
    congrFun (coeff_eq_zero L Hm x hx c fun a => by rw [hc]; simp [hf]) a
  simpa using hli.fintype_card_le_finrank

theorem le_of_perp_eq_bot {m : ℕ} (x : Fin m → Fin n → E) (hx : IsUnit (gramT L Hm x).det)
    (h : perp L Hm (Submodule.span E (Set.range x)) = ⊥) : n ≤ m := by
  haveI := nontrivial_alg L
  have h1 := (isCompl_perp L Hm x hx).sup_eq_top
  rw [h, sup_bot_eq] at h1
  simpa using finrank_le_of_span_eq_top h1

theorem exists_unit_norm [CharZero F] (hH : IsHermND L Hm) {m : ℕ} (x : Fin m → Fin n → E)
    (hx : IsUnit (gramT L Hm x).det) (h : perp L Hm (Submodule.span E (Set.range x)) ≠ ⊥) :
    ∃ w ∈ perp L Hm (Submodule.span E (Set.range x)), IsUnit (hf L Hm w w) := by
  by_contra hcon
  push Not at hcon
  haveI := L.reduced
  set W := perp L Hm (Submodule.span E (Set.range x)) with hW
  have h0 : ∀ w ∈ W, hf L Hm w w = 0 := fun w hw => by
    obtain ⟨a, ha⟩ := (L.cj_fix _).1 (cj_hf L Hm hH.1 w w)
    by_contra hne
    have ha0 : a ≠ 0 := fun h => hne (by rw [← ha, h, map_zero])
    exact hcon w hw (ha ▸ (IsUnit.mk0 a ha0).map (algebraMap F E))
  have h1 : ∀ u ∈ W, ∀ v ∈ W, hf L Hm u v + hf L Hm v u = 0 := fun u hu v hv => by
    have := h0 _ (W.add_mem hu hv)
    rw [hf_add_left, hf_add_right, hf_add_right, h0 u hu, h0 v hv] at this
    linear_combination this
  have h2u : IsUnit (2 : E) := by
    have := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F E)
    rwa [map_ofNat] at this
  have h2 : ∀ u ∈ W, ∀ v ∈ W, hf L Hm u v = 0 := fun u hu v hv => by
    have a1 := h1 u hu v hv
    have a2 := h1 _ (W.smul_mem (hf L Hm u v) hu) v hv
    rw [hf_smul_left, hf_smul_right, cj_hf L Hm hH.1] at a2
    have a3 : 2 * hf L Hm u v ^ 2 = 0 := by
      linear_combination a2 + (hf L Hm u v - hf L Hm v u) * a1
    exact IsNilpotent.eq_zero ⟨2, h2u.mul_right_eq_zero.1 a3⟩
  apply h
  rw [eq_bot_iff]
  intro v hv
  have h3 : ∀ y, hf L Hm v y = 0 := fun y => by
    have hy : y ∈ Submodule.span E (Set.range x) ⊔ W := by
      rw [(isCompl_perp L Hm x hx).sup_eq_top]; trivial
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    rw [hf_add_right, hv s hs, h2 v hv t ht, add_zero]
  have h4 : v ᵥ* Hm = 0 := funext fun j => by
    have := h3 (Pi.single j 1)
    simpa [hf, vecMul, dotProduct, Pi.single_apply, apply_ite] using this
  have h5 := congrArg (fun u => u ᵥ* Hm⁻¹) h4
  simpa only [vecMul_vecMul, mul_nonsing_inv _ hH.2, vecMul_one, zero_vecMul,
    Submodule.mem_bot] using h5

theorem gram_cons {m : ℕ} (x : Fin m → Fin n → E) (hx : IsUnit (gramT L Hm x).det)
    (w : Fin n → E) (hw : w ∈ perp L Hm (Submodule.span E (Set.range x)))
    (hu : IsUnit (hf L Hm w w)) :
    IsUnit (gramT L Hm (Fin.cons w x : Fin (m + 1) → Fin n → E)).det := by
  have h := (mem_perp_span L Hm x w).1 hw
  rw [det_succ_column_zero, Fin.sum_univ_succ, Finset.sum_eq_zero (fun i _ => by simp [gramT, h]),
    add_zero]
  have : (gramT L Hm (Fin.cons w x : Fin (m + 1) → Fin n → E)).submatrix
      (Fin.succAbove 0) Fin.succ = gramT L Hm x := by
    ext a b; simp [gramT]
  rw [this]
  simpa [gramT] using ⟨hu, hx⟩

theorem exists_orth [CharZero F] (hH : IsHermND L Hm) (k : ℕ) : ∀ (m : ℕ) (x : Fin m → Fin n → E),
    IsUnit (gramT L Hm x).det → m + k = n → ∃ w : Fin k → Fin n → E,
      Submodule.span E (Set.range w) = perp L Hm (Submodule.span E (Set.range x)) ∧
      (∀ i, IsUnit (hf L Hm (w i) (w i))) ∧ ∀ i j, i ≠ j → hf L Hm (w i) (w j) = 0 := by
  induction k with
  | zero =>
    intro m x hx hm
    refine ⟨Fin.elim0, ?_, fun i => i.elim0, fun i => i.elim0⟩
    rw [Set.range_eq_empty, Submodule.span_empty]
    by_contra h
    obtain ⟨w, hw, hu⟩ := exists_unit_norm L Hm hH x hx (Ne.symm h)
    have := le_of_gram L Hm _ (gram_cons L Hm x hx w hw hu)
    omega
  | succ k ih =>
    intro m x hx hm
    obtain ⟨w₀, hw, hu⟩ := exists_unit_norm L Hm hH x hx fun h => by
      have := le_of_perp_eq_bot L Hm x hx h
      omega
    obtain ⟨w, h1, h2, h3⟩ := ih (m + 1) _ (gram_cons L Hm x hx w₀ hw hu) (by omega)
    have hmem : ∀ v, v ∈ Submodule.span E (Set.range w) ↔
        hf L Hm v w₀ = 0 ∧ ∀ a, hf L Hm v (x a) = 0 := fun v => by
      rw [h1, mem_perp_span, Fin.forall_fin_succ]; simp
    have hw' := fun i => (hmem (w i)).1 (Submodule.subset_span ⟨i, rfl⟩)
    refine ⟨Fin.cons w₀ w, le_antisymm ?_ fun v hv => ?_, ?_, ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hw
      · exact (mem_perp_span L Hm x _).2 (hw' i).2
    · obtain ⟨d, hd⟩ := hu.exists_left_inv
      rw [Fin.range_cons, Submodule.mem_span_insert]
      refine ⟨hf L Hm v w₀ * d, v - (hf L Hm v w₀ * d) • w₀, (hmem _).2 ⟨?_, fun a => ?_⟩, by abel⟩
      · rw [hf_sub_left, hf_smul_left, mul_assoc, hd, mul_one, sub_self]
      · rw [hf_sub_left, hf_smul_left, (mem_perp_span L Hm x _).1 hv a,
          (mem_perp_span L Hm x _).1 hw a, mul_zero, sub_self]
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hu
      · exact h2 i
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · exact fun h => (h rfl).elim
      · intro _
        show hf L Hm w₀ (w j) = 0
        rw [← cj_hf L Hm hH.1, (hw' j).1, map_zero]
      · exact fun _ => (hw' i).1
      · exact fun h => h3 i j fun e => h (by rw [e])

theorem orth_basis_perp : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → m ≤ n ∧ IsCompl (Submodule.span E (Set.range x)) (perp L Hm (Submodule.span E (Set.range x))) ∧ ∃ w : Fin (n - m) → Fin n → E, Submodule.span E (Set.range w) = perp L Hm (Submodule.span E (Set.range x)) ∧ (∀ i, IsUnit (hf L Hm (w i) (w i))) ∧ ∀ i j, i ≠ j → hf L Hm (w i) (w j) = 0 := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH m x hx
  have h := le_of_gram L Hm x hx
  exact ⟨h, isCompl_perp L Hm x hx, exists_orth L Hm hH _ m x hx (by omega)⟩

end GlobalTheory.HermOrthBasis
