import Mathlib
import GroundTheory.FunctionField.PlaceBridge

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField KaehlerDifferential IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable (k) in

def spanDField (x : K) : IntermediateField k K where
  carrier := {y | D k K y ∈ Submodule.span K {D k K x}}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Derivation.leibniz] at *
    exact add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ ha)
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact add_mem ha hb
  algebraMap_mem' c := by
    simp only [Set.mem_ofPred_eq, Derivation.map_algebraMap]
    exact zero_mem _
  inv_mem' a ha := by
    simp only [Set.mem_ofPred_eq, Derivation.leibniz_inv] at *
    exact Submodule.smul_mem _ _ ha

theorem D_mem_span_of_mem_adjoin (x : K) {y : K} (hy : y ∈ k⟮x⟯) :
    D k K y ∈ Submodule.span K {D k K x} := by
  have : k⟮x⟯ ≤ spanDField k x := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]
    exact Submodule.subset_span rfl
  exact this hy

theorem span_D_eq_top (x : K) [Algebra.IsSeparable k⟮x⟯ K] :
    Submodule.span K {D k K x} = ⊤ := by
  have : Algebra.FormallyUnramified k⟮x⟯ K := .of_isSeparable _ _
  refine eq_top_iff.mpr fun ω hω ↦ ?_
  clear hω
  obtain ⟨z, rfl⟩ := (exact_mapBaseChange_map k k⟮x⟯ K ω).mp (Subsingleton.elim _ _)
  induction z with
  | zero => simp
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul a b =>
    rw [mapBaseChange_tmul]
    refine Submodule.smul_mem _ _ ?_
    have hb : b ∈ Submodule.span k⟮x⟯ (Set.range (D k k⟮x⟯)) := by
      rw [span_range_derivation]; trivial
    induction hb using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨e, rfl⟩ := h
      rw [map_D]
      exact D_mem_span_of_mem_adjoin x e.2
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | smul c _ _ h =>
      rw [map_smul, algebra_compatible_smul K c]
      exact Submodule.smul_mem _ _ h

variable [IsFunctionField k K]

theorem kaehlerDifferential_nontrivial : Nontrivial Ω[K⁄k] := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : Algebra.FormallyUnramified k K := ⟨h⟩
  have : Algebra.EssFiniteType k K := essFiniteType
  have : Module.Finite k K := Algebra.FormallyUnramified.finite_of_free k K
  have h1 := trdeg_eq_one (k := k) (K := K)
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  rw [_root_.trdeg_eq_zero] at h1
  exact zero_ne_one h1

theorem D_ne_zero_of_isSeparable (x : K) [Algebra.IsSeparable k⟮x⟯ K] : D k K x ≠ 0 := by
  intro h
  have htop := span_D_eq_top (k := k) x
  rw [h, Submodule.span_singleton_eq_bot.mpr rfl] at htop
  have := kaehlerDifferential_nontrivial (k := k) (K := K)
  exact bot_ne_top htop

section Perfect

variable [PerfectField k]

variable (k K) in

theorem exists_isSeparable_adjoin : ∃ x : K, Algebra.IsSeparable k⟮x⟯ K := by
  have : Algebra.EssFiniteType k K := essFiniteType
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have hcard : s.card = 1 := by
    have h := hs.cardinalMk_eq_trdeg
    rw [trdeg_eq_one, Cardinal.mk_coe_finset] at h
    exact_mod_cast h
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
  refine ⟨x, ?_⟩
  convert hsep <;> simp

variable (k K) in

theorem finrank_kaehlerDifferential : Module.finrank K Ω[K⁄k] = 1 := by
  obtain ⟨x, hx⟩ := exists_isSeparable_adjoin k K
  rw [← finrank_top, ← span_D_eq_top (k := k) x, finrank_span_singleton (D_ne_zero_of_isSeparable x)]

theorem span_D_eq_top_of_ne_zero {z : K} (hz : D k K z ≠ 0) :
    Submodule.span K {D k K z} = ⊤ :=
  have : FiniteDimensional K Ω[K⁄k] :=
    Module.finite_of_finrank_pos (by rw [finrank_kaehlerDifferential]; norm_num)
  Submodule.eq_top_of_finrank_eq (by
    rw [finrank_span_singleton hz, finrank_kaehlerDifferential])

theorem isSeparable_of_D_ne_zero {z : K} (hz : D k K z ≠ 0) : Algebra.IsSeparable k⟮z⟯ K := by
  have hsub : Subsingleton Ω[K⁄k⟮z⟯] := by
    refine subsingleton_of_forall_eq 0 fun ω' ↦ ?_
    obtain ⟨ω, rfl⟩ := map_surjective k k⟮z⟯ K ω'
    have hω : ω ∈ Submodule.span K {D k K z} := by rw [span_D_eq_top_of_ne_zero hz]; trivial
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hω
    have h0 : D k⟮z⟯ K z = 0 := (D k⟮z⟯ K).map_algebraMap ⟨z, mem_adjoin_simple_self k z⟩
    simp only [map_smul, map_D, Algebra.algebraMap_self, RingHom.id_apply]
    rw [h0, smul_zero]
  have : Algebra.FormallyUnramified k⟮z⟯ K := ⟨hsub⟩
  have : Algebra.EssFiniteType k K := essFiniteType
  have : Algebra.EssFiniteType k⟮z⟯ K := .of_comp k k⟮z⟯ K
  exact Algebra.FormallyUnramified.isSeparable k⟮z⟯ K

theorem exists_ord_eq_one_D_ne_zero (v : Place k K) :
    ∃ t : K, v.ord t = 1 ∧ D k K t ≠ 0 := by
  obtain ⟨π, hπ⟩ := v.exists_ord_eq_one
  have hπ0 : π ≠ 0 := fun h ↦ by simp [h, v.ord_zero] at hπ
  by_cases hd : D k K π = 0
  swap
  · exact ⟨π, hπ, hd⟩
  obtain ⟨x, hx⟩ := exists_isSeparable_adjoin k K
  have hdx := D_ne_zero_of_isSeparable (k := k) x
  have hx0 : x ≠ 0 := fun h ↦ hdx (by simp [h])
  set m : ℕ := (2 - v.ord x).toNat + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hord : v.ord (π ^ m * x) = m + v.ord x := by
    rw [v.ord_mul (pow_ne_zero _ hπ0) hx0, v.ord_pow, hπ, mul_one]
  have hlt : v.valuation (π ^ m * x) < v.valuation π := by
    rw [v.valuation_eq_exp_neg_ord (mul_ne_zero (pow_ne_zero _ hπ0) hx0),
      v.valuation_eq_exp_neg_ord hπ0, hord, hπ, WithZero.exp_lt_exp]
    omega
  refine ⟨π + π ^ m * x, ?_, ?_⟩
  · have hne : π + π ^ m * x ≠ 0 := by
      intro h
      have := Valuation.map_add_eq_of_lt_left v.valuation hlt
      rw [h, map_zero] at this
      exact (v.valuation.ne_zero_iff.mpr hπ0) this.symm
    have h := Valuation.map_add_eq_of_lt_left v.valuation hlt
    rw [v.valuation_eq_exp_neg_ord hne, v.valuation_eq_exp_neg_ord hπ0, hπ] at h
    have := WithZero.exp_injective h
    omega
  · rw [map_add, hd, zero_add, Derivation.leibniz, Derivation.leibniz_pow, hd]
    simp only [smul_zero, add_zero]
    exact smul_ne_zero (pow_ne_zero _ hπ0) hdx

end Perfect

section Order

variable [PerfectField k]

noncomputable def kaehlerCoeff (t : K) (ω : Ω[K⁄k]) : K :=
  haveI := Classical.propDecidable
  if h : ∃ c : K, c • D k K t = ω then h.choose else 0

theorem kaehlerCoeff_smul_D {t : K} (ht : D k K t ≠ 0) (ω : Ω[K⁄k]) :
    kaehlerCoeff t ω • D k K t = ω := by
  have hω : ω ∈ Submodule.span K {D k K t} := by rw [span_D_eq_top_of_ne_zero ht]; trivial
  have h := Submodule.mem_span_singleton.mp hω
  classical
  rw [kaehlerCoeff, dif_pos h]
  exact h.choose_spec

theorem kaehlerCoeff_eq {t : K} (ht : D k K t ≠ 0) {ω : Ω[K⁄k]} {c : K} (h : c • D k K t = ω) :
    kaehlerCoeff t ω = c :=
  smul_left_injective K ht ((kaehlerCoeff_smul_D ht ω).trans h.symm)

theorem kaehlerCoeff_smul {t : K} (ht : D k K t ≠ 0) (f : K) (ω : Ω[K⁄k]) :
    kaehlerCoeff t (f • ω) = f * kaehlerCoeff t ω :=
  kaehlerCoeff_eq ht (by rw [mul_smul, kaehlerCoeff_smul_D ht])

theorem kaehlerCoeff_add {t : K} (ht : D k K t ≠ 0) (ω₁ ω₂ : Ω[K⁄k]) :
    kaehlerCoeff t (ω₁ + ω₂) = kaehlerCoeff t ω₁ + kaehlerCoeff t ω₂ :=
  kaehlerCoeff_eq ht (by rw [add_smul, kaehlerCoeff_smul_D ht, kaehlerCoeff_smul_D ht])

theorem kaehlerCoeff_ne_zero {t : K} (ht : D k K t ≠ 0) {ω : Ω[K⁄k]} (hω : ω ≠ 0) :
    kaehlerCoeff t ω ≠ 0 := by
  intro h
  have := kaehlerCoeff_smul_D ht ω
  rw [h, zero_smul] at this
  exact hω this.symm

theorem kaehlerCoeff_D_self {t : K} (ht : D k K t ≠ 0) : kaehlerCoeff t (D k K t) = 1 :=
  kaehlerCoeff_eq ht (one_smul _ _)

theorem kaehlerCoeff_trans {t t' : K} (ht : D k K t ≠ 0) (ht' : D k K t' ≠ 0) (ω : Ω[K⁄k]) :
    kaehlerCoeff t ω = kaehlerCoeff t' ω * kaehlerCoeff t (D k K t') := by
  refine kaehlerCoeff_eq ht ?_
  rw [mul_smul, kaehlerCoeff_smul_D ht, kaehlerCoeff_smul_D ht']

noncomputable def kaehlerUniformizer (v : Place k K) : K :=
  (exists_ord_eq_one_D_ne_zero v).choose

theorem ord_kaehlerUniformizer (v : Place k K) : v.ord (kaehlerUniformizer v) = 1 :=
  (exists_ord_eq_one_D_ne_zero v).choose_spec.1

theorem D_kaehlerUniformizer_ne_zero (v : Place k K) : D k K (kaehlerUniformizer v) ≠ 0 :=
  (exists_ord_eq_one_D_ne_zero v).choose_spec.2

noncomputable def kaehlerOrd (v : Place k K) (ω : Ω[K⁄k]) : ℤ :=
  v.ord (kaehlerCoeff (kaehlerUniformizer v) ω)

theorem kaehlerOrd_smul (v : Place k K) {f : K} (hf : f ≠ 0) {ω : Ω[K⁄k]} (hω : ω ≠ 0) :
    kaehlerOrd v (f • ω) = v.ord f + kaehlerOrd v ω := by
  rw [kaehlerOrd, kaehlerCoeff_smul (D_kaehlerUniformizer_ne_zero v),
    v.ord_mul hf (kaehlerCoeff_ne_zero (D_kaehlerUniformizer_ne_zero v) hω), kaehlerOrd]

end Order

end GroundTheory.Arith.SchemeCoh
