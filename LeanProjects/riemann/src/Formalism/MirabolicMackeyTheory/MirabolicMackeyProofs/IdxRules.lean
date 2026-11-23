import Mathlib
import Formalism.MirabolicMackeyTheory.StatementL
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ImageLcv
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange

open Module NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues Formalism.HermitianLatticesTheory

section Gen

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {V' : Type*} [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']

theorem idxRules_alg_ne {s : R} (hs : s ≠ 0) : algebraMap R K s ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs

theorem idxRules_denom (B : Submodule R V) {x : V} (hx : x ∈ Submodule.span K (B : Set V)) :
    x ∈ locS R⁰ B := by
  induction hx using Submodule.span_induction with
  | mem x h => exact locBasic_le_locS _ _ h
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul k x _ hx =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    refine ⟨b * d, mul_mem hb hd, ?_⟩
    have hb0 : algebraMap R K b ≠ 0 := idxRules_alg_ne (nonZeroDivisors.ne_zero hb)
    have e : (b * d) • ((algebraMap R K a / algebraMap R K b) • x) = a • (d • x) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K a, ← algebraMap_smul K d, smul_smul,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [e]
    exact B.smul_mem a hdx

theorem idxRules_fin (p : Ideal R) [p.IsPrime] (X Y : Submodule R V) (hX : X.FG)
    (h : X ≤ locS R⁰ Y) :
    Module.length R (↥(localization₂ p X) ⧸ (localization₂ p Y).comap (localization₂ p X).subtype) ≠ ⊤ := by
  obtain ⟨d, hd, hdY⟩ := indexBasic_denom R⁰ X Y hX h
  exact Module.length_ne_top_iff.mpr (indexBasic_finLen p X Y hX hd hdY)

theorem idxRules_le_locS {W : Submodule K V} {X Y : Submodule R V}
    (hX : Submodule.span K (X : Set V) = W) (hY : Submodule.span K (Y : Set V) = W) :
    X ≤ locS R⁰ Y := fun x hx =>
  idxRules_denom Y (by rw [hY, ← hX]; exact Submodule.subset_span hx)

theorem idxRules_add (p : Ideal R) [p.IsPrime] (W : Submodule K V) (A B C : Submodule R V)
    (hA : A.FG ∧ Submodule.span K (A : Set V) = W) (hB : B.FG ∧ Submodule.span K (B : Set V) = W)
    (hC : C.FG ∧ Submodule.span K (C : Set V) = W) :
    lidx p A C = lidx p A B + lidx p B C := by
  have hD : ∀ X : Submodule R V, Submodule.span K (X : Set V) = W → X ≤ locS R⁰ (A ⊓ B ⊓ C) := by
    intro X hX
    rw [locBasic_locS_inf, locBasic_locS_inf]
    exact le_inf (le_inf (idxRules_le_locS hX hA.2) (idxRules_le_locS hX hB.2))
      (idxRules_le_locS hX hC.2)
  have hAD := idxRules_fin p A _ hA.1 (hD A hA.2)
  have hBD := idxRules_fin p B _ hB.1 (hD B hB.2)
  have hCD := idxRules_fin p C _ hC.1 (hD C hC.2)
  rw [indexBasic_lidx_via p A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right
      hAD hCD,
    indexBasic_lidx_via p A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hAD hBD,
    indexBasic_lidx_via p B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right
      hBD hCD]
  ring

theorem idxRules_lidx_of_le (p : Ideal R) [p.IsPrime] {A B : Submodule R V} (h : B ≤ A) :
    lidx p A B = locLen p A B := by
  unfold lidx
  rw [inf_eq_right.mpr h, indexBasic_locLen_self]
  simp

theorem idxRules_lidx_self (p : Ideal R) [p.IsPrime] (A : Submodule R V) : lidx p A A = 0 := by
  unfold lidx
  exact sub_self _

theorem localization_map₄ (p : Ideal R) [p.IsPrime] (φ : V →ₗ[K] V') (A : Submodule R V) :
    localization₂ p (A.map (φ.restrictScalars R)) = (localization₂ p A).map (φ.restrictScalars R) := by
  ext x
  constructor
  · rintro ⟨s, hs, y, hy, hyx⟩
    have hs0 : algebraMap R K s ≠ 0 := idxRules_alg_ne (fun h => hs (h ▸ p.zero_mem))
    refine ⟨(algebraMap R K s)⁻¹ • y, ⟨s, hs, ?_⟩, ?_⟩
    · rw [← algebraMap_smul K s, smul_smul, mul_inv_cancel₀ hs0, one_smul]
      exact hy
    · have h1 : φ y = s • x := hyx
      change φ ((algebraMap R K s)⁻¹ • y) = x
      rw [map_smul, h1, ← algebraMap_smul K s, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    exact ⟨s, hs, s • y, hy, by simp⟩

theorem idxRules_len_map (f : V →ₗ[R] V') (hf : Function.Injective f) (X Y : Submodule R V) :
    Module.length R (↥(X.map f) ⧸ (Y.map f).comap (X.map f).subtype) =
      Module.length R (↥X ⧸ Y.comap X.subtype) := by
  symm
  apply LinearEquiv.length_eq
  refine Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf X) ?_
  apply le_antisymm
  · rintro _ ⟨⟨x, hx⟩, hxY, rfl⟩
    exact ⟨x, hxY, rfl⟩
  · rintro ⟨z, hz⟩ ⟨y, hy, hyz⟩
    obtain ⟨x, hx, hxz⟩ := hz
    have hxy : x = y := hf (hxz.trans hyz.symm)
    subst hxy
    refine ⟨⟨x, hx⟩, hy, ?_⟩
    apply Subtype.ext
    exact hxz

theorem idxRules_lidx_map (p : Ideal R) [p.IsPrime] (φ : V →ₗ[K] V') (hφ : Function.Injective φ)
    (A B : Submodule R V) :
    lidx p (A.map (φ.restrictScalars R)) (B.map (φ.restrictScalars R)) = lidx p A B := by
  have hφ' : Function.Injective (φ.restrictScalars R) := hφ
  have hinf : A.map (φ.restrictScalars R) ⊓ B.map (φ.restrictScalars R) =
      (A ⊓ B).map (φ.restrictScalars R) := (Submodule.map_inf _ hφ').symm
  unfold lidx locLen
  rw [hinf, localization_map₄, localization_map₄, localization_map₄, idxRules_len_map _ hφ',
    idxRules_len_map _ hφ']

theorem idxRules_span_map (φ : V →ₗ[K] V') (A : Submodule R V) :
    Submodule.span K ((A.map (φ.restrictScalars R) : Submodule R V') : Set V') =
      (Submodule.span K (A : Set V)).map φ := by
  rw [Submodule.map_span]
  rfl

def scG (a : K) (A : Submodule R V) : Submodule R V :=
  A.map ((a • (LinearMap.id : V →ₗ[K] V)).restrictScalars R)

theorem idxRules_scG_lat {a : K} (ha : a ≠ 0) {W : Submodule K V} {A : Submodule R V}
    (hA : A.FG ∧ Submodule.span K (A : Set V) = W) :
    (scG a A).FG ∧ Submodule.span K ((scG a A : Submodule R V) : Set V) = W := by
  refine ⟨hA.1.map _, ?_⟩
  unfold scG
  rw [idxRules_span_map, hA.2, Submodule.map_smul _ _ a ha, Submodule.map_id]

theorem idxRules_smul_inj {a : K} (ha : a ≠ 0) :
    Function.Injective (a • (LinearMap.id : V →ₗ[K] V)) := by
  intro x y h
  exact smul_right_injective V ha h

theorem idxRules_scG_map (a : K) (φ : V →ₗ[K] V') (A : Submodule R V) :
    scG a (A.map (φ.restrictScalars R)) = (scG a A).map (φ.restrictScalars R) := by
  unfold scG
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  simp

theorem idxRules_scale_std (v : HeightOneSpectrum R) (n : ℕ) {a : K} (ha : a ≠ 0) :
    lidx v.asIdeal (Submodule.span R (Set.range (Pi.basisFun K (Fin n))))
        (scG a (Submodule.span R (Set.range (Pi.basisFun K (Fin n))))) =
      (n : ℤ) * FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ a) := by
  have h := indexChange_diagonal v (fun _ : Fin n => a) (fun _ => ha) (Pi.basisFun K (Fin n))
    (Pi.basisFun K (Fin n)).linearIndependent
  rw [idxChange_act_diagonal, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow] at h
  rw [← h]
  congr 1
  unfold scG
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem idxRules_scale [FiniteDimensional K V] (v : HeightOneSpectrum R) (W : Submodule K V)
    (B : Submodule R V) (hB : B.FG ∧ Submodule.span K (B : Set V) = W) {a : K} (ha : a ≠ 0) :
    lidx v.asIdeal B (scG a B) =
      (finrank K W : ℤ) * FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ a) := by
  set n := finrank K W with hn
  let b : Basis (Fin n) K W := Module.finBasis K W
  let φ : (Fin n → K) →ₗ[K] V := W.subtype ∘ₗ (b.equivFun.symm : (Fin n → K) →ₗ[K] W)
  have hφ : Function.Injective φ := W.injective_subtype.comp b.equivFun.symm.injective
  set F0 : Submodule R (Fin n → K) := Submodule.span R (Set.range (Pi.basisFun K (Fin n))) with hF0
  set F : Submodule R V := F0.map (φ.restrictScalars R) with hF
  have hFl : F.FG ∧ Submodule.span K (F : Set V) = W := by
    refine ⟨(Submodule.fg_span (Set.finite_range _)).map _, ?_⟩
    rw [hF, idxRules_span_map, hF0, Submodule.span_span_of_tower, (Pi.basisFun K (Fin n)).span_eq,
      Submodule.map_top, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      Submodule.range_subtype]
  have h1 : lidx v.asIdeal F (scG a F) =
      (n : ℤ) * FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ a) := by
    rw [hF, idxRules_scG_map, idxRules_lidx_map _ φ hφ, idxRules_scale_std v n ha]
  have h2 : lidx v.asIdeal (scG a F) (scG a B) = lidx v.asIdeal F B :=
    idxRules_lidx_map _ _ (idxRules_smul_inj ha) F B
  have h3 := idxRules_add v.asIdeal W B F (scG a B) hB hFl (idxRules_scG_lat ha hB)
  have h4 := idxRules_add v.asIdeal W F (scG a F) (scG a B) hFl (idxRules_scG_lat ha hFl)
    (idxRules_scG_lat ha hB)
  have h5 := idxRules_add v.asIdeal W B F B hB hFl hB
  rw [idxRules_lidx_self] at h5
  rw [h3, h4, h1, h2]
  linarith

theorem idxRules_cut_lat {W W' : Submodule K V} (hW : W' ≤ W) {A : Submodule R V}
    (hA : A.FG ∧ Submodule.span K (A : Set V) = W) :
    (A ⊓ W'.restrictScalars R).FG ∧
      Submodule.span K ((A ⊓ W'.restrictScalars R : Submodule R V) : Set V) = W' := by
  refine ⟨hA.1.of_le inf_le_left, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := idxRules_denom A (x := x) (by rw [hA.2]; exact hW hx)
    have hd0 : algebraMap R K d ≠ 0 := idxRules_alg_ne (nonZeroDivisors.ne_zero hd)
    have hm : d • x ∈ (A ⊓ W'.restrictScalars R : Submodule R V) :=
      ⟨hdx, (W'.restrictScalars R).smul_mem d hx⟩
    have e : x = (algebraMap R K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem idxRules_cut_le (p : Ideal R) [p.IsPrime] (W' : Submodule K V) (A B : Submodule R V)
    (hfin : Module.length R (↥(localization₂ p A) ⧸ (localization₂ p B).comap (localization₂ p A).subtype) ≠ ⊤) :
    locLen p (A ⊓ W'.restrictScalars R) (B ⊓ W'.restrictScalars R) ≤ locLen p A B := by
  unfold locLen
  refine ENat.toNat_le_toNat ?_ hfin
  have hle : localization₂ p (A ⊓ W'.restrictScalars R) ≤ localization₂ p A := locBasic_locS_mono _ inf_le_left
  let f : (↥(localization₂ p (A ⊓ W'.restrictScalars R)) ⧸
        (localization₂ p (B ⊓ W'.restrictScalars R)).comap (localization₂ p (A ⊓ W'.restrictScalars R)).subtype) →ₗ[R]
      (↥(localization₂ p A) ⧸ (localization₂ p B).comap (localization₂ p A).subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hle) (by
      rintro ⟨x, hx⟩ hxB
      exact locBasic_locS_mono _ inf_le_left hxB)
  refine Module.length_le_of_injective f ?_
  rw [injective_iff_map_eq_zero]
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    intro hx
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    obtain ⟨x, s, hs, hsx⟩ := x
    obtain ⟨t, ht, htx⟩ := hx
    refine ⟨s * t, mul_mem hs ht, ?_, ?_⟩
    · rw [mul_smul]
      exact B.smul_mem s htx
    · rw [mul_comm, mul_smul]
      exact (W'.restrictScalars R).smul_mem t hsx.2

theorem idxRules_inf_lat {W : Submodule K V} {A B : Submodule R V}
    (hA : A.FG ∧ Submodule.span K (A : Set V) = W) (hB : B.FG ∧ Submodule.span K (B : Set V) = W) :
    (A ⊓ B).FG ∧ Submodule.span K ((A ⊓ B : Submodule R V) : Set V) = W := by
  refine ⟨hA.1.of_le inf_le_left, le_antisymm ?_ ?_⟩
  · rw [← hA.2]
    exact Submodule.span_mono inf_le_left
  · intro x hx
    have hx' : x ∈ locS R⁰ (A ⊓ B) := by
      rw [locBasic_locS_inf]
      exact ⟨idxRules_denom A (by rw [hA.2]; exact hx), idxRules_denom B (by rw [hB.2]; exact hx)⟩
    obtain ⟨d, hd, hdx⟩ := hx'
    have hd0 : algebraMap R K d ≠ 0 := idxRules_alg_ne (nonZeroDivisors.ne_zero hd)
    have e : x = (algebraMap R K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hdx)

end Gen

theorem index_monotone : IdxMono := by
  intro K _ _ _ Z _ _ _ _ _ w W A B B' hA hB hB' hle
  have h := idxRules_add w.asIdeal W A B' B hA hB' hB
  have h2 : lidx w.asIdeal B' B = locLen w.asIdeal B' B := idxRules_lidx_of_le _ hle
  unfold lix
  rw [h, h2]
  have : (0 : ℤ) ≤ (locLen w.asIdeal B' B : ℤ) := Int.natCast_nonneg _
  linarith

theorem index_scale_inclusion : IdxScaleIn := by
  intro K _ _ _ Z _ _ _ _ _ w W A B hA hB a ha
  have hl := idxRules_scG_lat (R := 𝓞 K) ha hB
  refine ⟨hl, ?_⟩
  have h := idxRules_add w.asIdeal W A B (scG a B) hA hB hl
  have h2 := idxRules_scale w W B hB ha
  change lidx w.asIdeal A (scG a B) = lidx w.asIdeal A B + _
  rw [h, h2]
  rfl

theorem index_truncation_le : IdxCutLe := by
  intro K _ _ _ Z _ _ _ _ _ w W W' A B hA hB hle hW
  have hcl : cut W' B ≤ cut W' A := inf_le_inf_right _ hle
  have h1 : lix w (cut W' A) (cut W' B) = locLen w.asIdeal (cut W' A) (cut W' B) :=
    idxRules_lidx_of_le _ hcl
  have h2 : lix w A B = locLen w.asIdeal A B := idxRules_lidx_of_le _ hle
  refine ⟨idxRules_cut_lat hW hA, ?_, ?_⟩
  · rw [h1]
    exact Int.natCast_nonneg _
  · rw [h1, h2]
    exact_mod_cast idxRules_cut_le w.asIdeal W' A B
      (idxRules_fin w.asIdeal A B hA.1 (idxRules_le_locS hA.2 hB.2))

theorem index_transport : IdxTransport := by
  intro K _ _ _ Z _ _ _ _ w d φ hφ A B
  exact idxRules_lidx_map w.asIdeal φ hφ A B

theorem lattice_intersection : LatInter := by
  intro K _ _ _ Z _ _ _ _ _ A B hA hB a ha
  exact idxRules_inf_lat hA (idxRules_scG_lat (R := 𝓞 K) ha hB)

end Formalism.EigenvalueLevelCeiling
