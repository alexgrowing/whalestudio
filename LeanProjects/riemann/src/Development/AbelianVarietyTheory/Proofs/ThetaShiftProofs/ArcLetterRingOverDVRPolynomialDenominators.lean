import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

noncomputable section

namespace GlobalTheory.LetterDenom

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section General

variable {σ R L : Type*} [CommRing R] [CommRing L]

theorem exists_map_eq_of_constantCoeff (φ : R →+* L) (A G : MvPolynomial σ R) (P : MvPolynomial σ L)
    (hA : MvPolynomial.constantCoeff A = 1)
    (h : MvPolynomial.map φ A * P = MvPolynomial.map φ G) : ∃ Q, MvPolynomial.map φ Q = P := by
  classical
  have hcoe : ∀ B : MvPolynomial σ R, ((MvPolynomial.map φ B : MvPolynomial σ L) : MvPowerSeries σ L) =
      MvPowerSeries.map φ (B : MvPowerSeries σ R) := by
    intro B
    ext m
    simp [MvPolynomial.coeff_map]
  have hu : (A : MvPowerSeries σ R) * MvPowerSeries.invOfUnit (A : MvPowerSeries σ R) 1 = 1 := by
    apply MvPowerSeries.mul_invOfUnit
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
    simpa [MvPolynomial.constantCoeff_eq] using hA
  have hP : (P : MvPowerSeries σ L) =
      MvPowerSeries.map φ (MvPowerSeries.invOfUnit (A : MvPowerSeries σ R) 1 * (G : MvPowerSeries σ R)) := by
    rw [map_mul, ← hcoe G, ← h, MvPolynomial.coe_mul, hcoe A, ← mul_assoc, ← map_mul, mul_comm _ (A : MvPowerSeries σ R), hu,
      map_one, one_mul]
  have hc : ∀ m, ∃ r, φ r = P.coeff m := by
    intro m
    rw [← MvPolynomial.coeff_coe, hP, MvPowerSeries.coeff_map]
    exact ⟨_, rfl⟩
  choose r hr using hc
  refine ⟨∑ m ∈ P.support, MvPolynomial.monomial m (r m), ?_⟩
  rw [map_sum]
  conv_rhs => rw [P.as_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.map_monomial, hr]

theorem exists_map_eq_of_eval (φ : R →+* L) (a : σ → R) (A G : MvPolynomial σ R) (P : MvPolynomial σ L)
    (hA : MvPolynomial.eval a A = 1)
    (h : MvPolynomial.map φ A * P = MvPolynomial.map φ G) : ∃ Q, MvPolynomial.map φ Q = P := by
  let s : σ → MvPolynomial σ R := fun x => MvPolynomial.X x + MvPolynomial.C (a x)
  let t : σ → MvPolynomial σ R := fun x => MvPolynomial.X x - MvPolynomial.C (a x)
  have h1 : MvPolynomial.constantCoeff (MvPolynomial.bind₁ s A) = 1 := by
    rw [← hA]
    have : (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R).comp (MvPolynomial.bind₁ s).toRingHom =
        MvPolynomial.eval a := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro x; simp [s]
    exact RingHom.congr_fun this A
  have h2 := congrArg (MvPolynomial.bind₁ fun x => MvPolynomial.map φ (s x)) h
  rw [map_mul, ← MvPolynomial.map_bind₁, ← MvPolynomial.map_bind₁] at h2
  obtain ⟨Q, hQ⟩ := exists_map_eq_of_constantCoeff φ _ _ _ h1 h2
  refine ⟨MvPolynomial.bind₁ t Q, ?_⟩
  rw [MvPolynomial.map_bind₁, hQ, MvPolynomial.bind₁_bind₁]
  have : (fun x => MvPolynomial.bind₁ (fun i => MvPolynomial.map φ (t i)) (MvPolynomial.map φ (s x))) =
      MvPolynomial.X := by
    funext x
    simp [s, t]
  rw [this, MvPolynomial.bind₁_X_left]
  rfl

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eval_arcDetR (Dw : Datum H) (V : Type) [CommRing V] :
    MvPolynomial.eval (fun x : ArcLt Dw => if x.2.1 = x.2.2 then (1 : PowerSeries V) else 0)
      (arcDetR Dw V) = 1 := by
  classical
  unfold arcDetR
  rw [map_prod]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [RingHom.map_det]
  convert Matrix.det_one (n := Fin (Dw.mult τ)) (R := PowerSeries V)
  ext i k : 2
  simp [Matrix.one_apply]

theorem map_arcDetR (Dw : Datum H) (V K : Type) [CommRing V] [Field K] (φ : PowerSeries V →+* LaurentSeries K) :
    MvPolynomial.map φ (arcDetR Dw V) = arcDet Dw K := by
  unfold arcDetR arcDet
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i k : 2
  simp

theorem arcDetR_ne_zero (Dw : Datum H) (V : Type) [CommRing V] [Nontrivial V] : arcDetR Dw V ≠ 0 := by
  intro h0
  have h1 := eval_arcDetR Dw V
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

theorem den_ne_zero (Dw : Datum H) (V : Type) [CommRing V] [IsDomain V] {ϖ : V} (hϖ : ϖ ≠ 0) :
    MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V ≠ 0 := by
  refine mul_ne_zero ?_ (arcDetR_ne_zero Dw V)
  rw [Ne, MvPolynomial.C_eq_zero]
  refine mul_ne_zero ?_ PowerSeries.X_ne_zero
  intro h
  exact hϖ (PowerSeries.C_injective (h.trans (map_zero _).symm))

section Parts

variable (Dw : Datum H) (V K : Type) [CommRing V] [IsDomain V] [Field K] {ϖ : V}

theorem isDomain_letter (hϖ : ϖ ≠ 0) : IsDomain (ArcSR Dw V ϖ) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (den_ne_zero Dw V hϖ))

theorem algebraMap_letter_injective (hϖ : ϖ ≠ 0) :
    Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ)) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (den_ne_zero Dw V hϖ))

theorem flat_of_injective {A B : Type} [CommRing A] [IsDomain A] [IsBezout A] [CommRing B] [IsDomain B]
    (j : A →+* B) (hi : Function.Injective j) : j.Flat := by
  letI : Algebra A B := j.toAlgebra
  change Module.Flat A B
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  have hx' : j a * x = 0 := hx
  have ha' : j a ≠ 0 := fun h => nonZeroDivisors.ne_zero ha (hi (h.trans (map_zero _).symm))
  exact (mul_eq_zero.mp hx').resolve_left ha'

theorem exists_lift (hϖ : ϖ ≠ 0) (φ : PowerSeries V →+* LaurentSeries K) (hφ : Function.Injective φ) :
    ∃ ψ : ArcSR Dw V ϖ →+* ArcS Dw K,
      ψ.comp (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ)) =
        (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)).comp (MvPolynomial.map φ) := by
  have hu : IsUnit (((algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)).comp
      (MvPolynomial.map φ)) (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)) := by
    rw [map_mul]
    refine IsUnit.mul ?_ ?_
    · have hne : φ (PowerSeries.C ϖ * PowerSeries.X) ≠ 0 := by
        intro h
        apply den_ne_zero Dw V hϖ
        rw [hφ (h.trans (map_zero _).symm), map_zero, zero_mul]
      rw [RingHom.comp_apply, MvPolynomial.map_C]
      exact (hne.isUnit.map MvPolynomial.C).map _
    · rw [RingHom.comp_apply, map_arcDetR]
      exact IsLocalization.Away.algebraMap_isUnit _
  exact ⟨IsLocalization.Away.lift _ hu, IsLocalization.Away.lift_comp _ hu⟩

theorem denominators_gen {σ R L S S' : Type} [CommRing R] [CommRing L] [CommRing S] [CommRing S'] [IsDomain S]
    [Algebra (MvPolynomial σ R) S] (c Δ : MvPolynomial σ R) [IsLocalization.Away (c * Δ) S]
    (hinj : Function.Injective (algebraMap (MvPolynomial σ R) S))
    (j : MvPolynomial σ L →+* S') (hj : Function.Injective j) (a : σ → R) (ha : MvPolynomial.eval a Δ = 1)
    (φ : R →+* L) (hφ : Function.Injective φ) (ψ : S →+* S')
    (hψ : ∀ B, ψ (algebraMap (MvPolynomial σ R) S B) = j (MvPolynomial.map φ B))
    (f : S) (P : MvPolynomial σ L) (hP : j P = ψ f) :
    ∃ (N : ℕ) (G : MvPolynomial σ R), f * algebraMap (MvPolynomial σ R) S c ^ N = algebraMap _ S G := by
  obtain ⟨N, G₀, hf⟩ := IsLocalization.Away.surj (c * Δ) f
  have h3 := congrArg ψ hf
  rw [map_mul ψ, ← map_pow, ← hP, hψ, hψ, ← map_mul] at h3
  have h4 := hj h3
  have h5 : MvPolynomial.map φ (Δ ^ N) * (P * MvPolynomial.map φ (c ^ N)) = MvPolynomial.map φ G₀ := by
    rw [← h4, mul_pow, map_mul]; ring
  obtain ⟨Q, hQ⟩ := exists_map_eq_of_eval φ a _ _ _ (by rw [map_pow, ha, one_pow]) h5
  rw [← hQ, ← map_mul] at h5
  have h6 := MvPolynomial.map_injective φ hφ h5
  refine ⟨N, Q, ?_⟩
  have hu : IsUnit (algebraMap _ S (c * Δ)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at hu
  have hu' : IsUnit (algebraMap _ S (Δ ^ N)) := by
    rw [map_pow]
    exact (isUnit_of_mul_isUnit_right hu).pow N
  apply hu'.mul_left_cancel
  rw [← map_mul, h6, ← hf, map_mul, map_pow, mul_pow]
  ring

theorem denominators (hϖ : ϖ ≠ 0) (φ : PowerSeries V →+* LaurentSeries K) (hφ : Function.Injective φ)
    (ψ : ArcSR Dw V ϖ →+* ArcS Dw K)
    (hψ : ψ.comp (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ)) =
        (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)).comp (MvPolynomial.map φ))
    (f : ArcSR Dw V ϖ) (P : MvPolynomial (ArcLt Dw) (LaurentSeries K))
    (hP : algebraMap _ (ArcS Dw K) P = ψ f) :
    ∃ (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries V)),
      f * arcιR Dw V ϖ (PowerSeries.C (R := V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw V ϖ) G := by
  haveI := isDomain_letter Dw V hϖ
  have hinj := algebraMap_letter_injective Dw V hϖ
  have hD : arcDet Dw K ≠ 0 := by
    rw [← map_arcDetR Dw V K φ]
    exact fun h => arcDetR_ne_zero Dw V (MvPolynomial.map_injective φ hφ (h.trans (map_zero _).symm))
  have hinjL : Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)) :=
    IsLocalization.injective (M := Submonoid.powers (arcDet Dw K)) _
      (powers_le_nonZeroDivisors_of_noZeroDivisors hD)
  exact denominators_gen (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X)) (arcDetR Dw V) hinj _ hinjL _
    (eval_arcDetR Dw V) φ hφ ψ (fun B => RingHom.congr_fun hψ B) f P hP

theorem comp_eq_of_letters (φ : PowerSeries V →+* PowerSeries K) (ψ : ArcSR Dw V ϖ →+* ArcS Dw K) :
    ψ.comp (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ)) =
        (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)).comp
          (MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ K).comp φ)) ↔
      ψ.comp (arcιR Dw V ϖ) = (arcι Dw K).comp φ ∧ ∀ x : ArcLt Dw, ψ (arcXR Dw V ϖ x) = arcX Dw K x.1 x.2.1 x.2.2 := by
  constructor
  · intro hψ
    refine ⟨RingHom.ext fun p => ?_, fun x => ?_⟩
    · have := RingHom.congr_fun hψ (MvPolynomial.C p)
      simp only [RingHom.comp_apply, MvPolynomial.map_C] at this
      simp only [RingHom.comp_apply, arcιR, arcι, this]
    · have := RingHom.congr_fun hψ (MvPolynomial.X x)
      simp only [RingHom.comp_apply, MvPolynomial.map_X] at this
      simp only [arcXR, arcX, this]
  · rintro ⟨h1, h2⟩
    apply MvPolynomial.ringHom_ext
    · intro p
      have := RingHom.congr_fun h1 p
      simp only [RingHom.comp_apply, arcιR, arcι] at this
      simp only [RingHom.comp_apply, MvPolynomial.map_C, this]
    · intro x
      have := h2 x
      simp only [arcXR, arcX] at this
      simp only [RingHom.comp_apply, MvPolynomial.map_X, this]

theorem flat_letter [IsBezout V] (hϖ : ϖ ≠ 0) : ((arcιR Dw V ϖ).comp (PowerSeries.C (R := V))).Flat := by
  haveI := isDomain_letter Dw V hϖ
  refine flat_of_injective _ ?_
  rw [arcιR, RingHom.coe_comp, RingHom.coe_comp]
  exact ((algebraMap_letter_injective Dw V hϖ).comp (MvPolynomial.C_injective _ _)).comp PowerSeries.C_injective

omit [IsDomain V] in
theorem toLaurent_injective (i : V →+* K) (hi : Function.Injective i) :
    Function.Injective ((HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map i)) := by
  rw [RingHom.coe_comp]
  exact HahnSeries.ofPowerSeries_injective.comp (PowerSeries.map_injective _ hi)

end Parts

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V), ϖ ≠ 0 → IsDomain (ArcSR Dw Tv.V ϖ) ∧ Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (ArcSR Dw Tv.V ϖ)) ∧ ((arcιR Dw Tv.V ϖ).comp (PowerSeries.C (R := Tv.V))).Flat ∧ (∃ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) ∧ ∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) ∧ ∀ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) → (∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) → ∀ f : ArcSR Dw Tv.V ϖ, (∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr), algebraMap _ (ArcS Dw Tv.Fr) P = ψ f) → ∃ (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G := by
  intro E _ _ _ H Dw Tv ϖ hϖ
  have hφ := toLaurent_injective Tv.V Tv.Fr (algebraMap Tv.V Tv.Fr) (IsFractionRing.injective Tv.V Tv.Fr)
  refine ⟨isDomain_letter Dw Tv.V hϖ, algebraMap_letter_injective Dw Tv.V hϖ, flat_letter Dw Tv.V hϖ, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_lift Dw Tv.V Tv.Fr hϖ _ hφ
    exact ⟨ψ, (comp_eq_of_letters Dw Tv.V Tv.Fr _ ψ).1 hψ⟩
  · rintro ψ h1 h2 f ⟨P, hP⟩
    exact denominators Dw Tv.V Tv.Fr hϖ _ hφ ψ ((comp_eq_of_letters Dw Tv.V Tv.Fr _ ψ).2 ⟨h1, h2⟩) f P hP

end GlobalTheory.LetterDenom
