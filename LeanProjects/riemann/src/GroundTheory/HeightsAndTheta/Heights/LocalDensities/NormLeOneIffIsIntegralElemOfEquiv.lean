import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.LeviFormGbPotOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

open IsDedekindDomain NumberField Polynomial Rat.HeightOneSpectrum

theorem isIntegralElem_comp_ringEquiv {A B S : Type*} [CommRing A] [CommRing B] [CommRing S]
    (φ : A ≃+* B) (f : B →+* S) (x : S) :
    (f.comp (φ : A →+* B)).IsIntegralElem x ↔ f.IsIntegralElem x := by
  constructor
  · rintro ⟨q, hq, hx⟩
    exact ⟨q.map (φ : A →+* B), hq.map _, by rwa [eval₂_map]⟩
  · rintro ⟨q, hq, hx⟩
    refine ⟨q.map (φ.symm : B →+* A), hq.map _, ?_⟩
    rw [eval₂_map, RingHom.comp_assoc]
    have : (φ : A →+* B).comp (φ.symm : B →+* A) = RingHom.id B :=
      RingHom.ext fun b => by simp
    rwa [this, RingHom.comp_id]

theorem norm_le_one_iff_isIntegralElem_padicInt (p : ℕ) [Fact p.Prime] {K : Type*}
    [NormedField K] [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] (x : K) :
    ‖x‖ ≤ 1 ↔ ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])).IsIntegralElem x := by
  have hx : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p] x, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic hx)]
  let : Algebra ℤ_[p] K := ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
  have : IsScalarTower ℤ_[p] ℚ_[p] K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  constructor
  · intro h
    have hl : minpoly ℚ_[p] x ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hmon⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hx)
    refine ⟨q, hmon, ?_⟩
    have h0 : eval₂ (algebraMap ℚ_[p] K) x (q.map (algebraMap ℤ_[p] ℚ_[p])) = 0 := by
      rw [hq]; exact minpoly.aeval ℚ_[p] x
    rwa [eval₂_map] at h0
  · intro h n
    have hxZ : IsIntegral ℤ_[p] x := h
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hxZ, coeff_map,
      PadicInt.algebraMap_apply]
    exact PadicInt.norm_le_one _

theorem norm_le_one_iff_isIntegralElem_of_equiv (p : ℕ) [Fact p.Prime] {E O K : Type*} [Field E]
    [CommRing O] [NormedField K] [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    [Algebra E K] (ι : O →+* E) (e : ℚ_[p] →+* E) (ψ : ℤ_[p] ≃+* O)
    (hψ : ∀ z, ι (ψ z) = e (algebraMap ℤ_[p] ℚ_[p] z))
    (he : algebraMap ℚ_[p] K = (algebraMap E K).comp e) (x : K) :
    ‖x‖ ≤ 1 ↔ ((algebraMap E K).comp ι).IsIntegralElem x := by
  rw [norm_le_one_iff_isIntegralElem_padicInt p, ← isIntegralElem_comp_ringEquiv ψ]
  have : (algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p]) =
      ((algebraMap E K).comp ι).comp (ψ : ℤ_[p] →+* O) :=
    RingHom.ext fun z => by simp [he, hψ]
  rw [this]

theorem finiteDimensional_of_ringEquiv {E₁ E₂ L : Type*} [Field E₁] [Field E₂] [Field L]
    [Algebra E₁ L] [Algebra E₂ L] (e : E₂ ≃+* E₁)
    (he : algebraMap E₂ L = (algebraMap E₁ L).comp (e : E₂ →+* E₁)) [FiniteDimensional E₁ L] :
    FiniteDimensional E₂ L := by
  let : Algebra E₂ E₁ := (e : E₂ →+* E₁).toAlgebra
  have : IsScalarTower E₂ E₁ L := IsScalarTower.of_algebraMap_eq fun z => by rw [he]; rfl
  have : Module.Finite E₂ E₁ := Module.Finite.of_surjective (Algebra.linearMap E₂ E₁) e.surjective
  exact Module.Finite.trans E₁ L

def IntegralOnModelRat : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 ℚ) R] [Module.Flat (𝓞 ℚ) R]
    [Algebra.FiniteType (𝓞 ℚ) R] [IsIntegrallyClosed R] (r g : R) (s : 𝓞 ℚ),
    FourB.IntegralOnModel.Hyp ℚ R r g s → ∃ r' : R, r = algebraMap (𝓞 ℚ) R s * r'

theorem Normality.of_rat (hA : IntegralOnModelRat) : Normality.Statement := by
  intro A _ h a N ⟨hft, hdom, hic, htf, hh, hN, hint⟩
  let _ : Algebra (𝓞 ℚ) A :=
    ((Int.castRingHom A).comp (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)).toAlgebra
  have : IsDomain A := hdom
  have : Algebra.FiniteType (𝓞 ℚ) A := Algebra.FiniteType.of_restrictScalars_finiteType ℤ (𝓞 ℚ) A
  have hmap : ∀ c : 𝓞 ℚ, c ≠ 0 → algebraMap (𝓞 ℚ) A c ≠ 0 := fun c hc =>
    htf _ fun h0 => hc (Rat.ringOfIntegersEquiv.injective (by simpa using h0))
  have : Module.IsTorsionFree (𝓞 ℚ) A := ⟨fun c hc x y hxy => by
    have hc0 : c ≠ 0 := hc.ne_zero
    simp only [Algebra.smul_def] at hxy
    exact mul_left_cancel₀ (hmap c hc0) hxy⟩
  have hNQ : (N : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  suffices hH : FourB.IntegralOnModel.Hyp ℚ A a h (N : 𝓞 ℚ) by
    obtain ⟨r', hr'⟩ := hA A a h (N : 𝓞 ℚ) hH
    exact ⟨r', by rw [hr', map_natCast]⟩
  refine ⟨hNQ, hh, fun v L _ _ _ y _ hyint hyg => ?_⟩
  let P := primesEquiv v
  have : Fact (P : ℕ).Prime := ⟨P.2⟩
  let e : ℚ_[P] ≃+* v.adicCompletion ℚ := (adicCompletion.padicEquiv v).symm.toAlgEquiv.toRingEquiv
  let _ : Algebra ℚ_[P] L :=
    ((algebraMap (v.adicCompletion ℚ) L).comp (e : ℚ_[P] →+* v.adicCompletion ℚ)).toAlgebra
  have : FiniteDimensional ℚ_[P] L := finiteDimensional_of_ringEquiv e rfl
  have : Algebra.IsAlgebraic ℚ_[P] L := inferInstance
  let _ : NormedField L := spectralNorm.normedField ℚ_[P] L
  let _ : NormedAlgebra ℚ_[P] L := spectralNorm.normedAlgebra ℚ_[P] L
  have key : ∀ x : L, ‖x‖ ≤ 1 ↔ ((algebraMap (v.adicCompletion ℚ) L).comp
      (v.adicCompletionIntegers ℚ).subtype).IsIntegralElem x := fun x =>
    norm_le_one_iff_isIntegralElem_of_equiv (P : ℕ) (v.adicCompletionIntegers ℚ).subtype
      (e : ℚ_[P] →+* v.adicCompletion ℚ) (adicCompletionIntegers.padicIntEquiv v).symm.toAlgEquiv.toRingEquiv
      (fun z => adicCompletionIntegers.coe_padicIntEquiv_symm_apply v z) rfl x
  have hle := hint (P : ℕ) L y (fun b => (key _).2 (hyint b)) hyg
  rw [← key, map_natCast, map_natCast, norm_div]
  have hpos : 0 < ‖(N : L)‖ := by
    rw [← map_natCast (algebraMap ℚ_[P] L), norm_algebraMap', norm_pos_iff]
    exact_mod_cast hN.ne'
  exact (div_le_one hpos).2 hle

theorem Normality.of_integralOnModel (hA : FourB.IntegralOnModel.Statement) :
    Normality.Statement :=
  Normality.of_rat fun R _ _ _ _ _ _ r g s hH => hA ℚ R r g s hH

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
