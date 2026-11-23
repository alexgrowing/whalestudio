import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.Jets.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExistsAndVectorEqSmulTranslate
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem norm_adjoint_apply_of_norm_preserving {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (P : V →L[ℂ] V) (hP : ∀ v, ‖P v‖ = ‖v‖) (v : V) :
    ‖ContinuousLinearMap.adjoint P v‖ = ‖v‖ := by
  let L : V →ₗᵢ[ℂ] V := ⟨(P : V →ₗ[ℂ] V), hP⟩
  have hsurj : Function.Surjective (P : V →ₗ[ℂ] V) :=
    LinearMap.surjective_of_injective (f := (P : V →ₗ[ℂ] V)) L.injective
  obtain ⟨u, rfl⟩ := hsurj v
  have h1 : ContinuousLinearMap.adjoint P (P u) = u := by
    apply ext_inner_right ℂ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact L.inner_map_map u w
  change ‖ContinuousLinearMap.adjoint P (P u)‖ = ‖P u‖
  rw [h1, hP]

theorem norm_adjoint_of_intertwine {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (P : V →L[ℂ] V) (Q : U →L[ℂ] U) (A A' : U →L[ℂ] V) (hQ : ∀ v, ‖Q v‖ = ‖v‖)
    (h : A'.comp Q = P.comp A) (v : V) :
    ‖ContinuousLinearMap.adjoint A' v‖ = ‖ContinuousLinearMap.adjoint A (ContinuousLinearMap.adjoint P v)‖ := by
  rw [← norm_adjoint_apply_of_norm_preserving Q hQ]
  have h1 := congrArg (fun T : U →L[ℂ] V => ContinuousLinearMap.adjoint T v) h
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply] at h1
  rw [h1]

theorem norm_adjoint_real_pow_smul {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (A : U →L[ℂ] V) (t : ℝ) (d : ℕ) (v : V) :
    ‖ContinuousLinearMap.adjoint (((t : ℂ) ^ d) • A) v‖ ^ 2 =
      (t ^ 2) ^ d * ‖ContinuousLinearMap.adjoint A v‖ ^ 2 := by
  rw [LinearIsometryEquiv.map_smulₛₗ, ContinuousLinearMap.smul_apply, norm_smul, mul_pow]
  congr 1
  rw [RCLike.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← pow_mul, mul_comm, pow_mul, sq_abs]

theorem lower_bound_spreads :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (πp : Mx (n + 1) r → (Vp →L[ℂ] Vp)) (πm : Mx (n + 1) r → (Vm →L[ℂ] Vm)) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (Ap : (Fin (2 * r + (n + 1) + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + (n + 1) + 1) → ℂ) → (Vm →L[ℂ] V)) (n₀ : ℕ) (b : ℝ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖πp h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖πm h v‖ = ‖v‖) → IsFrameOf (n + 1) r [z] B → GlobalTheory.WigSh.WigMap (n + 1) r z πp π n₀ Ap → GlobalTheory.WigSh.WigMap (n + 1) r z πm π n₀ Am → (∀ v : V, ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap (B (Fin.last n))) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am (B (Fin.last n))) v‖ ^ 2)) → ∀ ω, inWb (n + 1) r ω → herm (Hpk (n + 1) r) ω z = 0 → ∀ v : V, (herm (Hpk (n + 1) r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  intro V _ _ _ Vp _ _ _ Vm _ _ _ n r z π πp πm B Ap Am n₀ b hz hT hπ hπp hπm hB hAp hAm hlow ω hω hωz v
  obtain ⟨t, h, hh, -, hre, rfl⟩ :=
    (GlobalTheory.frame_exists_and_vector_eq_smul_translate n r z hz hT).2 B hB ω hω hωz
  rw [hre, hAp.2.2.1, hAm.2.2.1, norm_adjoint_real_pow_smul, norm_adjoint_real_pow_smul,
    norm_adjoint_of_intertwine (π h) (πp h) _ _ (hπp h hh) (hAp.2.1 h hh _),
    norm_adjoint_of_intertwine (π h) (πm h) _ _ (hπm h hh) (hAm.2.1 h hh _)]
  have h1 := hlow (ContinuousLinearMap.adjoint (π h) v)
  rw [norm_adjoint_apply_of_norm_preserving (π h) (hπ h hh)] at h1
  have h2 : (0 : ℝ) ≤ (t ^ 2) ^ n₀ := by positivity
  calc _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
    _ = _ := by ring

end GlobalTheory.WigSh
