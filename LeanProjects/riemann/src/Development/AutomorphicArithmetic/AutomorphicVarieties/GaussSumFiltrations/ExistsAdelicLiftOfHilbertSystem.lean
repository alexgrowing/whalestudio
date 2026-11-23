import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashRationalMatrixProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.RationalGL2InfiniteFiniteFactor
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.AdelicLift

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem sl_indep {k : ℕ} {Ψ : GL (Fin 2) (Af F) → Hn F → ℂ} (hΨ : Sys k Ψ) (h : GL (Fin 2) (InfinitePlace F → ℝ))
    (g : GL (Fin 2) (Af F)) (τ τ' : GL (Fin 2) F) (hτ : Pos (toInf τ * h)) (hτ' : Pos (toInf τ' * h)) :
    sl k (toInf τ * h) (Ψ (toFin τ * g)) = sl k (toInf τ' * h) (Ψ (toFin τ' * g)) := by
  have hinv : Pos (toInf τ' * h)⁻¹ := (SlashCocycle.slash_cocycle F k _ _ 0 hτ' hτ').2.1
  have hγ : Pos (toInf (τ * τ'⁻¹)) := by
    have e : toInf (τ * τ'⁻¹) = (toInf τ * h) * (toInf τ' * h)⁻¹ := by
      rw [map_mul, map_inv]; group
    rw [e]
    exact (SlashCocycle.slash_cocycle F k _ _ 0 hτ hinv).1
  have hTP : TP (τ * τ'⁻¹).val.det := ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F k 0).2.1 _).1.1 hγ
  have e1 : toInf τ * h = toInf (τ * τ'⁻¹) * (toInf τ' * h) := by
    rw [map_mul, map_inv]; group
  have e2 : toFin τ * g = toFin (τ * τ'⁻¹) * (toFin τ' * g) := by
    rw [map_mul, map_inv]; group
  rw [e1, e2, (SlashCocycle.slash_cocycle F k _ _ _ hγ hτ').2.2.2.1, hΨ.left _ hTP]

theorem map_scalar {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map f.toMonoidHom z) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.GeneralLinearGroup.scalar]
  · simp [Matrix.GeneralLinearGroup.scalar, hij]

theorem scalar_comm {R : Type} [CommRing R] (z : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  apply Units.ext
  exact ((Matrix.scalar_commute (z : R) (fun r => Commute.all _ r) g.val).eq).symm

theorem exists_lift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : GA F 2 → ℂ, IsLift k Ψ φ ∧ (∀ u ∈ KLev F 2 1, ∀ g, φ (g * finGL F 2 u) = φ g) ∧ ∀ (z : Ideles F) (g : GA F 2), φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = φ g := by
  intro F _ _ _ k hk Ψ hΨ
  choose τ hτ using (GlobalTheory.T.rational_GL2_infinite_finite_factor F 1).2
  let G : GL (Fin 2) (InfinitePlace F → ℝ) → GL (Fin 2) (Af F) → Hn F → ℂ :=
    fun h g => sl k (toInf (τ h) * h) (Ψ (toFin (τ h) * g))
  have hG : ∀ h g σ, Pos (toInf σ * h) → G h g = sl k (toInf σ * h) (Ψ (toFin σ * g)) :=
    fun h g σ hσ => sl_indep hΨ h g _ _ (hτ h) hσ
  refine ⟨fun x => G (Matrix.GeneralLinearGroup.map (TR.pInf F) x) (Matrix.GeneralLinearGroup.map (pFin F) x)
    fun _ => UpperHalfPlane.I, ⟨fun γ x => ?_, fun h hh g => ?_⟩, fun u hu x => ?_, fun z x => ?_⟩
  · rw [(GlobalTheory.T.rational_GL2_infinite_finite_factor F γ).1]
    simp only [map_mul, TR.pInf_infGL, TR.pInf_finGL, TR.pFin_infGL, pFin_finGL, mul_one, one_mul]
    generalize Matrix.GeneralLinearGroup.map (TR.pInf F) x = h
    generalize Matrix.GeneralLinearGroup.map (pFin F) x = g
    have hp : Pos (toInf (τ (toInf γ * h) * γ) * h) := by
      rw [map_mul, mul_assoc]; exact hτ _
    rw [hG h g _ hp]
    simp only [G, map_mul, mul_assoc]
  · simp only [map_mul, TR.pInf_infGL, TR.pInf_finGL, TR.pFin_infGL, pFin_finGL, mul_one, one_mul]
    rw [hG h g 1 (by simpa using hh)]
    simp only [map_one, one_mul]
  · simp only [map_mul, TR.pInf_finGL, pFin_finGL, mul_one, G]
    rw [← mul_assoc, hΨ.right _ u hu]
  · simp only [map_mul, map_scalar]
    generalize Matrix.GeneralLinearGroup.map (TR.pInf F) x = h
    generalize Matrix.GeneralLinearGroup.map (pFin F) x = g
    generalize Units.map (TR.pInf F).toMonoidHom z = t
    generalize Units.map (pFin F).toMonoidHom z = s
    have e : toInf (τ h) * (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) t * (toInf (τ h) * h) := by
      rw [← mul_assoc, scalar_comm, mul_assoc]
    have e' : toFin (τ h) * (Matrix.GeneralLinearGroup.scalar (Fin 2) s * g) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) s * (toFin (τ h) * g) := by
      rw [← mul_assoc, scalar_comm, mul_assoc]
    have H := (GlobalTheory.T.hilbert_slash_rational_matrix_properties F k (Ψ (toFin (τ h) * g))).2.2.1 hk t _ (hτ h)
    rw [hG _ _ (τ h) (by rw [e]; exact H.1), e, e', hΨ.cent, H.2]

end GlobalTheory.HilbertThetaSeries.AdelicLift

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_lift_of_hilbert_system : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : GA F 2 → ℂ, IsLift k Ψ φ ∧ (∀ u ∈ KLev F 2 1, ∀ g, φ (g * finGL F 2 u) = φ g) ∧ ∀ (z : Ideles F) (g : GA F 2), φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = φ g := by
  first | exact @GlobalTheory.HilbertThetaSeries.AdelicLift.exists_lift | exact GlobalTheory.HilbertThetaSeries.AdelicLift.exists_lift | (intros; apply GlobalTheory.HilbertThetaSeries.AdelicLift.exists_lift <;> assumption)
