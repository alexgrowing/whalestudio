import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraBaseChangeIsoStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDiagonalCoordinatesOfDeterminantCondition
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieCoord

theorem exists_lieCoord_unif : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ} {L : Set E}
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X) (p : X.A.left ⟶ X₀.A.left),
    X.IsPullBy X₀ (spMap R.subtype) p →
    ∃ cd : X₀.Lie →ₗ[R] (Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ v, ∃ v' : X.Lie, Obj.LieCorr R.subtype p v v' ∧ U.u.IsDiff (cd v) v'.hom) ∧
      (∀ v (v' : X.Lie) W, Obj.LieCorr R.subtype p v v' → U.u.IsDiff W v'.hom → W = cd v) ∧
      ∀ ω : X₀.Lie →ₗ[R] R, ∃ lam : Fin (Module.finrank ℚ (FR E)) → ℂ, ∀ v, ((ω v : R) : ℂ) = ∑ j, lam j * cd v j := by
  intro E _ _ I _ 𝔠 φ L R X₀ X U p hpull
  obtain ⟨e, he⟩ := GlobalTheory.T.lie_algebra_base_change_iso (R := R) (R' := ℂ) hpull
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective U.u X.dim
  obtain ⟨d, hdi, hd⟩ := GlobalTheory.DiagCoord.exists_diff_linear U.u X.rm h₁ h₂
  have hds : Function.Surjective d := fun w => by
    obtain ⟨v, ⟨hv, hw⟩, -⟩ := h₂ w
    exact ⟨GlobalTheory.Serre.Lie.mk X.rm v hv, (h₁ v hv).unique (hd _) hw⟩
  let D : X.Lie ≃ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) := LinearEquiv.ofBijective d ⟨hdi, hds⟩
  let cd : X₀.Lie →ₗ[R] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    ((D.toLinearMap ∘ₗ e.toLinearMap).restrictScalars R) ∘ₗ TensorProduct.mk R ℂ X₀.Lie 1
  have hcd : ∀ v, cd v = d (e (1 ⊗ₜ v)) := fun v => rfl
  refine ⟨cd, fun v => ⟨e (1 ⊗ₜ v), (he v _).2 rfl, by rw [hcd]; exact hd _⟩, fun v v' W hc hW => ?_, fun ω => ?_⟩
  · have h' : v' = e (1 ⊗ₜ v) := (he v v').1 hc
    rw [hcd, ← h']
    exact (h₁ _ v'.isTangent).unique hW (hd v')
  · let ωc : ℂ ⊗[R] X₀.Lie →ₗ[ℂ] ℂ := LinearMap.liftBaseChange ℂ ((Algebra.linearMap R ℂ) ∘ₗ ω)
    let Λ : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] ℂ := ωc ∘ₗ e.symm.toLinearMap ∘ₗ D.symm.toLinearMap
    refine ⟨fun j => Λ (Pi.single j 1), fun v => ?_⟩
    have h1 : ((ω v : R) : ℂ) = Λ (cd v) := by
      simp [Λ, ωc, cd, D]
      rfl
    rw [h1, LinearMap.pi_apply_eq_sum_univ Λ (cd v)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    ext i
    simp [Pi.single_apply, eq_comm]

end GlobalTheory.LieCoord
