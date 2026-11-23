import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory

theorem dualBasis_baseChange : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] {M' : Type*} [AddCommGroup M'] [Module R' M']
    (f : M →ₛₗ[algebraMap R R'] M') (hf : Function.Bijective (liftSemi f)) {n : ℕ}
    (b : Module.Dual R M ≃ₗ[R] (Fin n → R)) (x : Fin n → Module.Dual R' M')
    (hx : ∀ k c, x k (f c) = algebraMap R R' (b.symm (Pi.single k 1) c)),
   LinearIndependent R' x ∧ Submodule.span R' (Set.range x) = ⊤ := by
  intro R R' _ _ _ M _ _ _ _ M' _ _ f hf n b x hx
  classical
  let B : Module.Basis (Fin n) R (Module.Dual R M) := Module.Basis.ofEquivFun b
  have hB : ∀ k, B k = b.symm (Pi.single k 1) := fun k => by simp [B]
  let C : Module.Basis (Fin n) R M := B.dualBasis.map (Module.evalEquiv R M).symm
  have hC : ∀ k l, B k (C l) = if k = l then 1 else 0 := fun k l => by
    have e : B k (C l) = Module.evalEquiv R M (C l) (B k) := rfl
    rw [e]
    simp only [C, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Module.Basis.dualBasis_apply_self]
  let D : Module.Basis (Fin n) R' M' :=
    (Algebra.TensorProduct.basis R' C).map (LinearEquiv.ofBijective (liftSemi f) hf)
  have hD : ∀ k, D k = f (C k) := fun k => by
    simp [D, Algebra.TensorProduct.basis_apply]
  have hxD : ∀ k, x k = D.dualBasis k := fun k => by
    refine D.ext fun l => ?_
    rw [hD, hx, ← hB, hC, ← hD, D.dualBasis_apply_self]
    by_cases h : k = l
    · subst h; simp
    · simp [h, Ne.symm h]
  have : x = ⇑D.dualBasis := funext hxD
  rw [this]
  exact ⟨D.dualBasis.linearIndependent, D.dualBasis.span_eq⟩

end GlobalTheory
