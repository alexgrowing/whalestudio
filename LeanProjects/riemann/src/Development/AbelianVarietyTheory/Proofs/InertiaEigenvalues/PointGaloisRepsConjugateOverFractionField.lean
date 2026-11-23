import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceCoefficientRing

noncomputable section

namespace GlobalTheory.PointRepConj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem exists_gl_of_equiv {K Γ : Type} [Field K] {n : ℕ} (A B : Γ → Matrix (Fin n) (Fin n) K)
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (he : ∀ g u, e (Matrix.toLin' (A g) u) = Matrix.toLin' (B g) (e u)) :
    ∃ P : GL (Fin n) K, ∀ g, (P : Matrix (Fin n) (Fin n) K) * A g = B g * (P : Matrix (Fin n) (Fin n) K) := by
  refine ⟨⟨LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)),
      LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)), ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    simp
  · rw [← LinearMap.toMatrix'_comp]
    simp
  · intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simpa [Matrix.toLin'_mul] using he g u

theorem main : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))), GoodR N i r → GoodR N i r' → ∀ x, (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r x g).map (toK N i) = (rO N i r' x g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) := by
  intro hC R H what₂ N i r r' hr hr' x
  have h₁ := (GlobalTheory.ComplementCompare.isHeckeGalois_iff N i x (r x)).1 (hr x)
  have h₂ := (GlobalTheory.ComplementCompare.isHeckeGalois_iff N i x (r' x)).1 (hr' x)
  obtain ⟨e, he⟩ := GlobalTheory.ComplementCompare.isRx_unique N hC i x _ _ h₁ h₂
  exact exists_gl_of_equiv _ _ e he

end GlobalTheory.PointRepConj

end
