import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeVectorBundlePullback
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_vector_bundle_pullback : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (E' : Type) [AddCommGroup E'] [Module Ω' E'] (j : E →+ E') (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E), Dominates ξ' ξ f i → (∀ (a : Ω) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → E), LinearIndependent Ω b → LinearIndependent Ω' fun k => j (b k)) → L.IsVBOn T r V → (L.pull ξ' f j).IsVBOn {p' | ∃ h : genPt ξ ⤳ f p'.1, (⟨f p'.1, h⟩ : Cpt ξ) ∈ T} r (Submodule.span Ω' (j '' V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LatPull.isVBOn_pull | exact GlobalTheory.CompanionTheory.Ar.LatPull.isVBOn_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.LatPull.isVBOn_pull <;> assumption)
