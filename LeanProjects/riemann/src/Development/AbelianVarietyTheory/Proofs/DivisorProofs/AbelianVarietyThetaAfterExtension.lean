import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgClosedPrincipallyPolarizedHasThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDescentFiniteExtension

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.ThetaFinite

theorem exists_finite_hasTheta : ∀ (K : Type) [Field K] (P : PPAS (Sp K)), ∃ (F : Type) (_ : Field F) (_ : Algebra K F), FiniteDimensional K F ∧ ∃ (Q : PPAS (Sp F)) (ψ : Q.A.left ⟶ P.A.left), Q.IsPull P (Spec.map (CommRingCat.ofHom (algebraMap K F))) ψ ∧ Q.HasTheta := by
  intro K _ P
  obtain ⟨PΩ, ψ, -, h⟩ := PPAS.exists_pull (Sp K) (Sp (AlgebraicClosure K)) P
    (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
  exact GlobalTheory.T.theta_descent_finite_extension K P (AlgebraicClosure K) PΩ ψ h (GlobalTheory.T.algClosed_principally_polarized_hasTheta _ PΩ)

end GlobalTheory.ThetaFinite

end
