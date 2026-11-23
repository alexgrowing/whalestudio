import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKaehlerBasisDifferentialsOfTopFormFrame
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameEtale

theorem etale_eval₂Hom_of_basis {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) (hα : α.Smooth)
    {n : ℕ} (z : Fin n → A) (b : Module.Basis (Fin n) A (Omega α)) (hb : ∀ i, b i = dFun α (z i)) :
    (MvPolynomial.eval₂Hom α z).Etale := by
  letI := α.toAlgebra
  haveI : Algebra.Smooth k A := hα
  letI := (MvPolynomial.eval₂Hom α z).toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.eval₂Hom_C α z r).symm
  have hX (i) : algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i) = z i :=
    MvPolynomial.eval₂Hom_X' α z i
  exact EtaleCoordJacobian.etale_of_basis k A (Fin n) b fun i => by rw [hX]; exact hb i

theorem isEtCoord_of_isFrame : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (V : Y.Opens) (z : Fin n → Γ(Y, V)), IsFrame (dOn q z) → IsAffineOpen V ∧ IsEtCoord q V z := by
  intro k _ Y q n hq V z hz
  refine ⟨hz.affine, ?_⟩
  obtain ⟨b, hb⟩ := FrameBasis.exists_basis_of_isFrame k Y q n hq V z hz
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  have h := HasRingHomProperty.appLE (@Smooth) q inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hz.affine⟩ le_top
  have h₁ : (DVR.FlatBC.algX q V).Smooth :=
    RingHom.Smooth.respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv h
  exact etale_eval₂Hom_of_basis (DVR.FlatBC.algX q V) h₁ z b hb

end GlobalTheory.FrameEtale
