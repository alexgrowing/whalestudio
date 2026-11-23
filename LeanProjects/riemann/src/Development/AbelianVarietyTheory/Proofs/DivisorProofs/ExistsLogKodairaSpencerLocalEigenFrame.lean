import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPairDForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadEigenFrameLieAlgebraToroidalComponenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKSSymPairBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldExtendFunctionFieldDerivatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldTopFormPairingRegularAtPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

theorem exists_genKS_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed Xo c → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ → ∃ D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z, GlobalTheory.LogKSDiv.GenKS TF Z (fun τ k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) D ∧ ∀ (U : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U), TopForm.IsFrame ω → ∀ hx : x ∈ U, RegAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U (gen_mem hx) ω)) ∧ (UnitAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U (gen_mem hx) ω)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ _ _ x φ f hφ
  obtain ⟨U, hU, hxU, ρ, n, e, v, φU, hρ, htan, hbas, heig, hw⟩ := GlobalTheory.T.exists_spread_eigenFrame_lieAlgebra_toroidalComponent E H Dw l Xo c TF Z x φ f hφ
  obtain ⟨ε, b, hKS⟩ := GlobalTheory.T.exists_logKS_symPair_basis_alt E H Dw l Xo c TF U n e v φU htan hbas heig
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_logVectorField_extend_functionFieldDerivation E H Dw l Xo c TF Z U hU ρ hρ (fun j => b j)
  exact ⟨D, ⟨U, hU, ρ, n, e, v, ε, fun j => b j, hρ, htan, hbas, fun τ i => hw τ i, hKS, hD⟩,
    fun U' ω hω hx => GlobalTheory.T.exists_logVectorField_topForm_pairing_regular_at_point E H Dw l Xo c TF Z x U hU hxU ρ hρ b D hD U' ω hω hx⟩

end GlobalTheory.LogKSDiv
