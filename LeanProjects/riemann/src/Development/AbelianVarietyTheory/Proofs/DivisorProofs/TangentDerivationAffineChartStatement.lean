import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivationAffineChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_derivation_affine_chart : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (δ : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (δ r))) → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (g : ℕ), IsGrpPullback A Xo.univ.t.G P.x π ∧ IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' ∧ i ≫ π' = π ∧ GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧ (∀ σ k, (ub σ k).left ≫ π = P.u σ k) ∧ (∀ σ k, GlobalTheory.DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧ (∀ (τ : GlobalTheory.FlagTan.psiSet H) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w) ∧ IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ (Xo.univ.t.PP.L.pull π).IsLB := by
  first | exact @GlobalTheory.KSPkg.ksPackage | exact GlobalTheory.KSPkg.ksPackage | (intros; apply GlobalTheory.KSPkg.ksPackage <;> assumption)
