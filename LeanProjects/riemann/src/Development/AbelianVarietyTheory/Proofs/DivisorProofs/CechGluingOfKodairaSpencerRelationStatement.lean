import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
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
theorem _root_.GlobalTheory.T.cechGluing_of_kodairaSpencer_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), (∀ a, IsTanAtG t (LogKS.chart U) (v a)) → LogKS.IsKS t V U v D Θ → ∀ (K : Type) [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1), ⊤ ≤ x0 ⁻¹ᵁ V → ∀ (y1 : Sp (DualNumber K) ⟶ X) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1), (∀ r, ev y1 U.1 hU' r = TrivSqZeroExt.inl (ev x0 U.1 hU r) + TrivSqZeroExt.inr (ev x0 U.1 hU (D r))) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ι : A.left ⟶ t.G.left) (ι' : A'.left ⟶ t.G.left) (i : A.left ⟶ A'.left) (u : Fin n → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A t.G x0 ι → IsGrpPullback A' t.G y1 ι' → i ≫ ι' = ι → (∀ a, (u a).left ≫ ι = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) → ∀ (M : LB A.left), ⨆ k, M.U k = ⊤ → LBIso (t.PP.L.pull ι) M → GlobalTheory.CechKS.IsCechKS A A' i M u (Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) := by
  first | exact @GlobalTheory.CechKS.isCechKS_of_isKS | exact GlobalTheory.CechKS.isCechKS_of_isKS | (intros; apply GlobalTheory.CechKS.isCechKS_of_isKS <;> assumption)
