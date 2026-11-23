import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCombinationTangentVectorsAffineOpen
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartPtChartPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfField
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearCombination_tangentVectors_affineOpen : ∀ {K B : Type} [CommRing K] [CommRing B] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (Y₀ : Y.affineOpens) (φ : K →+* B) (x : Sp B ⟶ Y) (hx : x ≫ p = spMap φ) (hxY : ⊤ ≤ x ⁻¹ᵁ Y₀.1) {n : ℕ} (w : Fin n → (Sp (DualNumber B) ⟶ Y)) (hwp : ∀ a, w a ≫ p = spMap ((algebraMap B (DualNumber B)).comp φ)) (hwx : ∀ a, spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w a = x) (c : Fin n → B), ∃ S : Sp (DualNumber B) ⟶ Y, S ≫ p = spMap ((algebraMap B (DualNumber B)).comp φ) ∧ spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ S = x ∧ ∀ O : Y.Opens, ⊤ ≤ x ⁻¹ᵁ O → ∀ f : Γ(Y, O), (valR S O f).snd = ∑ a, c a * (valR (w a) O f).snd := by
  first | exact @GlobalTheory.CechKS.LinTan.exists_linComb | exact GlobalTheory.CechKS.LinTan.exists_linComb | (intros; apply GlobalTheory.CechKS.LinTan.exists_linComb <;> assumption)
