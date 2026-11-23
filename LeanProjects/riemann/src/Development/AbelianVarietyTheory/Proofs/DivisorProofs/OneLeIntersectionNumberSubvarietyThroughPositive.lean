import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleModuloEffectiveAwayFromPointPullAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundleOfSmulClassEqAmpleAtAddNefStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PosThrough

theorem one_le_interNumRed : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X), IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → ∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e → topologicalKrullDim (Z : Set X) = e → 1 ≤ interNumRed k Z (fun _ : Fin e => N) := by
  intro hNN k _ X q hq
  letI := algebraΓOfHom q
  intro N N₁ N₂ hN h₁ h₂ a x hNef ha hcls hamp hN₂ Z e hZ hx he hdim
  have hBig : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q →
      letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X),
      IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → IsBig k N :=
    GlobalTheory.T.isBigLineBundle_of_smul_class_eq_ampleAt_add_nef hNN
  have hAmp : ∀ (Y X : Scheme.{0}) (π : X ⟶ Y) [IsAffineHom π] (N : LB Y), N.IsLB → ∀ x : X,
      AmpleAt N (π x) → AmpleAt (N.pull π) x := GlobalTheory.T.ampleModuloEffectiveAwayFromPoint_pull_affine
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ
  set q' := redι Z ≫ q with hq'
  letI := algebraΓOfHom q'
  have hi : ∀ r : k, (redι Z).appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r :=
    fun r => rfl
  have hpq : IsProjOver q' := by
    obtain ⟨n, f, hf, hs⟩ := hq
    exact ⟨n, redι Z ≫ f, inferInstance, by rw [Category.assoc, hs]⟩
  obtain ⟨w, rfl⟩ : x ∈ Set.range (redι Z) := by rw [range_redι]; exact hx
  have hb := hBig k _ q' hpq (N.pull (redι Z)) (N₁.pull (redι Z)) (N₂.pull (redι Z))
    (LB.isLB_pull hN _) (LB.isLB_pull h₁ _) (LB.isLB_pull h₂ _) a w
    (hNef.pull_of_isClosedImmersion _ hi) ha
    (by rw [cls_pull hN, cls_pull h₁, cls_pull h₂, ← map_nsmul, hcls, map_add])
    (hAmp _ _ _ N₁ h₁ w hamp) (hN₂.pull_of_isClosedImmersion _ hi)
  have hstr : strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = q' :=
    strHom_eq (f := q') fun _ => rfl
  have hD : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = e :=
    (topologicalKrullDim_red Z).trans hdim
  have hpos := ((hNN.2.2.isBig_iff (hstr ▸ hpq) hD (hNef.pull_of_isClosedImmersion _ hi)).1 hb)
  have heq : interNumRed k Z (fun _ : Fin e => N) = topSelfIntersection k (N.pull (redι Z)) e :=
    interNumOn_const_eq_topSelf hi hN e
  omega

end GlobalTheory.PosThrough
