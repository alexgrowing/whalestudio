import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
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

namespace GlobalTheory

theorem isBig_of_smul_cls_eq_add_ampleAt : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X), IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → IsBig k N := by
  intro hnum k _ X _ q hq
  letI := algebraΓOfHom q
  intro N N₁ N₂ hN h₁ h₂ a x _ ha e hx hn₂
  have hf : ∀ r, algebraMap k Γ(X, ⊤) r = q.appTop ((Scheme.ΓSpecIso (.of k)).inv r) :=
    algebraΓOfHom_algebraMap q
  have hp : IsProjOver (strHom k X) := (strHom_eq hf) ▸ hq
  obtain ⟨m, A, s, hm, hA, hAmp, hxs⟩ := hx
  have hD := Semi.LB.isLB_div (isLB_lbPow h₁ m) hA
  have hsec : HasNonzeroSec (LB.div (lbPow N₁ m) A) := ⟨s, sec_ne_zero_of_mem hxs⟩
  have hB : IsBig k (tens (lbPow N₂ m) A) := (hn₂.pow hAmp m).isBig_tens_ample hnum hp hAmp
  have hP := isLB_lbPow hN (a * m)
  have e₂ : (a * m) • cls N hN = m • (cls N₁ h₁ + cls N₂ h₂) := by
    rw [← e, smul_smul, mul_comm a m]
  have hbig : IsBig k (lbPow N (a * m)) := hB.of_cls_eq_add hf hq hD hsec hP (by
    rw [cls_tens (isLB_lbPow h₂ m) hA, cls_div (isLB_lbPow h₁ m) hA hD, cls_lbPow hN, cls_lbPow h₂,
      cls_lbPow h₁, e₂]
    module)
  exact hbig.of_pow hN (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero ha.ne' hm.ne'))
    fun n => finite_coh_zero_twist_of_isProjOver hf hq (isLB_lbPow hN n)

end GlobalTheory
