import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleD

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.Z2

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem relAmple_of_two_smul {G : Over (Sp Ω)} [GrpObj G] (hG : IsAbelianScheme G) {M N : LB G.left}
    (hM : M.IsLB) (hN : N.IsLB) (d : ℕ) (hd : 1 ≤ d) (e : d • cls M hM = d • cls N hN) (h : Out.RelAmple G N) :
    Out.RelAmple G M := by
  haveI : IsProper G.hom := hG.proper
  have hK := GlobalTheory.isLB_lbPow hN d
  have hcls : d • cls M hM = cls (lbPow N d) hK := by
    rw [cls_lbPow hN d hK, e]
  refine GlobalTheory.PosDefAmple.relAmple_of_nsmul hM hK hd hcls ?_
  refine GlobalTheory.relAmple_of_isAmpleLB G hK fun U hU => ?_
  have hNU := GlobalTheory.isAmpleLB_of_relAmple G hN h U hU
  have hpk : ∀ k : ℕ, ((lbPow N k).pull (G.hom ⁻¹ᵁ U).ι).IsLB :=
    fun k => pull_isLB (GlobalTheory.isLB_lbPow hN k) _
  have hN1 : (N.pull (G.hom ⁻¹ᵁ U).ι).IsLB := pull_isLB hN _
  have hc : ∀ k : ℕ, cls _ (hpk k) = k • cls _ hN1 := fun k => by
    rw [cls_pull (GlobalTheory.isLB_lbPow hN k), cls_lbPow hN k, map_nsmul, cls_pull hN]
  have key : ∀ k : ℕ, 1 ≤ k → GlobalTheory.IsAmpleLB ((lbPow N k).pull (G.hom ⁻¹ᵁ U).ι) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      exact GlobalTheory.IsAmpleLB.of_lbIso hNU (hpk 1) ((cls_eq_iff (hpk 1) hN1).1 (by rw [hc, one_smul]))
    | succ k hk ih =>
      refine GlobalTheory.IsAmpleLB.tensor ih hNU (hpk (k + 1)) ?_
      have h1 := LB.isLB_div (hpk (k + 1)) (hpk k)
      have h2 := LB.isLB_div h1 hN1
      refine (cls_eq_zero_iff h2).1 ?_
      rw [cls_div h1 hN1, cls_div (hpk (k + 1)) (hpk k), hc, hc, succ_nsmul]
      abel
  exact key d hd

end PositivityTheory.PrwZar.Z2
