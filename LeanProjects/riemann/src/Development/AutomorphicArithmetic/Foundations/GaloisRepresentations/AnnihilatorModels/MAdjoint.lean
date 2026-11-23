import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.adjoint_of :
    PairCalc → TorsFree → Adjoint := by
  intro hPC hTF p _ D R _ b N k _ s c o o' ψ ψ' hψ hψ' hc T x y
  have hpos : 0 < c := hψ.pos
  obtain ⟨a₁, a₂, -, -, hsim⟩ := hPC p D R b N _ s o
  obtain ⟨a₁', a₂', -, -, -⟩ := hPC p D R b N _ s o'
  obtain ⟨-, hmon, -, -, hiso, -⟩ := hψ
  have hsim' := (hsim o' ψ c).1 hiso
  haveI := hmon
  haveI := hψ'

  have hsym : ∀ (q : Obj b N s) {Y : Over (Sp k)} (u v : Y ⟶ q.A),
      evc q.isLB u v = evc q.isLB v u := by
    intro q Y u v
    have h1 := (GlobalTheory.CechPic.cls_eq_iff q.isLB (pull_isLB q.isLB _)).2 q.symm
    have h2 := congrArg (GlobalTheory.CechPic.pull (lift u v).left) h1
    rw [GlobalTheory.AbDual.cls_ev q.isLB, GlobalTheory.AbDual.pull_evc, lift_snd, lift_fst] at h2
    exact h2

  have hL1 := pull_isLB o'.isLB (lift (fst o.A o'.A ≫ ψ) (snd o.A o'.A)).left
  have hL2 := pull_isLB o.isLB (lift (fst o.A o'.A) (snd o.A o'.A ≫ ψ')).left
  have hL := LB.isLB_div hL1 hL2
  have cL := GlobalTheory.CechPic.cls_div hL1 hL2 hL
  have hev : ∀ {Y : Over (Sp k)} (u : Y ⟶ o.A) (v : Y ⟶ o'.A),
      evc hL u v = evc o'.isLB (u ≫ ψ) v - evc o.isLB u (v ≫ ψ') := by
    intro Y u v
    rw [GlobalTheory.AbDual.evc, cL, map_sub, GlobalTheory.AbDual.cls_ev o'.isLB, GlobalTheory.AbDual.cls_ev o.isLB,
      GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, lift_fst_assoc, lift_snd, lift_fst, lift_snd_assoc]
  have add₁ := (GlobalTheory.AbDual.isAdditive_iff o.isLB).1 a₁
  have add₁' := (GlobalTheory.AbDual.isAdditive_iff o'.isLB).1 a₁'
  have add₂ := (GlobalTheory.BirigidLift.isAdditive_swap_iff o.isLB).1 a₂
  have add₂' := (GlobalTheory.BirigidLift.isAdditive_swap_iff o'.isLB).1 a₂'
  have bL₁ : IsAdditive (A := o.A) (T := o'.A) _ := (GlobalTheory.AbDual.isAdditive_iff hL).2 fun Y u u' v ↦ by
    rw [hev, hev, hev, MonObj.mul_comp, add₁', add₁]
    abel
  have bL₂ : IsAdditive (swap _) := (GlobalTheory.BirigidLift.isAdditive_swap_iff hL).2 fun Y u v v' ↦ by
    rw [hev, hev, hev, MonObj.mul_comp, add₂', add₂]
    abel

  have hpow : ∀ {Y : Over (Sp k)} (u : Y ⟶ o'.A) (v : Y ⟶ o'.A) (n : ℕ),
      evc o'.isLB u (v ^ n) = n • evc o'.isLB u v := by
    intro Y u v n
    induction n with
    | zero =>
      have e := add₂' Y u 1 1
      rw [_root_.mul_one] at e
      rw [pow_zero, zero_smul]
      exact left_eq_add.1 e
    | succ n ih => rw [pow_succ, add₂', ih, succ_nsmul]
  have hcm : ∀ {Y : Over (Sp k)} (u : Y ⟶ o.A) (v : Y ⟶ o'.A),
      c • evc o'.isLB (u ≫ ψ) v = c • evc o.isLB u (v ≫ ψ') := by
    intro Y u v
    rw [← hsim' Y u (v ≫ ψ'), ← hpow, Category.assoc, hc, MonObj.comp_pow, Category.comp_id]
  have hcls : GlobalTheory.CechPic.cls _ hL = evc hL (fst o.A o'.A) (snd o.A o'.A) := by
    rw [GlobalTheory.AbDual.evc, lift_fst_snd, Over.id_left, GlobalTheory.CechPic.pull_id]
  have hz : GlobalTheory.CechPic.cls _ hL = 0 := hTF k o.A o'.A o.ab o'.ab _ hL bL₁ bL₂ c hpos (by
    rw [hcls, hev, smul_sub, hcm, sub_self])
  have hmain : ∀ {Y : Over (Sp k)} (u : Y ⟶ o.A) (v : Y ⟶ o'.A),
      evc o'.isLB (u ≫ ψ) v = evc o.isLB u (v ≫ ψ') := by
    intro Y u v
    rw [← sub_eq_zero, ← hev, GlobalTheory.AbDual.evc, hz, map_zero]
  exact ⟨hmain x y, by rw [hsym o', hmain, hsym o]⟩
