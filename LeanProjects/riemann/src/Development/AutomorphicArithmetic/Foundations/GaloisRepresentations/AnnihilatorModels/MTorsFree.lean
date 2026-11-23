import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.torsFree_of :
    DivC → TorsFree := by
  intro h k _ A B _ _ _ _ hA hB L hL hadd hadd' c hc hcls
  obtain ⟨D, instD, Q, hD, -, hQ, hQ'⟩ := GlobalTheory.dualAbelianScheme _ A hA
  have hcomm : IsCommMonObj D := hD.comm
  obtain ⟨x, hx, hx'⟩ := GlobalTheory.BirigidLift.exists_hom hQ hQ'.additive hL hadd hadd'
  have hone : IsMonHom (1 : B ⟶ D) := inferInstance
  have hev : ∀ (Y : Over (Sp k)) (a : Y ⟶ A) (b b' : Y ⟶ D),
      evc hQ.isLB a (b * b') = evc hQ.isLB a b + evc hQ.isLB a b' :=
    (GlobalTheory.BirigidLift.isAdditive_swap_iff hQ.isLB).1 hQ'.additive
  have hpow : ∀ (n : ℕ) (b : B ⟶ D), evc hQ.isLB (fst A B) (snd A B ≫ b ^ n) =
      n • evc hQ.isLB (fst A B) (snd A B ≫ b) := by
    intro n b
    induction n with
    | zero => rw [pow_zero, MonObj.comp_one, zero_smul, GlobalTheory.AbDual.evc_one_right hQ.isLB hQ.zero]
    | succ n ih => rw [pow_succ, MonObj.comp_mul, hev, ih, succ_nsmul]
  have h1 : evc hQ.isLB (fst A B) (snd A B ≫ x ^ c) =
      evc hQ.isLB (fst A B) (snd A B ≫ (1 : B ⟶ D)) := by
    rw [hpow, ← hx', hcls, MonObj.comp_one, GlobalTheory.AbDual.evc_one_right hQ.isLB hQ.zero]
  have h2 : x ^ c = 1 := GlobalTheory.BirigidLift.dual_ext hQ h1
  have h3 : x = 1 := (h (Sp k) B D hB c hc).2 x 1 hx hone (by rw [h2, one_pow])
  rw [hx', h3, MonObj.comp_one, GlobalTheory.AbDual.evc_one_right hQ.isLB hQ.zero]
