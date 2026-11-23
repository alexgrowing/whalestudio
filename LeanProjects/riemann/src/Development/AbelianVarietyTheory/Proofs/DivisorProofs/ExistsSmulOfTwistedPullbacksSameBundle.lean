import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSectionsIrreducibleThetaGroup
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsGenOfInvariant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.TwistRatio

theorem exists_smul_of_isTwistPull : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)) (m : ℕ), 1 ≤ m →
    ∀ (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))))
      (α α' : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver (Sp K)) P.A).left, (snd (baseOver (Sp K)) P.A ^ m).left]
        ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
      (s₁ s₁' : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))), α.IsGen → α'.IsGen →
    IsTwistPull P.A P.L (mulT P.A (baseOver (Sp K)) m) (snd (baseOver (Sp K)) P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ →
    IsTwistPull P.A P.L (mulT P.A (baseOver (Sp K)) m) (snd (baseOver (Sp K)) P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α' th s₁' →
    ∃ c : K, (SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁' : EA P (𝟙 (Sp K)) (m ^ 2)) = c • SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁ := by
  intro K _ _ _ P m hm th α α' s₁ s₁' hα hα' h h'
  have hG := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨a, ha⟩ := H1.exists_const P.L P.isLB (fst (baseOver (Sp K)) P.A).left
    (BoxTheta.surj_fst hG P.isAb _)
    (LB.mulGen P.L _ _ _ _ α' (LB.invGen P.L _ _ α))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hα' (DVR.invGen_isGen _ _ _ _ hα)) (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two])
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 a
  refine ⟨c, SecMod.ext_coord fun j => ?_⟩
  refine sec_ext_val P.isLB (fun y J hJ => ?_) j
  have e1 := VVRank.sv_of_isTwistPull P.A h' (𝟙 _) y hJ
  have e0 := VVRank.sv_of_isTwistPull P.A h (𝟙 _) y hJ
  have ev := ha _ (𝟙 _) y J hJ
  rw [val_mul hJ, val_inv] at ev
  have es := SecMod.value_smul hJ (𝟙 _) c (SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁)
  refine e1.trans (Eq.trans ?_ es.symm)
  have eg : gs (𝟙 _) y ⊤ (scal (fst (baseOver (Sp K)) P.A).left c) =
      gs (𝟙 _ ≫ (fst (baseOver (Sp K)) P.A).left) y ⊤
        ((ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv) c) :=
    gs_pull _ _ y ⊤ trivial _
  have eu : (val α' (𝟙 _) y J).val =
      (val α' (𝟙 _) y J * (val α (𝟙 _) y J)⁻¹).val * (val α (𝟙 _) y J).val := by
    rw [← Units.val_mul, inv_mul_cancel_right]
  change _ = _ * VVRank.sv P.A s₁ (𝟙 _) y J
  rw [e0, eg, ← ev, eu, _root_.mul_assoc]

end GlobalTheory.TwistRatio
