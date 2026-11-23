import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegRel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveQcPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOneProdKernel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BirigUniq

theorem one_comp_monHom {S : Scheme.{0}} {T A A' : Over S} [GrpObj A] [GrpObj A'] (f : A ⟶ A') [IsMonHom f] :
    (1 : T ⟶ A) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem pull_comp_left {S : Scheme.{0}} {U V W : Over S} (g : U ⟶ V) (f : V ⟶ W) (c : GlobalTheory.CechPic.Pic W.left) :
    GlobalTheory.CechPic.pull (g ≫ f).left c = GlobalTheory.CechPic.pull g.left (GlobalTheory.CechPic.pull f.left c) := by
  rw [Over.comp_left, GlobalTheory.CechPic.pull_comp]

theorem pic_eq_zero_of_fpqc {S : Scheme.{0}} (X Y Y' : Over S) [GrpObj X] (hX : IsAbelianScheme X)
    (c : Y' ⟶ Y) (hfl : Flat c.left) (hsu : Surjective c.left) (hqc : QuasiCompact c.left)
    (d : GlobalTheory.CechPic.Pic (X ⊗ Y).left)
    (h0 : GlobalTheory.CechPic.pull (lift (1 : Y ⟶ X) (𝟙 Y)).left d = 0)
    (h1 : GlobalTheory.CechPic.pull (lift (fst X Y') (snd X Y' ≫ c)).left d = 0) : d = 0 := by
  obtain ⟨D, hD, rfl⟩ := GlobalTheory.CechPic.cls_surj d
  have t := GlobalTheory.RigDesc.triv_of_triv_zero_of_fpqc S X Y Y' hX c hfl hsu hqc D hD
    ((GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hD _)).1 h0) ((GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hD _)).1 h1)
  exact (GlobalTheory.CechPic.cls_eq_zero_iff hD).2 t

end GlobalTheory.BirigUniq

namespace GlobalTheory.BirigUniq

end GlobalTheory.BirigUniq
