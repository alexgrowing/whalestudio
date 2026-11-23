import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymAmple

open GlobalTheory.CechPic

theorem exists_isAmpleLB_symm (S : Scheme.{0}) (G : Over S) [GrpObj G] (M₀ : LB G.left) (h₀ : IsAmpleLB M₀) :
    ∃ M : LB G.left, IsAmpleLB M ∧ LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M := by
  set i : G.left ⟶ G.left := (GrpObj.inv : G ⟶ G).left with hi_def
  have hii : i ≫ i = 𝟙 G.left := by
    rw [hi_def, ← Over.comp_left, GrpObj.inv_comp_inv G, Over.id_left]
  have : IsIso i := ⟨⟨i, hii, hii⟩⟩
  have hL := h₀.isLB
  have h₁ : IsAmpleLB (M₀.pull i) := h₀.pull_of_isAffineHom i
  let M : LB G.left := LB.LinComb M₀ (K := Fin 2) ![𝟙 G.left, i] ![1, 1]
  have hM : M.IsLB := LB.isLB_linComb hL _ _
  have hc : cls M hM = cls M₀ hL + pull i (cls M₀ hL) := by
    rw [cls_linComb hL]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_zsmul, pull_id]
  refine ⟨M, h₀.tensor h₁ hM ?_, ?_⟩
  · have hd₁ := LB.isLB_div hM hL
    have hd₂ := LB.isLB_div hd₁ (pull_isLB hL i)
    refine (cls_eq_zero_iff hd₂).1 ?_
    rw [cls_div hd₁ (pull_isLB hL i), cls_div hM hL, hc, cls_pull hL]
    abel
  · refine (cls_eq_iff (pull_isLB hM i) hM).1 ?_
    rw [cls_pull hM, hc, map_add, ← pull_comp, hii, pull_id]
    exact add_comm _ _

end GlobalTheory.SymAmple
