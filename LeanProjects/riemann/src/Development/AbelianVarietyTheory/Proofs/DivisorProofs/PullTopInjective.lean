import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentPullChart
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullBig

open GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 Filter

theorem map_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (σ : X ⟶ Y)
    (hσ : DenseRange σ) : σ (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image σ.continuous
  rw [Set.image_univ, hσ.closure_range] at h
  exact h.eq (genericPoint_spec Y)

theorem pull_top_injective {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {p : Y ⟶ Sp k} (σ : X ⟶ Y) (hσ : DenseRange σ) (B : LB Y) :
    Function.Injective (H0.pull (p := p) (B := B) (O := ⊤) σ (W := ⊤) le_top) := by
  have hη := map_genericPoint σ hσ
  have hF : IsField (Y.presheaf.stalk (σ (genericPoint X))) := by
    rw [hη]; exact Field.toIsField Y.functionField
  refine (injective_iff_map_eq_zero _).2 fun f hf => LB.sec_ext fun i => fun_ext_ger fun y hy => ?_
  have hηi : genericPoint Y ∈ B.U i :=
    ((genericPoint_spec Y).mem_open_set_iff (B.U i).isOpen).2 ⟨y, Set.mem_univ _, hy.2⟩
  have hxi : σ (genericPoint X) ∈ B.U i := hη ▸ hηi
  have h0 : germ (p := p) (O := ⊤) i (σ (genericPoint X)) trivial hxi f = 0 := by
    have e := congrArg (germ (p := σ ≫ p) (B := B.pull σ) (O := ⊤) (fun _ => i) (genericPoint X) trivial (mem_pull.2 hxi)) hf
    have e' := (germ_pull (p := p) (B := B) (O := ⊤) σ (W := ⊤) le_top (fun _ => i) (genericPoint X) trivial
      (mem_pull.2 hxi) f).symm.trans (e.trans (map_zero _))
    by_contra hne
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hne
    have := congrArg (σ.stalkMap (genericPoint X)).hom hb
    rw [map_mul, e', zero_mul, map_one] at this
    exact zero_ne_one this
  have hloc : f.loc i = 0 :=
    germ_injective_of_isIntegral Y (U := ⊤ ⊓ B.U i) (σ (genericPoint X)) ⟨trivial, hxi⟩
      (h0.trans (map_zero _).symm)
  exact congrArg _ hloc

theorem isBig_pull : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ Sp k) (σ : X ⟶ Y), IsProjOver p → IsProjOver (σ ≫ p) →
    topologicalKrullDim X = topologicalKrullDim Y → DenseRange σ → ∀ L : LB Y,
    (letI := algebraΓOfHom p; IsBig k L) → (letI := algebraΓOfHom (σ ≫ p); IsBig k (L.pull σ)) := by
  intro k _ X Y _ _ p σ hp hq hdim hσ L hL
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (σ ≫ p)
  obtain ⟨D, hD, c, hc, hm⟩ := hL.growth
  have hL' := LB.isLB_pull hL.isLB σ
  have key (m : ℕ) : lbH0 k (lbPow L m) ≤ lbH0 k (lbPow (L.pull σ) m) := by
    have hLm := isLB_lbPow hL.isLB m
    have hP := LB.isLB_pull hLm σ
    haveI := finite_top hq hP
    calc lbH0 k (lbPow L m) = Module.finrank k (H0 p (lbPow L m) ⊤) := (H0.finrank_top p _).symm
      _ ≤ Module.finrank k (H0 (σ ≫ p) ((lbPow L m).pull σ) ⊤) :=
        LinearMap.finrank_le_finrank_of_injective (pull_top_injective σ hσ _)
      _ = lbH0 k ((lbPow L m).pull σ) := H0.finrank_top _ _
      _ = lbH0 k (lbPow (L.pull σ) m) := lineBundleGlobalSectionsDim_congr_picardClass hP (isLB_lbPow hL' m) (by
        rw [cls_pull hLm, cls_lbPow hL.isLB, cls_lbPow hL', cls_pull hL.isLB, map_nsmul])
  refine (isBig_iff (fun _ => rfl) hq (hdim.trans hD)).2 ⟨hL', c, hc, hm.mono fun m hm' => ?_⟩
  exact hm'.trans (by exact_mod_cast key m)

end GlobalTheory.PullBig
