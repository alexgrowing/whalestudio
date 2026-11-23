import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPow8F
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.PowEightField

open GlobalTheory.EighthPowerFactor GlobalTheory.CechPic

theorem exists_eighthPower_evenUnimodular_charZero : ∃ d : ℕ, 1 ≤ d ∧ ∀ (K : Type) [Field K] [CharZero K] (P : PolAV (Sp K)), ∃ (Q : PolAV (Sp K)) (pr : Fin 8 → (Q.A ⟶ P.A)) (inc : P.A ⟶ Q.A), Q.g = 8 * P.g ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) ∧ IsPow8 P Q d pr inc := by
  obtain ⟨W, hW, hbas⟩ := ZM.exists_isE8_isSharpBasis
  have hW0 : 0 < W 0 0 := by
    have h := hW.1.diag_pos (i := 0)
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_add] at h
    have : (0 : ℝ) < (W 0 0 : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨(2 * W 0 0).toNat, by omega, ?_⟩
  intro K _ _ P
  have := P.isAb.comm
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  obtain ⟨bas, hb⟩ := hbas P.g
  obtain ⟨a, w, w', hw, hw', hs⟩ := exists_matrices hW.2
  let b : ZM.TBase K 1 := ⟨1, by simp, fun K _ β => by simp⟩
  have hc : (siegOne L₁.globalFns P.isAb P.isLB P.g).Principal :=
    ⟨relAmple_diag_lam P.isAb P.isLB (Moduli.cube_of_isLB _ P P.L P.isLB) P.ample,
      fun T x hx => SiegelOfPolarised.eq_one_of_lam P.isLB P.ktriv x hx⟩
  obtain ⟨t, ⟨pr, hpr, hu, hL, -⟩, h₁, h₂, h₃⟩ := exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB P.g _ W _ a w w'
    bas hW hb hw hw' hs 1 K b _ (𝟙 _) (siegOne L₁.globalFns P.isAb P.isLB P.g) (one_pow _) odd_one hc P.smoothDim
  obtain ⟨inc, hinc, -⟩ := hu P.A fun u => if u = 0 then 𝟙 P.A else 1
  refine ⟨t.pol, pr, inc, rfl, ⟨t.act w, t.act w', t.hom w, t.hom w', h₁, h₃, h₂⟩, hpr, ?_, hu, hinc, ?_⟩
  · refine isMonHom_of_coord hpr hu fun u => ?_
    rw [hinc u]
    by_cases h : u = 0
    · subst h; simp only [↓reduceIte]; exact inferInstanceAs (IsMonHom (𝟙 P.A))
    · simp only [h, ↓reduceIte]; exact inferInstanceAs (IsMonHom (toUnit P.A ≫ η[P.A]))
  ·
    have hP : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
    have hQ : t.pol.L.IsLB := t.pol.isLB
    have hlam : cls _ hP = lam (cls P.L P.isLB) (fst P.A P.A) (snd P.A P.A) := cls_cube_two P.isLB _ _ hP
    have hdiag := (cls_eq_iff (LB.isLB_linComb P.isLB _ _) (pull_isLB hP _)).2 (SiegelOfPolarised.lbIso_diag L₁ P)
    rw [cls_lbPow P.isLB, cls_pull hP, hlam, pull_lam, lift_fst, lift_snd] at hdiag
    have e1 := ((cls_eq_iff hQ (LB.isLB_linComb hP _ _)).2 hL).trans (cls_linComb hP _ _ _)
    refine (cls_eq_iff (pull_isLB hQ _) (LB.isLB_linComb P.isLB _ _)).1 ?_
    refine ((congrArg (pull inc.left) e1).trans ?_).trans (cls_lbPow P.isLB _ _).symm
    rw [hlam]
    erw [map_sum]
    rw [Fintype.sum_eq_single ((0 : Fin 8), (0 : Fin 8))]
    · erw [map_zsmul]
      erw [CechPic.pull_lam, CechPic.pull_lam]
      erw [lift_fst, lift_snd]
      dsimp only
      erw [hinc]
      simp only [↓reduceIte]
      rw [← hdiag, ← natCast_zsmul, ← natCast_zsmul, smul_smul, Int.toNat_of_nonneg (by omega)]
      congr 1
      push_cast
      ring
    · rintro ⟨u, v⟩ huv
      erw [map_zsmul]
      erw [CechPic.pull_lam, CechPic.pull_lam]
      erw [lift_fst, lift_snd]
      dsimp only
      have hi1 : ∀ u : Fin 8, u ≠ 0 → inc ≫ pr u = 1 := fun u h => (hinc u).trans (if_neg h)
      by_cases hu0 : u = 0
      · subst hu0
        have hv0 : v ≠ 0 := fun h => huv (by rw [h])
        erw [hi1 v hv0, lam_one_right, smul_zero]
      · erw [hi1 u hu0, lam_one_left, smul_zero]

end GlobalTheory.MBLow.PowEightField
