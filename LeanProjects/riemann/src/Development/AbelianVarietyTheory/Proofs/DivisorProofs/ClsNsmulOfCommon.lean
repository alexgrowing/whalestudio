import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
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

namespace GlobalTheory.HSApp.AmpleTwist

theorem cls_nsmul_of_common {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ)
    (a : Λ) : cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) := by
  induction n with
  | zero =>
    have h := cls_common_add C 0 0
    simp only [add_zero] at h
    simp only [zero_nsmul]
    exact left_eq_add.1 h
  | succ n ih => rw [succ_nsmul, cls_common_add C, ih, succ_nsmul]

theorem ampleAt_of_sec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (A : LB TF.Y.X), A.IsLB → ∀ (ρ χ : AllWt.Weight Dw) (n m : ℕ), IsAmpleLB (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)) → ∀ (y : Y₀ TF.X Z) (s : (LB.div (lbPow (L₀ TF.X Z χ) m) ((lbPow A n).pull (inc₀ TF.X Z ≫ TF.X.π))).Sec), y ∈ nonzeroLocus s → AmpleAt (L₀ TF.X Z (m • χ - ρ)) y := by
  intro E _ _ _ H Dw l Xo c TF Z A hA ρ χ n m hamp y s hs
  have hAg : (A.pull (inc₀ TF.X Z ≫ TF.X.π)).IsLB := pull_isLB hA _
  have hP : (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n).IsLB := isLB_lbPow hAg n
  have hρ := isLB_L₀ TF.X Z ρ
  have hB : (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)).IsLB := hamp.isLB
  have hN := isLB_L₀ TF.X Z (m • χ - ρ)
  have hN1 := isLB_lbPow hN 1
  have hD := LB.isLB_div hN1 hB
  have hχ := isLB_L₀ TF.X Z χ
  have hχm := isLB_lbPow hχ m
  have hAn := isLB_lbPow hA n
  have hAng : ((lbPow A n).pull (inc₀ TF.X Z ≫ TF.X.π)).IsLB := pull_isLB hAn _
  have hT := LB.isLB_div hχm hAng
  have hiso : LBIso (LB.div (lbPow (L₀ TF.X Z (m • χ - ρ)) 1)
      (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)))
      (LB.div (lbPow (L₀ TF.X Z χ) m) ((lbPow A n).pull (inc₀ TF.X Z ≫ TF.X.π))) := by
    refine (cls_eq_iff hD hT).1 ?_
    have e := cls_common_add (common₀ TF.X Z) (m • χ - ρ) ρ
    rw [sub_add_cancel] at e
    have e2 := cls_nsmul_of_common (common₀ TF.X Z) m χ
    rw [cls_div hN1 hB hD, cls_div hP hρ hB, cls_lbPow hN 1 hN1, cls_lbPow hAg n hP, cls_pull hA _ hAg,
      cls_div hχm hAng hT, cls_pull hAn _ hAng, cls_lbPow hA n hAn, cls_lbPow hχ m hχm, map_nsmul]
    have e3 : cls (L₀ TF.X Z (m • χ - ρ)) hN = m • cls (L₀ TF.X Z χ) hχ - cls (L₀ TF.X Z ρ) hρ := by
      rw [← e2, e, add_sub_cancel_right]
    rw [e3]
    abel
  obtain ⟨s', hs'⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hD hT hiso s
  refine ⟨1, LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ), s', one_pos, hB, hamp, ?_⟩
  rw [hs']
  exact hs

end GlobalTheory.HSApp.AmpleTwist
