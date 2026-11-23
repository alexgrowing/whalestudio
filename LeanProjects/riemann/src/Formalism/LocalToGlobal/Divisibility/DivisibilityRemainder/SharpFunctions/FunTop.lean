import Formalism.LocalToGlobal.TieTwRecOf
import Formalism.SharpRestriction.Divisibility.HookProducts.HhOfInputs
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.SharpFunctions.MidExp
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.SharpFunctions.PointB

noncomputable section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.Pk Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S

namespace Formalism.L2.DIV.FunSharpTop

theorem pow_absorb (x B l CH : ℝ) (hx : 56 ≤ x) (hB : 1 ≤ B) (hl : l ≤ 4 * B) :
    x ^ CH * B + 14 * l ≤ x ^ (max CH 1 + 1) * B := by
  have hx1 : 1 ≤ x := by linarith
  have hM : x ^ CH ≤ x ^ (max CH 1) := Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)
  have hM1 : x ≤ x ^ (max CH 1) := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ (max CH 1) := Real.rpow_le_rpow_of_exponent_le hx1 (le_max_right _ _)
  have hsplit : x ^ (max CH 1 + 1) = x ^ (max CH 1) * x := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  rw [hsplit]
  have hB0 : 0 ≤ B := by linarith
  have hPx : x ^ CH + 56 ≤ x ^ (max CH 1) * x := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x ^ (max CH 1)) (by linarith : (0 : ℝ) ≤ x - 56)]
  have h2 := mul_le_mul_of_nonneg_right hPx hB0
  nlinarith

theorem third_of (d Q : ℝ) (h0 : 0 ≤ d) (h1 : 3 * d * Q ≤ 1) (h2 : 1 ≤ Q) : d ≤ 1 / 3 := by nlinarith

variable {𝒜 : FamClass} {sel : Formalism.L2.TSel 𝒜} {selS : SelS 𝒜 sel} {selP : BaseLevelCompatibleSelection 𝒜 sel} {selDH : SelDH 𝒜 sel}
  {selC : ColumnCompatibleSelection 𝒜 sel selP} {selK : SelK 𝒜 sel}

theorem funSharp_fam [∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (i : Fm.Ix x), IsTotallyComplex (Fm.D x i).what₂.LL]
    (selI : IndefiniteRealisationChoice 𝒜 sel selS selP selDH selC selK) (hPA : PrimAll sel selI)
    (DefRows4 : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) (C CH : ℝ), Prop)
    (OneMapRow : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop)
    (hR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      DivRows3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (selP Fm hc x hx h i).1.Zs (selP Fm hc x hx h i).1.S0 (selP Fm hc x hx h i).1.S1 (Fm.ex x hx i).p0 (selP Fm hc x hx h i).1.C (selP Fm hc x hx h i).1.NuC (selP Fm hc x hx h i).1.I)
    {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (CH : ℝ) (hCsz : 0 ≤ Fm.Csz) (hDG : Formalism.MainNotions.DGamSize Fm)
    (hRows : RowsAtSel sel selI DefRows4 OneMapRow Fm hc CH) (hOne : EvSel sel Fm hc (OneMapRow Fm hc)) (hN : DIVinN Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ (max CH 1 + 1) * (Fm.L x i).sc.b := by
  obtain ⟨Cd, x4, hFDG⟩ := hDG
  obtain ⟨C, hC, x1, hr⟩ := hRows
  obtain ⟨x2, ho⟩ := hOne
  refine ⟨max (max (max x1 x2) (max x4 (x0F eps Fm.Ct Fm.Cc CH (ceF C 0 (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct)))))
    (max (sel Fm hc).1 56), fun x hx0 hx i => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx0
  have hx2 : x2 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx0
  have hx4 : x4 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx0
  have hx5 : x0F eps Fm.Ct Fm.Cc CH (ceF C 0 (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct)) ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx0
  have h : (sel Fm hc).1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx0
  have g56 : (56 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx0
  obtain ⟨ra, -⟩ := hr x hx h hx1 i
  obtain ⟨prows, hsep⟩ := hPA Fm hc x hx h i
  have hok1 := (selC Fm hc x hx h i).ok1
  have hP : CovolumeOntoIsometryConditions (selI Fm hc x hx h i).Rl (selI Fm hc x hx h i).F (selI Fm hc x hx h i).sEE (hkCan (selP Fm hc x hx h i).1.A3) C CH :=
    { toPrimRows3 := prows, w1 := ra.w1, covol := ra.covol, onto := ra.onto hN, lamLow := ra.lamLow (ho x hx h hx2 i),
      seeIso := ra.seeIso, miStar := ra.miStar, fun0 := ra.fun0 hN }
  have hS := Fm.sizes x hx i
  have hFD : FactDGam (Fm.D x i) (max Cd 0) := J.factDGam_mono (hFDG x hx4 i) (le_max_left _ _)
  have hDGp := Cons.gamma_size_of_sizeData (selP Fm hc x hx h i).2 (Formalism.L2.Top4Wire2.finiteT_of (selC Fm hc x hx h i))
    hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hS.2.2.2.2.2.1 (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2 (Fm.L x i).Nc (cloudConstant_nonneg (Fm.L x i))
    (max Cd 0) (le_max_right _ _) hFD
  have eCc : (Fm.L x i).Cc = Fm.Cc := Fm.Cc_eq x i
  have eCt : (Fm.L x i).Ct = Fm.Ct := Fm.Ct_eq x i
  have eCY : (Fm.params x hx i).CYL = Fm.CYL := Fm.params_CYL x hx i
  have hxL : x0F (Fm.L x i).sc.eps (Fm.L x i).Ct (Fm.L x i).Cc CH
      (ceF C 0 (2 + 9 * max Cd 0) (c0F Fm.Csz (Fm.L x i).Cc (Fm.params x hx i).CYL (Fm.L x i).Ct)) ≤ (Fm.L x i).sc.x := by
    rw [Fm.L_eps x i, eCt, eCc, eCY, Fm.L_x x i hx]
    exact hx5
  obtain ⟨lam0', Sw, C1, H, dg, hdg, hdvd, hA⟩ := arithClause_rec (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2 hS (selDH Fm hc x hx h i).2.1 (selDH Fm hc x hx h i).2.2 (Fm.params x hx i) (Fm.ex x hx i).fdef
    (Fm.ex x hx i).kap_def (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.tied.div.grp.card (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp _ C CH Fm.Csz 0
    (2 + 9 * max Cd 0) (Formalism.L2.Top4Wire2.finiteT_of (selC Fm hc x hx h i)) hDGp hC hCsz hxL (pkOf (selI Fm hc x hx h i) hok1 hsep C CH hP ra.pass)
  obtain ⟨Qq, hq0, hq1, hq2, -⟩ := (hA (Fm.D x i).u₀).q
  have key := funSharp_pt (selI Fm hc x hx h i) hok1 hsep C CH hP ra.pass (hR Fm hc x hx h i) ra.kap hq0
    (third_of _ _ hq0 hq1 hq2)
  have hla : Formalism.BasicNotions.lam0 (Fm.D x i) = Real.log (Fintype.card (selP Fm hc x hx h i).1.Gp) := by
    unfold Formalism.BasicNotions.lam0
    rw [(selP Fm hc x hx h i).1.tied.div.grp.card]
  have key' : (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
      (Fm.L x i).sc.x ^ CH * (Fm.L x i).sc.b + 14 * Formalism.BasicNotions.lam0 (Fm.D x i) := by
    rw [hla]
    exact key
  have hB1 : 1 ≤ (Fm.L x i).sc.b := by
    unfold Scale.b
    exact Real.one_le_exp (by unfold Scale.L; exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  refine key'.trans (pow_absorb _ _ _ CH ?_ hB1 (Formalism.MainNotions.DIV.HookProducts.FunSharp.lambda_zero_le_four_b (Fm.L x i) hS))
  rw [Fm.L_x x i hx]
  exact g56

theorem closed_funSharp (𝒜 : FamClass)
    (sel : Formalism.L2.TSel 𝒜)
    (selS : SelS 𝒜 sel)
    (selP : BaseLevelCompatibleSelection 𝒜 sel)
    (selDH : SelDH 𝒜 sel)
    (selC : ColumnCompatibleSelection 𝒜 sel selP)
    (selB : SelB 𝒜 sel selS selP selDH selC)
    (hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.IndefR.RowsB (selB Fm hc x hx h i))
    (hPA : PrimAll sel (selIOf selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, RowsAtSel sel (selIOf selB) (fun Fm hc x hx h i C CH => Formalism.L2.Top4Wire2.DefRowsF (selIOf selB) Fm hc x hx h i C CH) (OneMapOf selB)
        Fm (d3_a hc) CH) :
    ∃ CF0 : ℝ → List ℝ → ℝ, Closed (D3 3 𝒜) fun {eps} Fm _ => ∀ _ : D3 3 𝒜 Fm, TuSize Fm → Formalism.MainNotions.DGamSize Fm → DIVinN Fm →
      ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ CF0 eps Fm.cOut * (Fm.L x i).sc.b := by
  have : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (i : Fm.Ix x), NumberField.IsTotallyComplex (Fm.D x i).what₂.LL :=
    fun Fm x i => (Fm.D x i).tcLL
  have hDivR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps
        (selP Fm hc x hx h i).1.ψs (selP Fm hc x hx h i).1.Zs (selP Fm hc x hx h i).1.S0 (selP Fm hc x hx h i).1.S1 (Fm.ex x hx i).p0 (selP Fm hc x hx h i).1.C (selP Fm hc x hx h i).1.NuC (selP Fm hc x hx h i).1.I :=
    fun Fm hc x hx h i => (hDivG Fm hc x hx h i).toRows (Formalism.IndefR.LevelRealisationRankEquality.tupAllUsed_of_real (selB Fm hc x hx h i).Q)
  have hCsz : Closed (D3 3 𝒜) fun Fm _ => 0 ≤ Fm.Csz := Formalism.MainNotions.DIV.closed_Csz_ge_fn (D3 3 𝒜) fun _ => 0
  obtain ⟨f, hf⟩ := closed_atMid (rRows.and hCsz)
  refine ⟨fun e l => max (f e l) 1 + 1, hf.imp fun Fm _ _ hh hc _ hD hN => ?_⟩
  exact funSharp_fam (selIOf selB) hPA _ (OneMapOf selB) hDivR Fm (d3_a hc) _ hh.2 hD (hh.1 hc)
    ⟨0, fun x hx h _ i j => (hRB Fm (d3_a hc) x hx h i).oneMap j⟩ hN

theorem closed_funSharp_thr (𝒜 : FamClass)
    (sel : Formalism.L2.TSel 𝒜)
    (selS : SelS 𝒜 sel)
    (selP : BaseLevelCompatibleSelection 𝒜 sel)
    (selDH : SelDH 𝒜 sel)
    (selC : ColumnCompatibleSelection 𝒜 sel selP)
    (selB : SelB 𝒜 sel selS selP selDH selC)
    (hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.IndefR.RowsB (selB Fm hc x hx h i))
    (hPA : PrimAll sel (selIOf selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, RowsAtSel sel (selIOf selB) (fun Fm hc x hx h i C CH => Formalism.L2.Top4Wire2.DefRowsF (selIOf selB) Fm hc x hx h i C CH) (OneMapOf selB)
        Fm (d3_a hc) CH)
    (Eb Ec : List ℝ → ℝ) :
    Closed (D3 3 𝒜) fun Fm CH => ∀ _ : D3 3 𝒜 Fm, TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      ∃ CF0 : List ℝ → ℝ, Fm.Large (Formalism.MainNotions.DIV.Proofs.thrHH Eb Ec CF0) CH ∧ (DIVinN Fm →
      ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ CF0 Fm.cOut * (Fm.L x i).sc.b) := by
  obtain ⟨CF0, h⟩ := closed_funSharp 𝒜 sel selS selP selDH selC selB hRB hPA hDivG rRows
  exact closed_largeE (fun e => Formalism.MainNotions.DIV.Proofs.thrHH Eb Ec (CF0 e)) h
    fun {eps} Fm CH hL hP hc hT hD => ⟨CF0 eps, hL, hP hc hT hD⟩

end Formalism.L2.DIV.FunSharpTop

end
