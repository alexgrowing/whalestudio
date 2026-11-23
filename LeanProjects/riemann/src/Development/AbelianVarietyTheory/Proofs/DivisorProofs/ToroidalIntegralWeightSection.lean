import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefLineBundleWeightGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleWeightGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveGenerationCanonicalNefNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerIsoFlagTangentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecCanonTensPullId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalSectionModificationWeightStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

theorem gapGe_stdWt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) :
    GapGe 1 (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw) := by
  intro τ k hk
  simp only [gap, dif_pos hk, GlobalTheory.CompHt.stdWt]
  push_cast
  omega

theorem gapGe_sub_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (m : ℕ) (b : AllWt.Weight Dw) (h : GapGe (m : ℤ) b) :
    GapGe 0 (b - m • (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw)) := by
  intro τ k hk
  have h1 := h τ k hk
  simp only [gap, dif_pos hk, Pi.sub_apply, Pi.smul_apply, GlobalTheory.CompHt.stdWt] at h1 ⊢
  rw [nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  linarith

theorem cls_common_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ) (a : Λ) :
    cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) := by
  induction n with
  | zero =>
    have h := cls_common_add C 0 0
    simp only [add_zero] at h
    simp only [zero_nsmul]
    exact left_eq_add.1 h
  | succ n ih =>
    rw [succ_nsmul, cls_common_add C, ih, succ_nsmul]

theorem exists_canSec_ne_zero_at : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → 1 ≤ dimFlag Dw → ∀ (hV : IsVariety₀ TF.X Z) (la : AllWt.Weight Dw), GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) → letI := hV.1; ∀ y ∈ U₀ TF.X Z, ∃ g : H0 (str₀ TF.X Z) (tens (CanonLB.all (str₀ TF.X Z) (dimFlag Dw)).bundle (L₀ TF.X Z (la - FlagTan.kap Dw))) ⊤, y ∈ nonzeroLocus (toSec g) := by
  intro hP hN hNa hS hT hL E _ _ _ H Dw l Xo c TF Z hF hD hV la hg
  letI := hV.1
  intro y hy
  set std : AllWt.Weight Dw := GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) with hstd_def
  set m : ℕ := (dimFlag Dw + 1).choose 2 + 1 with hm_def
  have hstd : GapGe 1 std := gapGe_stdWt Dw
  have hmu : GapGe 0 (la - FlagTan.kap Dw - m • std) := gapGe_sub_smul m _ hg
  letI := algebraΓOfHom (str₀ TF.X Z)
  have nef : ∀ w : AllWt.Weight Dw, GapGe 0 w → IsNef c.F (L₀ TF.X Z w) :=
    fun w hw => GlobalTheory.T.nef_line_bundle_weight_gap hP hN hL E H Dw l Xo c TF Z hF w hw
  obtain ⟨mu, hmu0, m', hm', hA⟩ := GlobalTheory.T.ample_line_bundle_weight_gap hP hN hS hT E H Dw l Xo c TF Z hF std hstd y hy
  have C := common₀ TF.X Z
  have e₁ : m' • cls (L₀ TF.X Z std) (isLB_L₀ TF.X Z std) =
      cls (L₀ TF.X Z (m' • std - mu)) (isLB_L₀ TF.X Z _) + cls (L₀ TF.X Z mu) (isLB_L₀ TF.X Z mu) := by
    have h := cls_common_add (common₀ TF.X Z) (m' • std - mu) mu
    rw [sub_add_cancel] at h
    rw [← h]
    exact (cls_common_nsmul (common₀ TF.X Z) m' std).symm
  have e₂ : cls (L₀ TF.X Z (la - FlagTan.kap Dw)) (isLB_L₀ TF.X Z _) =
      m • cls (L₀ TF.X Z std) (isLB_L₀ TF.X Z std) + cls (L₀ TF.X Z (la - FlagTan.kap Dw - m • std)) (isLB_L₀ TF.X Z _) := by
    have h := cls_common_add (common₀ TF.X Z) (m • std) (la - FlagTan.kap Dw - m • std)
    rw [add_sub_cancel] at h
    rw [h]
    exact congrArg (· + _) (cls_common_nsmul (common₀ TF.X Z) m std)
  obtain ⟨s, hs⟩ := GlobalTheory.T.effective_generation_canonical_nef_numberField hNa hN c.F (Y₀ TF.X Z) (str₀ TF.X Z) (dimFlag Dw) hV.2.1 hV.2.2 hD
    (CanonLB.all _ _) (L₀ TF.X Z std) (L₀ TF.X Z (la - FlagTan.kap Dw - m • std)) (L₀ TF.X Z (la - FlagTan.kap Dw))
    (isLB_L₀ TF.X Z _) (isLB_L₀ TF.X Z _) (isLB_L₀ TF.X Z _) m' m y (nef std (hstd.mono (by norm_num))) (nef _ hmu)
    (by omega) ⟨_, _, isLB_L₀ TF.X Z (m' • std - mu), isLB_L₀ TF.X Z mu, hm', e₁, hA, nef mu hmu0⟩ e₂
  refine ⟨H0.ofSec _ ⊤ s, ?_⟩
  rwa [show toSec (H0.ofSec (str₀ TF.X Z) ⊤ s) = s from H0.bijective_ofSec_top.1 (ofSec_toSec _)]

theorem freeOnOpen_of_gapGe : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed Xo c → 1 ≤ dimFlag Dw → ∀ la : AllWt.Weight Dw, GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) → CuspIso TF.X Z U la → FreeOnOpen TF.X Z U la := by
  intro hP hG hQ hNa hPr hS hT hL E _ _ _ H Dw l Xo c TF Z r U hF hD la hg hC
  have hV := @GlobalTheory.VarFlag.isVariety₀_flag E _ _ _ H Dw l Xo c TF Z hF
  have hpq : 1 ≤ Dw.p + Dw.q := by
    by_contra h
    have h0 : Dw.p + Dw.q = 0 := by omega
    have : dimFlag Dw = 0 := by
      unfold GlobalTheory.FlagTan.dimFlag
      rw [h0]
      simp
    omega
  let M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw) := Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)
  obtain ⟨ω⟩ := GlobalTheory.CompHS.canId_nonempty hP.p5 E H Dw l Xo c TF.Y TF.X Z M (fun K _ _ y => GlobalTheory.T.kodaira_spencer_iso_flag_tangent hP hG E H Dw l Xo c K y hpq)
  intro y hy
  rw [mem_support_baseIdeal]
  push_neg
  obtain ⟨g, hgy⟩ := exists_canSec_ne_zero_at hP hQ.nef hNa hS hT hL E H Dw l Xo c TF Z hF hD hV la hg y hy
  haveI := hV.1
  haveI : SmoothOfRelativeDimension (dimFlag Dw) (𝟙 (Y₀ TF.X Z) ≫ str₀ TF.X Z) := M.smooth
  obtain ⟨g', hg'⟩ := GlobalTheory.ModifRefl.exists_sec_canon_tens_pull_id c.F (Y₀ TF.X Z) (str₀ TF.X Z) (dimFlag Dw) _ (isLB_L₀ TF.X Z _) g y hgy
  have hyM : (y : M.X) ∈ M.off := by
    rw [M.off_eq]
    exact hy
  obtain ⟨s, hs, hsy⟩ := GlobalTheory.T.canonical_section_modification_weight hP hG E H Dw l Xo c TF Z hF M ω la g' y hyM hg'
  exact ⟨s, hC.2 hs, hsy⟩

end GlobalTheory.HSApp
