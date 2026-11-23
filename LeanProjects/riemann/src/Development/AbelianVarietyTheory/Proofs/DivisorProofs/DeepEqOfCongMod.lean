import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeEqOfNatCastEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenNonemptyCrystallineTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivLabelledLatticesUnitaryTraitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsUnitaryClassicalTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsExtendToDeeperLevelStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.DeepSame

theorem deep_eq_of_congMod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (f : D.X.S.Gam → X₁.S.HH X₁.M z₁ → D.X.Ω₁) (t : ∀ (ct : UCTrait X₁ p z₁) (_ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), ct.T.P.D.toPre.X → X₁.S.HH X₁.M z₁ → PadicAlgCl p), (∀ a κ (z' : D.X.M.Z), D.q z' = z₁ → f a κ ∈ D.X.M.O z') → (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) → (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t ct yy₁ μ κ‖ ≤ δ) → ∀ (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → IsProjOver D.X.M.s → ∀ (ct₀ : UCTrait D.X p z₂) (yy₀ : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct₀.T.P.D.toPre.X), UIsLabW D.X w₂ ct₀ yy₀ → ∀ (a a' : D.X.S.Gam) (ν ν' : ct₀.T.P.D.toPre.X), yy₀ a = QuotientAddGroup.mk ν → yy₀ a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → ∀ κ, f a κ = f a' κ := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D p _ z₁ z₂ hz f t hf hsum w₁ w₂ htie hproj ct₀ yy₀ hyy₀ a a' ν ν' ha ha' hcong κ
  obtain ⟨U₁, hU₁, hct⟩ := GlobalTheory.UPoinc.UCTraitEx.exists_uCTrait_of_open E H Dw hpq l Xo cf C X₁ p
  have hU : ((D.q ⁻¹ᵁ U₁ : D.X.M.Z.Opens) : Set D.X.M.Z).Nonempty :=
    GlobalTheory.Poinc.FinPts.preimage_nonempty D.gen hU₁
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := by
    have := D.X.normal
    intro x
    exact ⟨inferInstance, inferInstance⟩
  have hfa : f a κ ∈ D.X.M.O z₂ := hf a κ z₂ hz
  have hfa' : f a' κ ∈ D.X.M.O z₂ := hf a' κ z₂ hz
  have hb : f a κ - f a' κ ∈ D.X.M.O (ct₀.y (cPt p)) := by
    rw [ct₀.cen]; exact sub_mem hfa hfa'
  have key := GlobalTheory.Poinc.eq_zero_of_val_cen_eq_zero D.X.o₁ D.X.Ω₁ D.X.M hN (D.q ⁻¹ᵁ U₁) hU p ct₀.y
    (f a κ - f a' κ) hb ?_
  · exact sub_eq_zero.1 key
  intro y' hy'
  obtain ⟨hcen, hrange⟩ := hy'
  rw [ct₀.cen] at hcen
  have hr₁ : Set.range (gPt p ≫ (y' ≫ D.q)) ⊆ (U₁ : Set X₁.M.Z) := by
    rintro _ ⟨w, rfl⟩
    exact hrange ⟨w, rfl⟩
  obtain ⟨ct', hct'⟩ := hct (y' ≫ D.q) hr₁
  have hz₁ : (y' ≫ D.q) (cPt p) = z₁ := by rw [← hz, ← hcen]; rfl
  let ct₁ : UCTrait X₁ p z₁ :=
    { y := y' ≫ D.q, cen := hz₁, T := ct'.T, ι := ct'.ι, int := ct'.int,
      comm := by have hc := ct'.comm; rw [hct'] at hc; exact hc }
  obtain ⟨yy₁, hyy₁⟩ := GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw hpq l Xo cf C X₁ w₁ p z₁ ct₁
  obtain ⟨yy, hyy, hcomp⟩ := GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ ct₁ yy₁ hyy₁ y' rfl
  let ct₂ : UCTrait D.X p z₂ := { D.lift ct₁ y' rfl with cen := hcen }
  have hyy₂ : UIsLabW D.X w₂ ct₂ yy := hyy
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_linearEquiv_labelledLattices_unitaryTraits E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ ct₀ ct₂ yy₀ yy hyy₀ hyy₂
  have h1 := he a ν ha
  have h2 := he a' ν' ha'
  obtain ⟨w, hw⟩ := hcong
  have hc : CongMod D.m (e ν) (e ν') := ⟨e w, by rw [hw, map_add, map_nsmul]⟩
  have hfin : ∀ δ : ℝ, 0 < δ → ‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖ ≤ 2 * δ := by
    intro δ hδ
    obtain ⟨S₀, hS₀⟩ := hsum ct₁ yy₁ hyy₁.uIsLab y' rfl hcen yy hyy.uIsLab hcomp a (e ν) κ h1 δ hδ
    obtain ⟨S₀', hS₀'⟩ := hsum ct₁ yy₁ hyy₁.uIsLab y' rfl hcen yy hyy.uIsLab hcomp a' (e ν') κ h2 δ hδ
    let S := (S₀ ∪ S₀').filter (fun μ => CongMod D.m μ (e ν))
    have A := hS₀ S (fun μ hμ => (Finset.mem_filter.1 hμ).2)
      (fun μ hμ hc' => Finset.mem_filter.2 ⟨Finset.mem_union_left _ hμ, hc'⟩)
    have B := hS₀' S
      (fun μ hμ => by
        obtain ⟨w₁', hw₁'⟩ := (Finset.mem_filter.1 hμ).2
        obtain ⟨w₂', hw₂'⟩ := hc
        exact ⟨w₁' + w₂', by rw [hw₁', hw₂', smul_add]; abel⟩)
      (fun μ hμ hc' => by
        refine Finset.mem_filter.2 ⟨Finset.mem_union_right _ hμ, ?_⟩
        obtain ⟨w₁', hw₁'⟩ := hc'
        obtain ⟨w₂', hw₂'⟩ := hc
        exact ⟨w₁' - w₂', by rw [hw₁', hw₂', smul_sub]; abel⟩)
    calc ‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖
        = ‖(D.X.M.val (gPt p ≫ y') (f a κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ) -
            (D.X.M.val (gPt p ≫ y') (f a' κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ)‖ := by congr 1; abel
      _ ≤ ‖D.X.M.val (gPt p ≫ y') (f a κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ‖ +
            ‖D.X.M.val (gPt p ≫ y') (f a' κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ‖ := norm_sub_le _ _
      _ ≤ δ + δ := add_le_add A B
      _ = 2 * δ := by ring
  have hxx : D.X.M.val (gPt p ≫ y') (f a κ) = D.X.M.val (gPt p ≫ y') (f a' κ) := by
    by_contra hne
    have hpos : 0 < ‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖ :=
      norm_pos_iff.2 (sub_ne_zero.2 hne)
    have := hfin (‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖ / 4) (by positivity)
    linarith
  have hsp : ∀ w, (gPt p ≫ y') w ⤳ z₂ := GlobalTheory.ZH.RatModel.gPt_specializes hcen
  have hadd := GlobalTheory.ZH.RatModel.val_add hsp (sub_mem hfa hfa') hfa'
  rw [sub_add_cancel] at hadd
  rw [hadd] at hxx
  simpa using hxx

end GlobalTheory.UPoinc.DeepSame
