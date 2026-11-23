import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularKodairaSpencerCoordinateAffineOffBoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCoordinateUniqueNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCoordsTwoChartsTransitionStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame KSIso)

theorem isUnit_ger_of_ev {Z : Scheme.{0}} {V : Z.Opens} (a : Γ(Z, V)) (y : Z) (hy : y ∈ V)
    (h : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), GlobalTheory.FlagMod.ev z V hz a ≠ 0) :
    IsUnit (ger y hy a) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
  have hWV : W ≤ V := hWV
  replace hW : IsAffineOpen W := hW
  let p := hW.primeIdealOf ⟨y, hyW⟩
  have hne := h p.asIdeal.ResidueField (spMap (algebraMap Γ(Z, W) p.asIdeal.ResidueField) ≫ GlobalTheory.FlagMod.tau hW)
    (GlobalTheory.FlagMod.le_preimage_comp _ (GlobalTheory.FlagMod.tau_le hW hWV))
  rw [← GlobalTheory.FlagMod.ev_res _ hWV (GlobalTheory.FlagMod.le_preimage_comp _ (GlobalTheory.FlagMod.tau_le hW le_rfl)),
    GlobalTheory.FlagMod.ev_spMap_tau] at hne
  have hnm : resG Z hWV a ∈ p.asIdeal.primeCompl := fun hm => hne (Ideal.algebraMap_residueField_eq_zero.2 hm)
  letI := Z.presheaf.algebra_section_stalk (⟨y, hyW⟩ : W)
  have := hW.isLocalization_stalk ⟨y, hyW⟩
  have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (Z.presheaf.stalk y) p.asIdeal (resG Z hWV a)).2 hnm
  rw [← ger_resG hWV y hyW]
  exact hu

theorem canId_nonempty : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F))
    (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)),
    (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) →
    Nonempty (CanId M) := by
  intro hdR E _ _ _ H Dw l Xo c Y X Z M hKS
  haveI : Smooth M.str := SmoothOfRelativeDimension.smooth (dimFlag Dw) M.str
  haveI : IsReduced M.X := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isReduced_of_smooth M.str
  have hBLB : (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).IsLB :=
    LB.isLB_div M.K.isLB (LB.isLB_pull ((common₀ X Z).isLB _) M.σ)
  have hloc : ∀ t : M.K.bundle.ι × X.F.J, ∃ a : Γ(M.X, ksOpen M t.1 t.2), ∀ (K : Type) [Field K]
      (z : Sp K ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ ksOpen M t.1 t.2), KSRel M t.1 t.2 z (GlobalTheory.FlagMod.ev z _ hz a) := fun t =>
    GlobalTheory.FlagMod.glue_field (ksOpen M t.1 t.2) (fun L _ z x => KSRel M t.1 t.2 z x)
      (fun L _ z hz x y hx hy => (GlobalTheory.T.kodairaSpencer_coordinate_unique_ne_zero M hKS t.1 t.2 L z hz).1 x y hx hy)
      (fun W hW hle => GlobalTheory.T.exists_regular_kodairaSpencerCoordinate_affine_off_boundary M hdR hKS t.1 t.2 W hW hle)
  choose a ha using hloc
  have cover : ∀ y ∈ M.off, ∃ t : M.K.bundle.ι × X.F.J, y ∈ ksOpen M t.1 t.2 := by
    intro y hy
    obtain ⟨i, hi⟩ := exists_chart M.K.isLB y
    obtain ⟨k, hk⟩ := ((common₀ X Z).pull M.σ).cover y
    exact ⟨(i, k), hy, hi, (((common₀ X Z).pull M.σ).mem _ k y).2 hk⟩
  have rule : ∀ (y : M.X) (t t' : M.K.bundle.ι × X.F.J) (h : y ∈ ksOpen M t.1 t.2) (h' : y ∈ ksOpen M t'.1 t'.2),
      ger y h (a t) = (tr (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) y (t.1, flagIdx M _ t.2)
        (t'.1, flagIdx M _ t'.2) : _) * ger y h' (a t') := by
    intro y t t' h h'
    have hle : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤
        (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (t.1, flagIdx M _ t.2) ⊓
          (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (t'.1, flagIdx M _ t'.2) :=
      fun q hq => ⟨hq.1.2, hq.2.2⟩
    rw [val_tr _ y (hle ⟨h, h'⟩)]
    have e : resG M.X (inf_le_left : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤ _) (a t) =
        resG M.X hle ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g (t.1, flagIdx M _ t.2)
          (t'.1, flagIdx M _ t'.2)).val * resG M.X inf_le_right (a t') := by
      refine GlobalTheory.FlagMod.ext_ev_field fun L _ z hz => ?_
      have h1 := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
      have h2 := GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz
      have hg := GlobalTheory.FlagMod.le_preimage_mono hle hz
      rw [map_mul, GlobalTheory.FlagMod.ev_res z _ hz h1, GlobalTheory.FlagMod.ev_res z _ hz h2, GlobalTheory.FlagMod.ev_res z _ hz hg]
      exact GlobalTheory.T.kodairaSpencerCoords_two_charts_transition M hKS t.1 t'.1 t.2 t'.2 L z h1 h2 hg _ _ (ha t L z h1) (ha t' L z h2)
    have := congrArg (ger y (⟨h, h'⟩ : y ∈ ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2)) e
    have e1 := ger_resG (inf_le_left : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤ _) y ⟨h, h'⟩ (a t)
    have e2 := ger_resG (inf_le_right : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤ _) y ⟨h, h'⟩ (a t')
    have e3 := ger_resG hle y ⟨h, h'⟩ ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g (t.1, flagIdx M _ t.2)
          (t'.1, flagIdx M _ t'.2)).val
    rw [map_mul, e1, e2, e3] at this
    exact this
  obtain ⟨f, hf⟩ := H0.exists_of_germs (p := M.str) (O := M.off) hBLB
    (fun t : M.K.bundle.ι × X.F.J => ksOpen M t.1 t.2) (fun t => (t.1, flagIdx M _ t.2))
    (fun t => inf_le_left) (fun t => inf_le_right) cover a rule
  have hloc' : ∀ i k, f.loc (i, flagIdx M _ k) = a (i, k) := fun i k =>
    fun_ext_ger fun y hy => (H0.germ_apply _ y hy.1 hy.2 f).symm.trans (hf (i, k) y hy)
  refine ⟨⟨f, nowhereZero_of_exists fun y hy => ?_, (isKS_iff_ksRel M f).2 @fun K _ z i k ho hi => ?_⟩⟩
  · obtain ⟨t, ht⟩ := cover y hy
    refine ⟨(t.1, flagIdx M _ t.2), ht.2, ?_⟩
    rw [hf t y ht]
    exact isUnit_ger_of_ev (a t) y ht fun L _ z hz => (GlobalTheory.T.kodairaSpencer_coordinate_unique_ne_zero M hKS t.1 t.2 L z hz).2 _ (ha t L z hz)
  · have hk : KSRel M i k z (GlobalTheory.FlagMod.ev z (ksOpen M i k) (GlobalTheory.FlagMod.le_preimage_inf ho hi) (a (i, k))) :=
      ha (i, k) K z (GlobalTheory.FlagMod.le_preimage_inf ho hi)
    have e : H0.val (B := LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi f =
        GlobalTheory.FlagMod.ev z (ksOpen M i k) (GlobalTheory.FlagMod.le_preimage_inf ho hi) (a (i, k)) := by
      rw [← hloc' i k]
      rfl
    rw [e]
    exact @hk

end GlobalTheory.CompHS
