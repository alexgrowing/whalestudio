import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResolutionDivisorsTopFormNormalCrossingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceOfBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverTargetOfBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalPrimeDivisorOrdersFunctionsTopFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentreOfValuationSubringProperDominantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorOverOrdEqSumAdaptedMonomialStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem finite_test_divisors : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G D₀ : CartierDiv X), η ≠ 0 → 0 < m → ∃ S : Set (DivOver p), S.Finite ∧ ∀ (x : X) (g f : X.functionFieldˣ) (c : ℚ), G.IsEqn x g → D₀.IsEqn x f → ((∀ E ∈ S, E.Through x → -1 < discrep E η m g - c * E.ord f) → ∀ E : DivOver p, E.Through x → -1 < discrep E η m g - c * E.ord f) ∧ ((∀ E ∈ S, E.Through x → -1 ≤ discrep E η m g - c * E.ord f) → ∀ E : DivOver p, E.Through x → -1 ≤ discrep E η m g - c * E.ord f) := by
  intro hP X _ _ p n hproj hn η m G D₀ hη hm
  haveI : LocallyOfFiniteType p := by
    obtain ⟨h1, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hproj
    infer_instance
  obtain ⟨Y, hYi, hYn, s, hsd, B, hsm, hprop, hbij, hfin, hη', hchart, hG, hD, hK⟩ :=
    GlobalTheory.T.exists_resolution_divisors_topForm_normalCrossings hP X p n hproj hn η G D₀ hη
  haveI := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth (s ≫ p)
  have hnY : topologicalKrullDim Y = n := GlobalTheory.NadelApp.topologicalKrullDim_eq_of_smooth Y (s ≫ p) n
  set S : Set (DivOver p) := ⋃ v ∈ {v : Y | v ∈ B ∧ Order.coheight v = 1},
    {E : DivOver p | ∀ f, f ∈ E.ring ↔ RegAt v (functionFieldMap s f)} with hSdef
  refine ⟨S, hfin.biUnion fun v _ => Set.Subsingleton.finite fun E hE E₂ hE₂ => ?_, ?_⟩
  · have hr : E.ring = E₂.ring := SetLike.ext fun f => (hE f).trans (hE₂ f).symm
    cases E; cases E₂
    cases hr
    rfl
  intro x g f c hg hf
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm

  have core : ∀ E : DivOver p, E.Through x → ∃ (ι : Type) (_ : Fintype ι) (Es : ι → DivOver p) (t : ι → ℤ),
      (∀ j, Es j ∈ S ∧ (Es j).Through x ∧ 0 ≤ t j) ∧
      ((∀ j, t j = 0) → (1 : ℚ) ≤ 1 + (discrep E η m g - c * E.ord f)) ∧
      ((∃ j, t j ≠ 0) → ∑ j, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) ≤
        1 + (discrep E η m g - c * E.ord f)) := by
    intro E hE
    obtain ⟨E', hE'⟩ := GlobalTheory.T.exists_primeDivisor_over_source_of_birational p s hbij E
    obtain ⟨y, hyx, hy⟩ := GlobalTheory.T.exists_centre_of_valuationSubring_proper_dominant s E'.ring x fun a ha => (hE' a).1 (hE a ha)
    obtain ⟨U, hyU, z, J, w, u, hc⟩ := hchart y
    have hgen := isFreeGen_formOf (gen_mem hyU) hc.frame
    set ω0 := formOf U (gen_mem hyU) (dOn (s ≫ p) z) with hω0
    have h0 : ω0 ≠ 0 := fun h =>
      one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
    obtain ⟨h, hh⟩ := hgen.2 (ratPull p s n η)
    have hh0 : h ≠ 0 := fun e => hη' (by simp [← hh, e])
    set H : Y.functionFieldˣ := Units.mk0 h hh0 with hH
    have hHη : ratPull p s n η = (H : Y.functionField) • ω0 := hh.symm

    have hgy : G.IsEqn (s y) g := by
      obtain ⟨V, hV, hgV⟩ := hg.exists_nhds
      exact hgV _ (hyx.mem_open V.isOpen hV)
    have hfy : D₀.IsEqn (s y) f := by
      obtain ⟨V, hV, hfV⟩ := hf.exists_nhds
      exact hfV _ (hyx.mem_open V.isOpen hV)

    have hoff : ∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j : J, v ≠ w j) → v ∉ B := by
      intro v hv h1 hne hvB
      obtain ⟨j, hj, rfl⟩ := (hc.mem v hv h1).1 hvB
      exact hne ⟨j, hj⟩ rfl
    have hHv : ∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j : J, v ≠ w j) →
        Scheme.ord (H : Y.functionField) v = 0 := by
      intro v hv h1 hne
      obtain ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := s ≫ p) h1
      have e1 := hK v F h1 (hoff v hv h1 hne) hF
      rw [hHη, F.formOrd_smul hnY h0, DivOver.formOrd_formOf_eq_zero (hv.mem_open U.isOpen hyU) hF hc.frame,
        add_zero, hF.ord_eq] at e1
      exact e1
    have hM := fun φ hφ => GlobalTheory.T.primeDivisorOver_ord_eq_sum_adaptedMonomial E' y hy (ι := J) (fun j => w j) (fun j => u j)
      (fun a b e => Subtype.ext (hc.inj a.2 b.2 e)) (fun j => hc.spec j j.2) (fun j => hc.coheight j j.2)
      (fun j => hc.ord_self j j.2) (fun j v hv _ hne => hc.ord_other j j.2 v hv hne) φ hφ
    have hMH := hM H hHv
    have hMg := hM (fnPull s g) fun v hv h1 hne => hG y v g hv h1 (hoff v hv h1 hne) hgy
    have hMf := hM (fnPull s f) fun v hv h1 hne => hD y v f hv h1 (hoff v hv h1 hne) hfy

    have hFj : ∀ j : J, ∃ F : DivOver (s ≫ p), F.IsAt (w j) := fun j =>
      DivOver.exists_isAt_of_coheight_eq_one (hc.coheight j j.2)
    choose F hF using hFj
    have hEj : ∀ j : J, ∃ Ej : DivOver p, DivOver.Over s (F j) Ej := fun j => GlobalTheory.T.exists_primeDivisor_over_target_of_birational p s hbij (F j)
    choose Es hEs using hEj
    have hA := GlobalTheory.T.birational_primeDivisor_orders_functions_topForms p n hn s hbij E E' hE'
    have hAj := fun j => GlobalTheory.T.birational_primeDivisor_orders_functions_topForms p n hn s hbij (Es j) (F j) (hEs j)

    set t : J → ℤ := fun j => E'.ord (u j) with ht
    have htn : ∀ j, 0 ≤ t j := fun j => by
      refine (E'.ord_nonneg_iff _).2 (hy _ ?_)
      rw [hc.val j j.2]
      exact regAt_fnOf hyU _ _
    set Fo := E'.formOrd ω0 with hFo
    have hlog : ∑ j : J, t j - 1 ≤ Fo :=
      GlobalTheory.T.sum_ord_sub_one_le_ord_wedgeDifferentials hnY E' hyU hy z h0 (J := J) Subtype.val Subtype.val_injective (fun j => u j)
        fun j => hc.val j j.2
    have hnn : 0 ≤ Fo := DivOver.formOrd_formOf_nonneg hnY hyU hy (dOn (s ≫ p) z) h0
    have eFE : E.formOrd η = ∑ j : J, Scheme.ord (H : Y.functionField) (w j) * t j + Fo := by
      rw [← hA.2 η hη, hHη, E'.formOrd_smul hnY h0, hMH]
    have egE : E.ord g = ∑ j : J, Scheme.ord (fnPull s g : Y.functionField) (w j) * t j := by
      rw [← hA.1 g, hMg]
    have efE : E.ord f = ∑ j : J, Scheme.ord (fnPull s f : Y.functionField) (w j) * t j := by
      rw [← hA.1 f, hMf]
    have eFj : ∀ j, (Es j).formOrd η = Scheme.ord (H : Y.functionField) (w j) := fun j => by
      rw [← (hAj j).2 η hη, hHη, (F j).formOrd_smul hnY h0,
        DivOver.formOrd_formOf_eq_zero ((hc.spec j j.2).mem_open U.isOpen hyU) (hF j) hc.frame, add_zero,
        (hF j).ord_eq]
    have egj : ∀ j, (Es j).ord g = Scheme.ord (fnPull s g : Y.functionField) (w j) := fun j => by
      rw [← (hAj j).1 g, (hF j).ord_eq]
    have efj : ∀ j, (Es j).ord f = Scheme.ord (fnPull s f : Y.functionField) (w j) := fun j => by
      rw [← (hAj j).1 f, (hF j).ord_eq]
    have key : ∑ j : J, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) =
        1 + (discrep E η m g - c * E.ord f) - (1 + Fo - ∑ j : J, (t j : ℚ)) := by
      simp only [discrep, eFE, egE, efE, eFj, egj, efj]
      push_cast
      rw [Finset.sum_div, Finset.mul_sum]
      have : ∀ j : J, (1 + ((Scheme.ord (H : Y.functionField) (w j) : ℚ) -
          (Scheme.ord (fnPull s g : Y.functionField) (w j) : ℚ) / m -
          c * (Scheme.ord (fnPull s f : Y.functionField) (w j) : ℚ))) * (t j : ℚ) =
          (t j : ℚ) + (Scheme.ord (H : Y.functionField) (w j) : ℚ) * t j -
          (Scheme.ord (fnPull s g : Y.functionField) (w j) : ℚ) * t j / m -
          c * ((Scheme.ord (fnPull s f : Y.functionField) (w j) : ℚ) * t j) := fun j => by ring
      rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
      ring
    refine ⟨J, inferInstance, Es, t, fun j => ⟨?_, ?_, htn j⟩, fun h0' => ?_, fun ⟨j0, hj0⟩ => ?_⟩
    · refine Set.mem_biUnion (x := w j) ⟨(hc.mem _ (hc.spec j j.2) (hc.coheight j j.2)).2 ⟨j, j.2, rfl⟩,
        hc.coheight j j.2⟩ fun a => (hEs j a).trans (hF j _)
    · intro a ha
      refine (hEs j a).2 ((hF j _).2 (regAt_of_specializes (hc.spec j j.2) ?_))
      exact GlobalTheory.Cartier.PullDominant.regAt_map s (regAt_of_specializes hyx ha)
    · have hs0 : ∑ j : J, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [h0' j]; simp
      have ht0 : ∑ j : J, (t j : ℚ) = 0 := Finset.sum_eq_zero fun j _ => by rw [h0' j]; simp
      have : (0 : ℚ) ≤ Fo := by exact_mod_cast hnn
      linarith
    · have h1 : 1 ≤ ∑ j : J, t j := by
        have := Finset.single_le_sum (f := t) (fun j _ => htn j) (Finset.mem_univ j0)
        have : 1 ≤ t j0 := by have := htn j0; omega
        omega
      have h1q : (1 : ℚ) ≤ ∑ j : J, (t j : ℚ) := by exact_mod_cast h1
      have hlq : (∑ j : J, (t j : ℚ)) - 1 ≤ Fo := by exact_mod_cast hlog
      rw [key]
      linarith
  refine ⟨fun hS E hE => ?_, fun hS E hE => ?_⟩
  · obtain ⟨ι, _, Es, t, hEs, h0, h1⟩ := core E hE
    by_cases hall : ∀ j, t j = 0
    · have := h0 hall
      linarith
    · push_neg at hall
      have hpos : 0 < ∑ j, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) := by
        obtain ⟨j0, hj0⟩ := hall
        refine Finset.sum_pos' (fun j _ => mul_nonneg ?_ ?_) ⟨j0, Finset.mem_univ _, mul_pos ?_ ?_⟩
        · have := hS (Es j) (hEs j).1 (hEs j).2.1; linarith
        · exact_mod_cast (hEs j).2.2
        · have := hS (Es j0) (hEs j0).1 (hEs j0).2.1; linarith
        · have : 0 < t j0 := lt_of_le_of_ne (hEs j0).2.2 (Ne.symm hj0)
          exact_mod_cast this
      have := h1 hall
      linarith
  · obtain ⟨ι, _, Es, t, hEs, h0, h1⟩ := core E hE
    by_cases hall : ∀ j, t j = 0
    · have := h0 hall
      linarith
    · push_neg at hall
      have hnn : 0 ≤ ∑ j, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) := by
        refine Finset.sum_nonneg fun j _ => mul_nonneg ?_ ?_
        · have := hS (Es j) (hEs j).1 (hEs j).2.1; linarith
        · exact_mod_cast (hEs j).2.2
      have := h1 hall
      linarith

end GlobalTheory.PairStep
