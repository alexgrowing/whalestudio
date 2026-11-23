import Formalism.SharpRestriction.Divisibility.HookProducts.HhOfInputs
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalLinkOfBranchIdentitiesAndMultiplicity
import Formalism.SharpRestriction.GlobalSchurBounds.LogXLowerFamilyOfTheorems
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.HeckeRamifiedZeroAll
import Formalism.LocalToGlobal.ClassOfRecordOfChoice

noncomputable section

namespace Formalism.L2.DIV.LvlWire

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

variable {eps : ℝ}

theorem ramified_level_zero_holds (Fm : FamP eps) (tT : FamU Fm ConcreteFormsLevelZero) : FamU Fm LocalLatticeBases.HeckeRamifiedLevelZero :=
  tT.mono fun D u hS h => UnramifiedTrace.hecke_ramified_zero_all D u hS h

theorem transposed_slope_of_form_tie (Fm : FamP eps) (tT : FamU Fm ConcreteFormsLevelZero) : FamU Fm product_first_zeroth_parts.family_property_and :=
  let r := slope_free_branch_family Fm tT freeTT_holds slopeLineT_holds LemB.second_branch_all_members
  (r.1.and r.2.1).mono fun _ _ hS h => by obtain ⟨⟨W⟩, hm⟩ := h; exact product_first_zeroth_parts.division_side_conditions_at_sizeData hS W hm

theorem slope_no_collision_of_form_tie (Fm : FamP eps) (tT : FamU Fm ConcreteFormsLevelZero) : FamU Fm LocalLatticeBases.CongruenceLatticeLengthBound :=
  let r := slope_free_branch_family Fm tT freeTT_holds slopeLineT_holds LemB.second_branch_all_members
  (r.2.2.and ((hI_tied Fm tT PI.IntegralAtBasePointLattice.integral_at_t0_lattice).and (ramified_level_zero_holds Fm tT))).mono
    fun _ _ hS h => LocalLatticeBases.congruence_no_kernel_minimal hS h.1 h.2.1 h.2.2

theorem level_lines_of_form_tie (Fm : FamP eps) (tT : FamU Fm ConcreteFormsLevelZero) (hTu : TuSize Fm) : J.LvlF Fm :=
  lvlF_of Fm (Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hTu) (transposed_slope_of_form_tie Fm tT) (slope_no_collision_of_form_tie Fm tT)

theorem lvlF_of_ties (Fm : FamP eps) (t : RealPlaceSecondLayerConditions Fm) (hTu : TuSize Fm) : J.LvlF Fm :=
  level_lines_of_form_tie Fm (family_conditions_of_layer_two Fm t).2.2 hTu

theorem level_lines_of_family_bound (Fm : FamP eps) (crystallineComparison : ℝ) (h10 : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) (hTu : TuSize Fm) : J.LvlF Fm := by
  obtain ⟨a, h⟩ := h10
  refine lvlF_of Fm (Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hTu)
    ⟨a, fun x hx _ i u hS => product_first_zeroth_parts.ramified_rank_lines_of_full (h x hx i u hS).2.1⟩
    ⟨a, fun x hx _ i u hS w hw => ⟨((h x hx i u hS).2.2.2.2.1 w hw).1, ((h x hx i u hS).2.2.2.2.1 w hw).2.2⟩⟩

theorem slope_lemma_division_side (Fm : FamP eps) (hE : J.LvlF Fm) (hTu : TuSize Fm) (hrk : J.MuRank Fm) (lG : LinkG Fm) (lMu : LinkMu Fm) :
    LocalQuadraticParts.SlopeLemmaFamily Fm := by
  obtain ⟨C, x0, -, h⟩ := Lnk.slopesNF_of Fm
    (Formalism.L2.GlobalTheoryTheory.Places.placesF_min' Fm (J.lemma_five_one_of_theorem_two Fm hTu hE) (nuCommensF_min Fm hE) hTu hrk lG lMu)
  exact ⟨C, x0, fun x hx i _ u => h x hx i u⟩

theorem nuFullF_of_lvl (Fm : FamP eps) (hE : J.LvlF Fm) : NuFullF Fm := nuFullF_of Fm (nuCommensF_min Fm hE)

theorem muRank_of_lvl (Fm : FamP eps) {C0 : ℝ} (hC0 : 0 < C0) (cPr : ChosenProviso Fm C0) (hE : J.LvlF Fm) (hTu : TuSize Fm) :
    J.MuRank Fm :=
  muRank_min Fm hC0 cPr (nuFullF_of_lvl Fm hE) hE (Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hTu)

theorem hh_of_lvl (Fm : FamP eps) (CH : ℝ) (Eb CF0 : List ℝ → ℝ)
    (hL : Fm.Large (Formalism.MainNotions.DIV.Proofs.thrHH Eb Formalism.MainNotions.DIV.HookProducts.Row4C.EcHH CF0) CH)
    (hE : J.LvlF Fm) (hTu : TuSize Fm) (hrk : J.MuRank Fm)
    (lG : LinkG Fm) (lMu : LinkMu Fm) (c2 : LocalQuadraticParts.ComplementTwoFamily Fm)
    (hb : ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) u,
      (((Fm.D x i).fm u).lat 0).muMax ≤ (Fm.L x i).sc.x ^ Eb Fm.cOut * (Fm.L x i).sc.b)
    (he : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ CF0 Fm.cOut * (Fm.L x i).sc.b) :
    LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH :=
  Formalism.MainNotions.DIV.Proofs.height_bound_of_component_bounds Fm CH Eb Formalism.MainNotions.DIV.HookProducts.Row4C.EcHH CF0 hL
    (slope_lemma_division_side Fm hE hTu hrk lG lMu) hrk (nuFullF_of_lvl Fm hE) hb (Formalism.MainNotions.DIV.HookProducts.Row4C.gauge_form_bound_of_uniform_size Fm c2) hTu he

theorem proviso_of_working_class {𝒜 : FamClass} {C0 : ℝ} (Fm : FamP eps) (hc : Formalism.L2.Top3.D3 C0 𝒜 Fm) : ChosenProviso Fm C0 := by
  obtain ⟨CH, C5, c6, Cb, -, -, -, -, -, -, -, -, cPr, -⟩ := hc.2.1
  exact cPr

theorem hh_of_sel {𝒜 : FamClass} (Fm : FamP eps) (hc : Formalism.L2.Top3.D3 3 𝒜 Fm) (s : Formalism.L2.TSelF Fm)
    (hχ : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x) (h : s.1 ≤ x), x0 ≤ x → ∀ (i : Fm.Ix x) u, ChiFin0 ((s.2 x hx h i).T.cols.forms u))
    (CH : ℝ) (Eb CF0 : List ℝ → ℝ)
    (hL : Fm.Large (Formalism.MainNotions.DIV.Proofs.thrHH Eb Formalism.MainNotions.DIV.HookProducts.Row4C.EcHH CF0) CH)
    (hTu : TuSize Fm) (lG : LinkG Fm) (lMu : LinkMu Fm) (c2 : LocalQuadraticParts.ComplementTwoFamily Fm)
    (hb : ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) u,
      (((Fm.D x i).fm u).lat 0).muMax ≤ (Fm.L x i).sc.x ^ Eb Fm.cOut * (Fm.L x i).sc.b)
    (he : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ CF0 Fm.cOut * (Fm.L x i).sc.b) :
    LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH :=
  have hE : J.LvlF Fm := lvlF_of_ties Fm (Formalism.L2.Top3.real_place_second_layer_conditions_of_choice s hχ) hTu
  hh_of_lvl Fm CH Eb CF0 hL hE hTu (muRank_of_lvl Fm (by norm_num) (proviso_of_working_class Fm hc) hE hTu) lG lMu c2 hb he

theorem closed_lvl {𝒜 : FamClass} (sel : Formalism.L2.TSel 𝒜)
    (hχ : Closed (Formalism.L2.Top3.D3 3 𝒜) fun Fm _ => ∀ hc : Formalism.L2.Top3.D3 3 𝒜 Fm, ∃ x0 : ℝ,
      ∀ x (hx : Fm.x1 < x) (h : (sel Fm (Formalism.L2.Top3.d3_a hc)).1 ≤ x), x0 ≤ x →
        ∀ (i : Fm.Ix x) u, ChiFin0 (((sel Fm (Formalism.L2.Top3.d3_a hc)).2 x hx h i).T.cols.forms u)) :
    Closed (Formalism.L2.Top3.D3 3 𝒜) fun Fm _ => J.LvlF Fm ∧ NuFullF Fm ∧ J.MuRank Fm :=
  Formalism.L2.Top3.closed_of_mem <| hχ.imp fun Fm _ _ h hc =>
    have hE : J.LvlF Fm := lvlF_of_ties Fm (Formalism.L2.Top3.real_place_second_layer_conditions_of_choice (sel Fm (Formalism.L2.Top3.d3_a hc)) (h hc)) hc.2.2.1
    ⟨hE, nuFullF_of_lvl Fm hE, muRank_of_lvl Fm (by norm_num) (proviso_of_working_class Fm hc) hE hc.2.2.1⟩

end Formalism.L2.DIV.LvlWire

end

set_option pp.fullNames true
