import Formalism.HermitianCurvature.HermitianCurvatureProofs.LetterPairStep

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.WeakDominationWordBounds

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
  Formalism.FourierDecayAlt.P.LetterPairRecursion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]

section
variable (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hFm : CkOn (m : ℕ∞) (GV k r) F)
    (hDom1 : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS)
    (hDom2 : ∀ K : Set (Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p)
include hFm hDom1 hDom2

lemma words_all :
    ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z', dLR u v (JF D F) g = ∫ p, xiP D p • dLR u v (rho D p F) g ∂D.μSS := by
  have base : ∀ v : List (Mat k r), (∀ X ∈ v, unitLie k r X) → v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z', dLR [] v (JF D F) g = ∫ p, xiP D p • dLR [] v (rho D p F) g ∂D.μSS := by
    intro v
    induction v with
    | nil => intro _ _ g _; rfl
    | cons X v ih =>
      intro hv hl
      have hv' : ∀ Y ∈ v, unitLie k r Y := fun Y hY => hv Y (List.mem_cons_of_mem _ hY)
      exact step_pair D hFm hDom1 hDom2 false (hv X List.mem_cons_self) (u := []) (v := v) (u2 := [])
        (v2 := X :: v) (by simp) hv' (by simp) hv (by simpa using hl) (by simp) (fun f => rfl)
        (ih hv' (by simp at hl; omega))
  intro u
  induction u with
  | nil => intro v _ hv hl; exact base v hv (by simpa using hl)
  | cons X u ih =>
    intro v hu hv hl
    have hu' : ∀ Y ∈ u, unitLie k r Y := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    exact step_pair D hFm hDom1 hDom2 true (hu X List.mem_cons_self) (u := u) (v := v) (u2 := X :: u) (v2 := v)
      hu' hv hu hv hl (by simp) (fun f => rfl) (ih v hu' hv (by simp at hl; omega))

lemma ck_all : Formalism.FourierDecayAlt.Q.CkLev k r 0 m (Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z') (JF D F) := by
  classical
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  intro g0 hg0
  have hg0G : g0 ∈ GV k r := hg0.1.1
  have hchart0 : Formalism.FourierDecayAlt.P.Ux10.chart g0 0 = g0 := by
    have h1 : (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) = Formalism.FourierDecayAlt.P.Ux10.co 0 :=
      funext fun i => (Formalism.FourierDecayAlt.P.Ux10.co_zero i).symm
    unfold Formalism.FourierDecayAlt.P.Ux10.chart Formalism.FourierDecayAlt.P.Ux10.kap
    rw [h1, Formalism.FourierDecayAlt.P.Ux10.Mv_co, Formalism.FourierDecayAlt.P.Ux10.prj_zero]
    simp
  have hcont : ContinuousAt (Formalism.FourierDecayAlt.P.Ux10.chart g0) 0 :=
    (Formalism.FourierDecayAlt.P.Ux10.chart_diff g0 Formalism.FourierDecayAlt.P.Ux10.zero_mem_dom).continuousAt
  have hV : Formalism.FourierDecayAlt.P.Ux10.Dom k r ∩ Formalism.FourierDecayAlt.P.Ux10.chart g0 ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' ∈
      𝓝 (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) :=
    Filter.inter_mem (Formalism.FourierDecayAlt.P.Ux10.dom_open.mem_nhds Formalism.FourierDecayAlt.P.Ux10.zero_mem_dom)
      (hcont.preimage_mem_nhds ((isOpen_OmPlus _ _).mem_nhds (by rw [hchart0]; exact hg0.2)))
  obtain ⟨δ1, hδ1, hsub⟩ := Metric.mem_nhds_iff.1 hV
  set δ := δ1 / 2 with hδ
  have hδp : 0 < δ := by rw [hδ]; linarith
  have hclb : Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ ⊆ Metric.ball 0 δ1 :=
    Metric.closedBall_subset_ball (by rw [hδ]; linarith)
  have hcl : Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ ⊆ Formalism.FourierDecayAlt.P.Ux10.Dom k r :=
    fun Y hY => (hsub (hclb hY)).1
  set K := Formalism.FourierDecayAlt.P.Ux10.chart g0 '' Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ with hKdef
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).image_of_continuousOn ((Formalism.FourierDecayAlt.P.Ux10.chart_cd g0).continuousOn.mono hcl)
  have hKOm : K ⊆ Om k r D.z D.z' := by
    rintro _ ⟨Y, hY, rfl⟩
    exact (⟨Formalism.FourierDecayAlt.P.Ux10.chart_mem hg0G (hcl hY), (hsub (hclb hY)).2⟩ :
      Formalism.FourierDecayAlt.P.Ux10.chart g0 Y ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z')
  have hKG : K ⊆ GV k r := fun x hx => (show x ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' from hKOm hx).1
  have hmemK : ∀ Y ∈ Metric.ball (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ, Formalism.FourierDecayAlt.P.Ux10.chart g0 Y ∈ K :=
    fun Y hY => ⟨Y, Metric.ball_subset_closedBall hY, rfl⟩
  obtain ⟨bd, hbdI, hbd⟩ := hDom2 K hK hKOm
  set WS : Set (List (Mat k r) × List (Mat k r)) :=
    (fun w : List (Formalism.FourierDecayAlt.P.Ux10.J k r) => (w.map Formalism.FourierDecayAlt.P.Ux10.Lt, ([] : List (Mat k r)))) ''
      {w | w.length ≤ m} with hWSdef
  have hWS : WS.Countable := (Set.to_countable _).image _
  have hunit : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), ∀ X ∈ w.map Formalism.FourierDecayAlt.P.Ux10.Lt, unitLie k r X := by
    intro w X hX
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hX
    exact Formalism.FourierDecayAlt.P.Ux10.Lt_unit i
  have hWSl : ∀ uv ∈ WS, (∀ Y ∈ uv.1, unitLie k r Y) ∧ (∀ Y ∈ uv.2, unitLie k r Y) ∧
      uv.1.length + uv.2.length ≤ m := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨hunit w, by simp, by simpa using hw⟩
  have good := good_set D hFm hK hKG hWS hWSl bd fun uv huv g' hg' =>
    hbd uv.1 uv.2 (hWSl uv huv).1 (hWSl uv huv).2.1 (hWSl uv huv).2.2 g' hg'
  set P0 : Set (SS k r) := {p | D.inSS p ∧ ∀ uv ∈ WS, ∀ g' ∈ K, ‖dLR uv.1 uv.2 (rho D p F) g'‖ ≤ bd p} with hP0
  have goodae : ∀ᵐ p ∂D.μSS, p ∈ P0 := good
  set hK' : SS k r → Mat k r → (Wq →L[ℂ] Wp) := fun p => if p ∈ P0 then rho D p F else fun _ => 0 with hK'def
  have hsel : ∀ p (u' v' : List (Mat k r)),
      dLR u' v' (hK' p) = if p ∈ P0 then dLR u' v' (rho D p F) else fun _ => 0 := by
    intro p u' v'
    by_cases hp : p ∈ P0
    · simp only [hK'def, if_pos hp]
    · simp only [hK'def, if_neg hp, dLR_zero]
  have hAL := int_chart_loc (xiP D) (fun p => norm_xiP D p) (continuous_xiP D).aestronglyMeasurable hK' m
    (fun p => by
      by_cases hp : p ∈ P0
      · simp only [hK'def, if_pos hp]; exact ckOn_rho D hp.1 hFm
      · simp only [hK'def, if_neg hp]; exact ckOn_zero _)
    hg0G hδp hcl
    (fun w hw Y hY => by
      refine (hDom1 (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] (hunit w) (by simp) (by simpa using hw) _
        (hKOm (hmemK Y hY))).congr ?_
      filter_upwards [goodae] with p hp
      rw [hsel, if_pos hp, dLR_rho D hp.1])
    (fun p => ‖bd p‖) hbdI.norm
    (fun w hw Y hY p => by
      rw [hsel]
      by_cases hp : p ∈ P0
      · rw [if_pos hp]; exact (hp.2 _ ⟨w, hw, rfl⟩ _ (hmemK Y hY)).trans (Real.le_norm_self _)
      · rw [if_neg hp, norm_zero]; exact norm_nonneg _)
  have hAL' : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y => JF D F (Formalism.FourierDecayAlt.P.Ux10.chart g0 Y))
      (Metric.ball 0 δ) := by
    refine hAL.congr fun Y _ => ?_
    show ∫ p, xiP D p • rho D p F _ ∂D.μSS = _
    refine integral_congr_ae ?_
    filter_upwards [goodae] with p hp
    simp only [hK'def, if_pos hp]
  obtain ⟨U, F', hU, hgU, hF', hUF⟩ := ck_at_of_chart hg0G hδp hAL'
  exact ⟨U, F', hU, hgU, hF', fun g hg hgl => hUF g hg hgl.1⟩

end

theorem _root_.Formalism.FourierDecayAlt.P.bessel_words_of_domain : JWordsOfDom := by
  intro hDom k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC
  obtain ⟨hDom1, hDom2⟩ := hDom k r Wp Wq D A m F hThr hCC
  obtain ⟨c, hc⟩ := hCC
  have hFm : CkOn (m : ℕ∞) (GV k r) F := hc.1
  have hW := words_all D hFm hDom1 hDom2
  refine ⟨ck_all D hFm hDom1 hDom2, fun u v hu hv hl g hg => ?_⟩
  obtain ⟨bd, hbdI, hbd⟩ := hDom2 {g} isCompact_singleton (Set.singleton_subset_iff.2 hg)
  have hb := hbd u v hu hv hl g (Set.mem_singleton g)
  refine ⟨hbdI.norm.mono' ((continuous_xiP D).aestronglyMeasurable.smul (hDom1 u v hu hv hl g hg)) ?_, ?_⟩
  · filter_upwards [hb] with p hp
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_xiP D p)).trans (hp.trans (Real.le_norm_self _))
  · rw [hW u v hu hv hl g hg]
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS D] with p hp
    rw [dLR_rho D hp]

end Formalism.FourierDecayAlt.P.WeakDominationWordBounds
