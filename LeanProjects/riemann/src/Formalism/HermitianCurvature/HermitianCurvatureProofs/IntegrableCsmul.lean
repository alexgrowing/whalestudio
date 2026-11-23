import Formalism.HermitianCurvature.HermitianCurvatureProofs.Imports
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDomainMeasurable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLevelMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JacquetRaisingOperator

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section right

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def pR (ξ : Mt k r × Mt k r) : SS k r := ((Matrix.of.symm 1, Matrix.of.symm 1), ξ)

def InR (Bs : RealPlaceData k r Wp Wq) (ξ : Mt k r × Mt k r) : Prop :=
  (Matrix.of ξ.1 : Mat k r) ∈ UWset k r Bs.z' ∧ (Matrix.of ξ.2 : Mat k r) ∈ Nset k r

theorem inSS_pR (Bs : RealPlaceData k r Wp Wq) {ξ : Mt k r × Mt k r} (h : InR Bs ξ) : Bs.inSS (pR ξ) := by
  refine ⟨?_, ?_, h.1, h.2⟩
  · show (Matrix.of (Matrix.of.symm 1) : Mat k r) ∈ UWset k r Bs.z
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.C2x7.one_mem_UW Bs.z
  · show (Matrix.of (Matrix.of.symm 1) : Mat k r) ∈ Nset k r
    rw [Equiv.apply_symm_apply]; exact Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one

theorem rho_pR (Bs : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (ξ : Mt k r × Mt k r) (x : Mat k r) :
    rho Bs (pR ξ) F x = (F (x * Matrix.of ξ.2 * Matrix.of ξ.1)).comp (Bs.π' (Matrix.of ξ.1)⁻¹) := by
  simp only [rho, sgs, pR, Equiv.apply_symm_apply, inv_one, Matrix.one_mul, Bs.π_rep.1]
  rfl

theorem AdL_pR (ξ : Mt k r × Mt k r) (X : Mat k r) : AdL (pR ξ) X = X := by
  simp [AdL, sL, pR]

theorem kr_eq (Bs : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (x : Mat k r) :
    Kr Bs F x = ∫ ξ, star (psi k r Bs.z' cStd (Matrix.of ξ.2)) • rho Bs (pR ξ) F x ∂(Bs.μW'.prod Bs.μN) := by
  unfold Kr
  congr 1
  funext ξ
  rw [rho_pR]

theorem ae_inR (Bs : RealPlaceData k r Wp Wq) : ∀ᵐ ξ ∂(Bs.μW'.prod Bs.μN), InR Bs ξ := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW'
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarN
  have h1 : ∀ᵐ ξ ∂(Bs.μW'.prod Bs.μN), (Matrix.of ξ.1 : Mat k r) ∈ UWset k r Bs.z' :=
    Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B5.haar_ae Bs.haarW')
  have h2 : ∀ᵐ ξ ∂(Bs.μW'.prod Bs.μN), (Matrix.of ξ.2 : Mat k r) ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Formalism.FourierDecayAlt.P.B5.haar_ae Bs.haarN)
  filter_upwards [h1, h2] with ξ a b
  exact ⟨a, b⟩

theorem isClosed_InR (Bs : RealPlaceData k r Wp Wq) : IsClosed {ξ : Mt k r × Mt k r | InR Bs ξ} :=
  IsClosed.and ((Formalism.FourierDecayAlt.P.B6.isClosed_UWset k r Bs.z').preimage continuous_fst)
    ((Formalism.FourierDecayAlt.P.B6.isClosed_Nset k r).preimage continuous_snd)

theorem norm_psi_le (z : Fin (2 * r + k + 1) → ℂ) (n : Mat k r) : ‖star (psi k r z cStd n)‖ ≤ 1 := by
  rw [norm_star, psi, Complex.norm_exp]
  simp

section zeroNear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem op_zero_near {X : Mat k r} (b : Bool) (hX : inLie k r X) {f : Mat k r → E} {U : Set (Mat k r)}
    (hU : IsOpen U) (hf : ∀ g ∈ GV k r, g ∈ U → f g = 0) : ∀ g ∈ GV k r, g ∈ U → op b X f g = 0 := by
  intro g hg hgU
  unfold op
  have hc : Continuous (fun t : ℝ => cv b X t g) := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.cv_continuous b X g
  have hU0 : U ∈ 𝓝 (cv b X 0 g) := by rw [cv_zero]; exact hU.mem_nhds hgU
  have hev : (fun t : ℝ => f (cv b X t g)) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds hU0] with t ht
    exact hf _ (cv_mem hX hg t) ht
  rw [hev.deriv_eq]
  simp

theorem W_zero_near (w : List (Bool × Mat k r)) (hw : AllLie w) {f : Mat k r → E} {U : Set (Mat k r)}
    (hU : IsOpen U) (hf : ∀ g ∈ GV k r, g ∈ U → f g = 0) : ∀ g ∈ GV k r, g ∈ U → W w f g = 0 := by
  induction w with
  | nil => exact hf
  | cons x w ih =>
    rw [W_cons]
    exact op_zero_near x.1 (hw x List.mem_cons_self) hU (ih fun y hy => hw y (List.mem_cons_of_mem _ hy))

end zeroNear

section ck

variable [FiniteDimensional ℂ Wp]

theorem inv_cont_GV : ContinuousOn (fun y : Mat k r => y⁻¹) (GV k r) := by
  have hc : Continuous (fun y : Mat k r => Hpk k r * yᴴ * Hpk k r) :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  refine hc.continuousOn.congr fun y hy => ?_
  exact Formalism.FourierDecayAlt.P.B6.inv_eq_hermitian_form_conjTranspose hy

theorem kr_ck (Bs : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn ⊤ (GV k r) F)
    {C : Set (Mat k r)} (hC : IsCompact C) (hz : ∀ g ∈ GV k r, g ∉ C → F g = 0) (m : ℕ) {x0 : Mat k r}
    (hx0 : x0 ∈ GV k r) :
    ∃ (U : Set (Mat k r)) (F' : Mat k r → (Wq →L[ℂ] Wp)), IsOpen U ∧ x0 ∈ U ∧
      ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) F' U ∧ ∀ g ∈ U, g ∈ GV k r → Kr Bs F g = F' g := by
  classical
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW'
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarN
  set μ := Bs.μW'.prod Bs.μN with hμ
  have hFm : CkOn (m : ℕ∞) (GV k r) F := Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF

  obtain ⟨δ1, hδ1, hsub⟩ := Metric.mem_nhds_iff.1
    (Formalism.FourierDecayAlt.P.Ux10.dom_open.mem_nhds (Formalism.FourierDecayAlt.P.Ux10.zero_mem_dom (k := k) (r := r)))
  set δ := δ1 / 2 with hδ
  have hδp : 0 < δ := by rw [hδ]; linarith
  have hcl : Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ ⊆ Formalism.FourierDecayAlt.P.Ux10.Dom k r :=
    fun Y hY => hsub (Metric.closedBall_subset_ball (by rw [hδ]; linarith) hY)
  set K := Formalism.FourierDecayAlt.P.Ux10.chart x0 '' Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ with hKdef
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).image_of_continuousOn ((Formalism.FourierDecayAlt.P.Ux10.chart_cd x0).continuousOn.mono hcl)
  have hKG : K ⊆ GV k r := by
    rintro _ ⟨Y, hY, rfl⟩
    exact Formalism.FourierDecayAlt.P.Ux10.chart_mem hx0 (hcl hY)
  have hmemK : ∀ Y ∈ Metric.ball (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ, Formalism.FourierDecayAlt.P.Ux10.chart x0 Y ∈ K :=
    fun Y hY => ⟨Y, Metric.ball_subset_closedBall hY, rfl⟩

  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hF hC hz 0 m
  have hbnd : ∀ u : List (Mat k r), (∀ X ∈ u, unitLie k r X) → u.length ≤ m → ∀ g ∈ GV k r,
      ‖dLR u [] F g‖ ≤ c := by
    intro u hu hl g hg
    have := hc.2 u [] hu (by simp) (by simpa using hl) g hg
    rwa [Real.rpow_zero, one_mul] at this

  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r Bs.z' Bs.z'_mem Bs.T'_pos
  set φ : Mat k r × Mat k r × Mat k r → Mat k r :=
    fun t => (Hpk k r * t.1ᴴ * Hpk k r) * t.2.1 * (Hpk k r * t.2.2ᴴ * Hpk k r) with hφ
  have hφc : Continuous φ :=
    ((continuous_const.matrix_mul continuous_fst.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
      (continuous_snd.fst) |>.matrix_mul
      ((continuous_const.matrix_mul continuous_snd.snd.matrix_conjTranspose).matrix_mul continuous_const)
  set Kn := φ '' (K ×ˢ C ×ˢ UWset k r Bs.z') with hKn
  have hKnc : IsCompact Kn := (hK.prod (hC.prod hW)).image hφc
  set S' : Set (Mt k r × Mt k r) := {ξ | (Matrix.of ξ.2 : Mat k r) ∈ Kn} with hS'
  have hS'c : IsClosed S' :=
    hKnc.isClosed.preimage (show Continuous (fun ξ : Mt k r × Mt k r => (Matrix.of ξ.2 : Mat k r)) from continuous_snd)
  have hS'm : MeasurableSet S' := hS'c.measurableSet

  have hWm : Bs.μW' Set.univ < ⊤ := by
    have h1 : Bs.μW' {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r Bs.z'} < ⊤ :=
      Bs.haarW'.finite_compact _ hW
    calc Bs.μW' Set.univ ≤ Bs.μW' {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r Bs.z'} +
          Bs.μW' {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r Bs.z'}ᶜ := by
          rw [← Set.union_compl_self {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r Bs.z'}]
          exact measure_union_le _ _
      _ < ⊤ := by
          have h2 : Bs.μW' {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r Bs.z'}ᶜ = 0 := Bs.haarW'.conc
          rw [h2, add_zero]; exact h1
  have hNm : Bs.μN {x : Mt k r | (Matrix.of x : Mat k r) ∈ Kn} < ⊤ := Bs.haarN.finite_compact _ hKnc
  have hS'fin : μ S' < ⊤ := by
    have e : S' = Set.univ ×ˢ {x : Mt k r | (Matrix.of x : Mat k r) ∈ Kn} := by
      ext ξ; simp [hS']
    rw [e, hμ, Measure.prod_prod]
    exact ENNReal.mul_lt_top hWm hNm
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hbnd [] (by simp) (by simp) 1 Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_one)
  set β : Mt k r × Mt k r → ℝ := S'.indicator (fun _ => c) with hβ
  have hβI : Integrable β μ :=
    (integrableOn_const (μ := μ) (s := S') (C := c) hS'fin.ne).integrable_indicator hS'm

  set hfam : Mt k r × Mt k r → Mat k r → (Wq →L[ℂ] Wp) :=
    fun ξ => if InR Bs ξ then rho Bs (pR ξ) F else fun _ => 0 with hfamdef
  have hsel : ∀ ξ (u v : List (Mat k r)),
      dLR u v (hfam ξ) = if InR Bs ξ then dLR u v (rho Bs (pR ξ) F) else fun _ => 0 := by
    intro ξ u v
    by_cases hξ : InR Bs ξ
    · simp only [hfamdef, if_pos hξ]
    · simp only [hfamdef, if_neg hξ]; exact Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.dLR_zero u v
  have hunit : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), ∀ X ∈ w.map Formalism.FourierDecayAlt.P.Ux10.Lt, unitLie k r X := by
    intro w X hX
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hX
    exact Formalism.FourierDecayAlt.P.Ux10.Lt_unit i
  have hmapAd : ∀ ξ (u : List (Mat k r)), u.map (AdL (pR ξ)) = u := by
    intro ξ u
    have e : AdL (pR ξ) = id := funext (AdL_pR ξ)
    rw [e, List.map_id]

  have hform : ∀ (w : List (Formalism.FourierDecayAlt.P.Ux10.J k r)) ξ (y : Mat k r), InR Bs ξ →
      dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] (hfam ξ) y =
        (dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] F (y * Matrix.of ξ.2 * Matrix.of ξ.1)).comp
          (Bs.π' (Matrix.of ξ.1)⁻¹) := by
    intro w ξ y hξ
    rw [hsel, if_pos hξ, Formalism.FourierDecayAlt.P.SandwichRhoAction.dLR_rho Bs (inSS_pR Bs hξ), hmapAd, List.map_nil, rho_pR]
  have hSm : MeasurableSet {ξ : Mt k r × Mt k r | InR Bs ξ} := (isClosed_InR Bs).measurableSet
  have hres : μ.restrict {ξ : Mt k r × Mt k r | InR Bs ξ} = μ := Measure.restrict_eq_self_of_ae_mem (ae_inR Bs)
  have hSGV : ∀ ξ, InR Bs ξ → (Matrix.of ξ.1 : Mat k r) ∈ GV k r ∧ (Matrix.of ξ.2 : Mat k r) ∈ GV k r :=
    fun ξ h => ⟨h.1.1, h.2.1⟩

  have hM : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), w.length ≤ m → ∀ Y ∈ Metric.ball (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ,
      AEStronglyMeasurable (fun ξ => dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] (hfam ξ) (Formalism.FourierDecayAlt.P.Ux10.chart x0 Y)) μ := by
    intro w hw Y hY
    set y := Formalism.FourierDecayAlt.P.Ux10.chart x0 Y with hydef
    have hy : y ∈ GV k r := hKG (hmemK Y hY)
    have hd : ContinuousOn (dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] F) (GV k r) := by
      rw [Formalism.FourierDecayAlt.P.B4.dLR_eq]
      refine Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (m := ((0 : ℕ) : ℕ∞)) ?_
      exact smooth_on_of_word_derivatives _ (allLie_lr (hunit w) (by simp)) 0 (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF)
    have hf1 : Continuous (fun ξ : Mt k r × Mt k r => y * (Matrix.of ξ.2 : Mat k r) * (Matrix.of ξ.1 : Mat k r)) :=
      (continuous_const.matrix_mul continuous_snd).matrix_mul continuous_fst
    have hmap1 : Set.MapsTo (fun ξ : Mt k r × Mt k r => y * (Matrix.of ξ.2 : Mat k r) * (Matrix.of ξ.1 : Mat k r))
        {ξ | InR Bs ξ} (GV k r) := fun ξ h =>
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hy (hSGV ξ h).2) (hSGV ξ h).1
    have hg1 : ContinuousOn (fun ξ : Mt k r × Mt k r => Bs.π' ((Matrix.of ξ.1 : Mat k r))⁻¹) {ξ | InR Bs ξ} := by
      refine Bs.π'_cont.comp (inv_cont_GV.comp continuous_fst.continuousOn fun ξ h => (hSGV ξ h).1) ?_
      intro ξ h
      exact Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv h.1
    have hG : ContinuousOn (fun ξ : Mt k r × Mt k r =>
        (dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] F (y * Matrix.of ξ.2 * Matrix.of ξ.1)).comp
          (Bs.π' (Matrix.of ξ.1)⁻¹)) {ξ | InR Bs ξ} :=
      (hd.comp hf1.continuousOn hmap1).clm_comp hg1
    have hGm := hG.aestronglyMeasurable (μ := μ) hSm
    rw [hres] at hGm
    refine hGm.congr ?_
    filter_upwards [ae_inR Bs] with ξ hξ
    exact (hform w ξ y hξ).symm

  have hβ0 : ∀ ξ, 0 ≤ β ξ := fun ξ => Set.indicator_nonneg (fun _ _ => hc0) ξ
  have hbd : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), w.length ≤ m → ∀ Y ∈ Metric.ball (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ,
      ∀ ξ, ‖dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] (hfam ξ) (Formalism.FourierDecayAlt.P.Ux10.chart x0 Y)‖ ≤ β ξ := by
    intro w hw Y hY ξ
    set y := Formalism.FourierDecayAlt.P.Ux10.chart x0 Y with hydef
    have hyK : y ∈ K := hmemK Y hY
    have hy : y ∈ GV k r := hKG hyK
    by_cases hξ : InR Bs ξ
    · rw [hform w ξ y hξ]
      set q := y * (Matrix.of ξ.2 : Mat k r) * (Matrix.of ξ.1 : Mat k r) with hq
      have hqG : q ∈ GV k r :=
        Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hy (hSGV ξ hξ).2) (hSGV ξ hξ).1
      have h1 : ‖(dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] F q).comp (Bs.π' (Matrix.of ξ.1 : Mat k r)⁻¹)‖ ≤
          ‖dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] F q‖ := by
        calc _ ≤ ‖dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] F q‖ * ‖Bs.π' (Matrix.of ξ.1 : Mat k r)⁻¹‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] F q‖ * 1 :=
              mul_le_mul_of_nonneg_left (Formalism.FourierDecayAlt.P.B7.norm_pi'_le Bs (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hξ.1))
                (norm_nonneg _)
          _ = _ := mul_one _
      refine h1.trans ?_
      by_cases hqC : q ∈ C
      · have hmem : ξ ∈ S' := by
          show (Matrix.of ξ.2 : Mat k r) ∈ Kn
          refine ⟨(y, q, (Matrix.of ξ.1 : Mat k r)), ⟨hyK, hqC, hξ.1⟩, ?_⟩
          have hyu : IsUnit y.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hy
          have hhu : IsUnit (Matrix.of ξ.1 : Mat k r).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hξ.1.1
          simp only [hφ]
          rw [← Formalism.FourierDecayAlt.P.B6.inv_eq_hermitian_form_conjTranspose hy, ← Formalism.FourierDecayAlt.P.B6.inv_eq_hermitian_form_conjTranspose hξ.1.1, hq]
          rw [show y⁻¹ * (y * (Matrix.of ξ.2 : Mat k r) * (Matrix.of ξ.1 : Mat k r)) * (Matrix.of ξ.1 : Mat k r)⁻¹ =
            (y⁻¹ * y) * (Matrix.of ξ.2 : Mat k r) * ((Matrix.of ξ.1 : Mat k r) * (Matrix.of ξ.1 : Mat k r)⁻¹) by
              simp only [Matrix.mul_assoc]]
          rw [Matrix.nonsing_inv_mul _ hyu, Matrix.mul_nonsing_inv _ hhu, Matrix.one_mul, Matrix.mul_one]
        rw [hβ, Set.indicator_of_mem hmem]
        exact hbnd _ (hunit w) (by simpa using hw) q hqG
      · have h0 : dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] F q = 0 := by
          rw [Formalism.FourierDecayAlt.P.B4.dLR_eq]
          exact W_zero_near _ (allLie_lr (hunit w) (by simp)) hC.isClosed.isOpen_compl
            (fun g hg hgC => hz g hg hgC) q hqG hqC
        rw [h0, norm_zero]
        exact hβ0 ξ
    · rw [hsel, if_neg hξ, norm_zero]
      exact hβ0 ξ
  have hh : ∀ ξ, CkOn ((m : ℕ) : ℕ∞) (GV k r) (hfam ξ) := by
    intro ξ
    by_cases hξ : InR Bs ξ
    · simp only [hfamdef, if_pos hξ]; exact ckOn_rho Bs (inSS_pR Bs hξ) hFm
    · simp only [hfamdef, if_neg hξ]; exact Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.ckOn_zero _
  have hpRc : Continuous (fun ξ : Mt k r × Mt k r => pR ξ) := continuous_const.prodMk continuous_id
  have hAL := int_chart_loc (fun ξ => Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ)) (fun ξ => Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.norm_xiP Bs _)
    ((Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.continuous_xiP Bs).comp hpRc).aestronglyMeasurable hfam m hh hx0 hδp hcl hM β hβI hbd
  have hxi : ∀ ξ, Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) = star (psi k r Bs.z' cStd (Matrix.of ξ.2)) := by
    intro ξ
    simp only [Formalism.FourierDecayAlt.JF.xiP, pR, Equiv.apply_symm_apply, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z_mem, one_mul]
  have hAL' : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y => Kr Bs F (Formalism.FourierDecayAlt.P.Ux10.chart x0 Y))
      (Metric.ball 0 δ) := by
    refine hAL.congr fun Y _ => ?_
    show Kr Bs F _ = _
    rw [kr_eq]
    refine integral_congr_ae ?_
    filter_upwards [ae_inR Bs] with ξ hξ
    simp only [hfamdef, if_pos hξ, hxi]
  exact ck_at_of_chart hx0 hδp hAL'

theorem kr_loc_cpt (Bs : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn ⊤ (GV k r) F)
    {C : Set (Mat k r)} (hC : IsCompact C) (hz : ∀ g ∈ GV k r, g ∉ C → F g = 0) :
    ∀ x0 ∈ GV k r, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ⊤ (Kr Bs F) x0 := by
  have hS : Formalism.FourierDecayAlt.Q.SmoothLev k r 0 Set.univ (Kr Bs F) := by
    refine Formalism.FourierDecayAlt.P5.Rad.smoothLev_of_ck isOpen_univ fun m => ?_
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hF', hUF⟩ := kr_ck Bs hF hC hz m hg₀.1.1
    exact ⟨U, F', hU, hgU, hF', fun g hg hgl => hUF g hg hgl.1⟩
  intro x0 hx0
  obtain ⟨U, F', hU, hgU, hF', hUF⟩ := hS x0 ⟨Formalism.FourierDecayAlt.P5.Rad.glev0 hx0, Set.mem_univ _⟩
  exact ⟨U, F', hU, hgU, hF', fun g hg hgG => hUF g hg (Formalism.FourierDecayAlt.P5.Rad.glev0 hgG)⟩

theorem sgs_pR (ξ : Mt k r × Mt k r) (x : Mat k r) :
    sgs (pR ξ) x = x * Matrix.of ξ.2 * Matrix.of ξ.1 := by
  simp [sgs, pR]

theorem dmin_pR (Bs : RealPlaceData k r Wp Wq) {ξ : Mt k r × Mt k r} (hξ : InR Bs ξ) (x : Mat k r) (l : Fin (r + 2)) :
    Dmin k r Bs.z Bs.z' (x * Matrix.of ξ.2 * Matrix.of ξ.1) l = Dmin k r Bs.z Bs.z' x l := by
  rw [← sgs_pR]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs (inSS_pR Bs hξ) x l

theorem kr_loc (Bs : RealPlaceData k r Wp Wq) (l : Fin (r + 2)) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : ∀ g ∈ GV k r, Dmin k r Bs.z Bs.z' g l ≠ 0 → Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ⊤ F g)
    {C : Set (Mat k r)} (hC : IsCompact C) (hz : ∀ g ∈ GV k r, g ∉ C → F g = 0) :
    ∀ x0 ∈ GV k r, Dmin k r Bs.z Bs.z' x0 l ≠ 0 → Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ⊤ (Kr Bs F) x0 := by
  intro x0 hx0 hD
  set c₀ := Dmin k r Bs.z Bs.z' x0 l with hc₀
  have hc0 : 0 < ‖c₀‖ := norm_pos_iff.mpr hD
  obtain ⟨χD, ⟨hχs, -, -⟩, hχ1, hχsupp⟩ := Formalism.FourierDecayAlt.P.JCTx6.Pos.bump_exists hD
  have hDc : Continuous (fun g : Mat k r => Dmin k r Bs.z Bs.z' g l) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' l).continuous
  set Ft : Mat k r → (Wq →L[ℂ] Wp) := fun g => χD (Dmin k r Bs.z Bs.z' g l) • F g with hFtdef
  have hFt : CkOn ⊤ (GV k r) Ft := by
    intro g0 hg0
    by_cases hmem : Dmin k r Bs.z Bs.z' g0 l ∈ tsupport χD
    · have hne : Dmin k r Bs.z Bs.z' g0 l ≠ 0 := by
        intro h0
        have := (hχsupp _ hmem).1
        rw [h0, norm_zero] at this
        linarith
      obtain ⟨U, f', hU, hgU, hf', he⟩ := hF g0 hg0 hne
      refine ⟨U, fun g => χD (Dmin k r Bs.z Bs.z' g l) • f' g, hU, hgU, ?_, fun g hg hgG => ?_⟩
      · exact ((hχs.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' l)).contDiffOn).smul hf'
      · show χD (Dmin k r Bs.z Bs.z' g l) • F g = χD (Dmin k r Bs.z Bs.z' g l) • f' g
        rw [he g hg hgG]
    · refine ⟨(fun g => Dmin k r Bs.z Bs.z' g l) ⁻¹' (tsupport χD)ᶜ, fun _ => 0,
        (isClosed_tsupport χD).isOpen_compl.preimage hDc, hmem, contDiffOn_const, fun g hg _ => ?_⟩
      show χD (Dmin k r Bs.z Bs.z' g l) • F g = 0
      rw [image_eq_zero_of_notMem_tsupport hg, zero_smul]
  have hzt : ∀ g ∈ GV k r, g ∉ C → Ft g = 0 := fun g hg hgC => by
    show χD (Dmin k r Bs.z Bs.z' g l) • F g = 0
    rw [hz g hg hgC, smul_zero]
  obtain ⟨U, f', hU, hx0U, hf', he⟩ := kr_loc_cpt Bs hFt hC hzt x0 hx0
  set V := {x : Mat k r | dist (Dmin k r Bs.z Bs.z' x l) c₀ < ‖c₀‖ / 4} with hV
  have hVo : IsOpen V := isOpen_lt (hDc.dist continuous_const) continuous_const
  refine ⟨U ∩ V, f', hU.inter hVo, ⟨hx0U, by show dist c₀ c₀ < ‖c₀‖ / 4; rw [dist_self]; positivity⟩,
    hf'.mono Set.inter_subset_left, fun x hx hxG => ?_⟩
  have heq : Kr Bs F x = Kr Bs Ft x := by
    rw [kr_eq, kr_eq]
    refine integral_congr_ae ?_
    filter_upwards [ae_inR Bs] with ξ hξ
    simp only [rho_pR, hFtdef, dmin_pR Bs hξ x l]
    rw [hχ1 _ (le_of_lt hx.2), one_smul]
  rw [heq]
  exact he x hx.1 hxG

end ck

section words

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

open Formalism.FourierDecayAlt.P.JFxDs3 in

theorem rhoW_cont (D : RealPlaceData k r Wp Wq) {A c : ℝ} {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hc : CCle A m F c)
    (hA : 0 ≤ A) (u v : List (Mat k r)) (hu : ∀ X ∈ u, unitLie k r X) (hv : ∀ X ∈ v, unitLie k r X)
    (hl : u.length + v.length ≤ m) {g : Mat k r} (hgG : g ∈ GV k r) :
    ContinuousOn (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) {p : SS k r | D.inSS p} := by
  have hc0 : 0 ≤ c := cc_nonneg hc
  have hwu : ∀ x ∈ lr u v, unitLie k r x.2 := unit_lr' hu hv
  have hwt : LRt ((lr u v).map Prod.fst) := lrt_lr u v
  have hwl : (lr u v).length ≤ m := by rw [length_lr]; exact hl
  have hx : ContinuousOn (fun p => sgs p g) {p : SS k r | D.inSS p} := B6.conjugated_pair_continuous_on D g
  have hxG : ∀ p ∈ {p : SS k r | D.inSS p}, sgs p g ∈ GV k r := fun p hp => B7.sgs_mem D hp hgG
  have hmain : ContinuousOn (fun p => W ((lr u v).map (adM p)) F (sgs p g)) {p : SS k r | D.inSS p} := by
    intro p₀ hp₀
    have hAL : AllLie ((lr u v).map (adM p₀)) := by
      intro y hy
      obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
      exact adM_lie hp₀ (hwu y' hy').1
    have hck : CkOn ((0 : ℕ) : ℕ∞) (GV k r) (W ((lr u v).map (adM p₀)) F) :=
      smooth_on_of_word_derivatives ((lr u v).map (adM p₀)) hAL 0 (ckOn_mono (by simpa using hwl) hc.1)
    have hsec : ContinuousWithinAt (fun p => W ((lr u v).map (adM p₀)) F (sgs p g)) {p : SS k r | D.inSS p} p₀ :=
      ((B6.continuousOn_of_contDiffOn_group hck).comp hx hxG) p₀ hp₀
    let Kf : SS k r → ℝ := fun p => 1 + ((lr u v).map fun x => ‖(adM p x).2‖ + ‖(adM p₀ x).2‖).sum
    let εf : SS k r → ℝ := fun p => ((lr u v).map fun x => ‖(adM p x).2 - (adM p₀ x).2‖).sum
    have hKc : ContinuousOn Kf {p : SS k r | D.inSS p} :=
      continuousOn_const.add (cont_sum _ (fun x p => ‖(adM p x).2‖ + ‖(adM p₀ x).2‖) (lr u v)
        (fun x _ => (adM_cont D x).norm.add continuousOn_const))
    have hεc : ContinuousOn εf {p : SS k r | D.inSS p} :=
      cont_sum _ (fun x p => ‖(adM p x).2 - (adM p₀ x).2‖) (lr u v)
        (fun x _ => ((adM_cont D x).sub continuousOn_const).norm)
    have hε0 : εf p₀ = 0 := by simp [εf]
    let Bf : SS k r → ℝ := fun p => ((lr u v).length : ℝ) * (Kf p ^ m * εf p * c)
    have hBc : ContinuousWithinAt Bf {p : SS k r | D.inSS p} p₀ :=
      continuousWithinAt_const.mul ((((hKc p₀ hp₀).pow m).mul (hεc p₀ hp₀)).mul continuousWithinAt_const)
    have hB0 : Bf p₀ = 0 := by simp [Bf, hε0]
    have hd : Tendsto (fun p => W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g))
        (𝓝[{p : SS k r | D.inSS p}] p₀) (𝓝 0) := by
      have hBt : Tendsto Bf (𝓝[{p : SS k r | D.inSS p}] p₀) (𝓝 0) := by
        have := hBc.tendsto; rwa [hB0] at this
      refine squeeze_zero_norm' ?_ hBt
      filter_upwards [self_mem_nhdsWithin] with p hp
      have hxp := hxG p hp
      have hK1 : 1 ≤ Kf p := le_add_of_nonneg_right (List.sum_nonneg (by
        intro y hy
        obtain ⟨y', _, rfl⟩ := List.mem_map.mp hy
        positivity))
      have hT := tele hc hc0 hK1 (adM p) (adM p₀) (lr u v) [] (by simp)
        (by
          intro x hx
          have hmK := le_sum_map (fun x => ‖(adM p x).2‖ + ‖(adM p₀ x).2‖) (fun _ => by positivity) (lr u v) hx
          have hmε := le_sum_map (fun x => ‖(adM p x).2 - (adM p₀ x).2‖) (fun _ => norm_nonneg _) (lr u v) hx
          refine ⟨rfl, rfl, adM_lie hp (hwu x hx).1, adM_lie hp₀ (hwu x hx).1, ?_, ?_, hmε⟩
          · have := norm_nonneg (adM p₀ x).2
            show ‖(adM p x).2‖ ≤ Kf p
            simp only [Kf]; linarith
          · have := norm_nonneg (adM p x).2
            show ‖(adM p₀ x).2‖ ≤ Kf p
            simp only [Kf]; linarith)
        (by simpa using hwt) (by simpa using hwl) _ hxp
      simp only [List.nil_append] at hT
      have h1 : 1 ≤ gN (sgs p g) ^ A := Real.one_le_rpow (BetaSesquilinearity.gN_ge_one hxp) hA
      calc ‖W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g)‖
          ≤ gN (sgs p g) ^ A * ‖W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g)‖ :=
            le_mul_of_one_le_left (norm_nonneg _) h1
        _ ≤ Bf p := hT
    have hdc : ContinuousWithinAt
        (fun p => W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g))
        {p : SS k r | D.inSS p} p₀ := by
      have e0 : (fun p => W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g)) p₀ = 0 :=
        sub_self _
      unfold ContinuousWithinAt
      rw [e0]
      exact hd
    refine (hdc.add hsec).congr (fun p _ => ?_) ?_
    · simp
    · simp
  show ContinuousOn (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) {p : SS k r | D.inSS p}
  ·
    have e : (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) =
        fun p => B6.Sd D p (W ((lr u v).map (adM p)) F (sgs p g)) := by
      funext p
      rw [B6.rho_eq, dLR_eq, lr_ad]
    rw [e]
    exact (B6.Sd_continuousOn D).clm_apply hmain

theorem rw_rho_bound (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ} (hc : CCle 0 m F c)
    {p : SS k r} (hp : D.inSS p) {B : ℝ} (hB : ∀ X, unitLie k r X → ‖AdR p X‖ ≤ B) (v : List (Mat k r))
    (hv : ∀ X ∈ v, unitLie k r X) (hl : v.length ≤ m) {q : Mat k r} (hq : q ∈ GV k r) :
    ‖Rw v (rho D p F) q‖ ≤ c * B ^ v.length := by
  have e : Rw v (rho D p F) q = rho D p (dLR ([].map (AdL p)) (v.map (AdR p)) F) q :=
    congrFun (Formalism.FourierDecayAlt.P.SandwichRhoAction.dLR_rho D hp [] v F) q
  rw [e]
  refine (Formalism.FourierDecayAlt.P.B7.norm_rho_le D hp _ q).trans ?_
  have hx := Formalism.FourierDecayAlt.P.B7.sgs_mem D hp hq
  have hw : AllLie (lr [] (v.map (AdR p))) := by
    intro x hx'
    simp only [lr, List.map_nil, List.nil_append, List.mem_map] at hx'
    obtain ⟨Y, ⟨X, hX, rfl⟩, rfl⟩ := hx'
    exact inLie_conj (Formalism.FourierDecayAlt.P.JFxDs2.sR_mem hp) (hv X hX).1
  have hB' := bound_scaled hc (lr [] (v.map (AdR p))) (lrt_lr _ _) hw (by rw [length_lr]; simpa using hl) _ hx
  rw [Real.rpow_zero, one_mul, ← Formalism.FourierDecayAlt.P.B4.dLR_eq] at hB'
  refine hB'.trans ?_
  have hpn : pn (lr [] (v.map (AdR p))) = (v.map fun X => ‖AdR p X‖).prod := by
    simp [pn, lr, List.map_map, Function.comp_def]
  rw [hpn, mul_comm]
  have hc0 : 0 ≤ c := cc_nonneg hc
  refine mul_le_mul_of_nonneg_left ?_ hc0
  have key : ∀ l : List ℝ, (∀ x ∈ l, 0 ≤ x ∧ x ≤ B) → 0 ≤ l.prod ∧ l.prod ≤ B ^ l.length := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons x l ih =>
      intro h
      obtain ⟨h0, h1⟩ := h x List.mem_cons_self
      obtain ⟨i0, i1⟩ := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
      refine ⟨by simpa using mul_nonneg h0 i0, ?_⟩
      simp only [List.prod_cons, List.length_cons, pow_succ]
      rw [mul_comm (B ^ l.length) B]
      exact mul_le_mul h1 i1 i0 (h0.trans h1)
  have := key (v.map fun X => ‖AdR p X‖) (by
    intro x hx'
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx'
    exact ⟨norm_nonneg _, hB X (hv X hX)⟩)
  simpa using this.2

theorem rw_rho_zero (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} {C : Set (Mat k r)} (hC : IsClosed C)
    (hz : ∀ g ∈ GV k r, g ∉ C → F g = 0) {p : SS k r} (hp : D.inSS p) (v : List (Mat k r))
    (hv : ∀ X ∈ v, unitLie k r X) {q : Mat k r} (hq : q ∈ GV k r) (hqC : sgs p q ∉ C) :
    Rw v (rho D p F) q = 0 := by
  have e : Rw v (rho D p F) q = rho D p (dLR ([].map (AdL p)) (v.map (AdR p)) F) q :=
    congrFun (Formalism.FourierDecayAlt.P.SandwichRhoAction.dLR_rho D hp [] v F) q
  rw [e]
  have hw : AllLie (lr [] (v.map (AdR p))) := by
    intro x hx'
    simp only [lr, List.map_nil, List.nil_append, List.mem_map] at hx'
    obtain ⟨Y, ⟨X, hX, rfl⟩, rfl⟩ := hx'
    exact inLie_conj (Formalism.FourierDecayAlt.P.JFxDs2.sR_mem hp) (hv X hX).1
  have h0 : dLR ([].map (AdL p)) (v.map (AdR p)) F (sgs p q) = 0 := by
    rw [Formalism.FourierDecayAlt.P.B4.dLR_eq]
    exact W_zero_near _ hw hC.isOpen_compl (fun g hg hgC => hz g hg hgC) _
      (Formalism.FourierDecayAlt.P.B7.sgs_mem D hp hq) hqC
  simp only [rho, h0, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]

theorem kr_maj (Bs : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} {C : Set (Mat k r)} (hC : IsCompact C)
    (hz : ∀ g ∈ GV k r, g ∉ C → F g = 0) {m : ℕ} {c : ℝ} (hc : CCle 0 m F c) {K : Set (Mat k r)} (hK : IsCompact K)
    (hKG : K ⊆ GV k r) :
    ∃ β : Mt k r × Mt k r → ℝ, Integrable β (Bs.μW'.prod Bs.μN) ∧ (∀ ξ, 0 ≤ β ξ) ∧
      ∀ v : List (Mat k r), (∀ X ∈ v, unitLie k r X) → v.length ≤ m → ∀ q ∈ K, ∀ ξ, InR Bs ξ →
        ‖Rw v (rho Bs (pR ξ) F) q‖ ≤ β ξ := by
  classical
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW'
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarN
  set μ := Bs.μW'.prod Bs.μN with hμ
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r Bs.z' Bs.z'_mem Bs.T'_pos
  set φ : Mat k r × Mat k r × Mat k r → Mat k r :=
    fun t => (Hpk k r * t.1ᴴ * Hpk k r) * t.2.1 * (Hpk k r * t.2.2ᴴ * Hpk k r) with hφ
  have hφc : Continuous φ :=
    ((continuous_const.matrix_mul continuous_fst.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
      (continuous_snd.fst) |>.matrix_mul
      ((continuous_const.matrix_mul continuous_snd.snd.matrix_conjTranspose).matrix_mul continuous_const)
  set Kn := φ '' (K ×ˢ C ×ˢ UWset k r Bs.z') with hKn
  have hKnc : IsCompact Kn := (hK.prod (hC.prod hW)).image hφc
  set S' : Set (Mt k r × Mt k r) := {ξ | (Matrix.of ξ.2 : Mat k r) ∈ Kn} with hS'
  have hS'c : IsClosed S' :=
    hKnc.isClosed.preimage (show Continuous (fun ξ : Mt k r × Mt k r => (Matrix.of ξ.2 : Mat k r)) from continuous_snd)
  have hS'm : MeasurableSet S' := hS'c.measurableSet
  have hWm : Bs.μW' Set.univ < ⊤ := by
    have h1 : Bs.μW' {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r Bs.z'} < ⊤ :=
      Bs.haarW'.finite_compact _ hW
    calc Bs.μW' Set.univ ≤ Bs.μW' {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r Bs.z'} +
          Bs.μW' {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r Bs.z'}ᶜ := by
          rw [← Set.union_compl_self {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r Bs.z'}]
          exact measure_union_le _ _
      _ < ⊤ := by
          have h2 : Bs.μW' {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r Bs.z'}ᶜ = 0 := Bs.haarW'.conc
          rw [h2, add_zero]; exact h1
  have hNm : Bs.μN {x : Mt k r | (Matrix.of x : Mat k r) ∈ Kn} < ⊤ := Bs.haarN.finite_compact _ hKnc
  have hS'fin : μ S' < ⊤ := by
    have e : S' = Set.univ ×ˢ {x : Mt k r | (Matrix.of x : Mat k r) ∈ Kn} := by
      ext ξ; simp [hS']
    rw [e, hμ, Measure.prod_prod]
    exact ENNReal.mul_lt_top hWm hNm

  obtain ⟨M1, hM1⟩ := hKnc.exists_bound_of_continuousOn (Formalism.FourierDecayAlt.P.B6.gN_continuous (k := k) (r := r)).continuousOn
  obtain ⟨M2, hM2⟩ := hW.exists_bound_of_continuousOn (Formalism.FourierDecayAlt.P.B6.gN_continuous (k := k) (r := r)).continuousOn
  set B : ℝ := gN (Hpk k r) ^ 2 * (|M1| * |M2|) ^ 2 * ((2 * r + k + 1 : ℕ) : ℝ) + 1 with hBdef
  have hB1 : 1 ≤ B := by
    have : 0 ≤ gN (Hpk k r) ^ 2 * (|M1| * |M2|) ^ 2 * ((2 * r + k + 1 : ℕ) : ℝ) := by positivity
    linarith
  have hc0 : 0 ≤ c := cc_nonneg hc
  set β : Mt k r × Mt k r → ℝ := S'.indicator (fun _ => c * B ^ m) with hβ
  refine ⟨β, (integrableOn_const (μ := μ) (s := S') (C := c * B ^ m) hS'fin.ne).integrable_indicator hS'm,
    fun ξ => Set.indicator_nonneg (fun _ _ => by positivity) ξ, fun v hv hl q hq ξ hξ => ?_⟩
  have hqG : q ∈ GV k r := hKG hq
  have hp := inSS_pR Bs hξ
  by_cases hqC : sgs (pR ξ) q ∈ C
  · have hmem : ξ ∈ S' := by
      show (Matrix.of ξ.2 : Mat k r) ∈ Kn
      rw [sgs_pR] at hqC
      refine ⟨(q, q * (Matrix.of ξ.2 : Mat k r) * (Matrix.of ξ.1 : Mat k r), (Matrix.of ξ.1 : Mat k r)),
        ⟨hq, hqC, hξ.1⟩, ?_⟩
      have hyu : IsUnit q.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hqG
      have hhu : IsUnit (Matrix.of ξ.1 : Mat k r).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hξ.1.1
      simp only [hφ]
      rw [← Formalism.FourierDecayAlt.P.B6.inv_eq_hermitian_form_conjTranspose hqG, ← Formalism.FourierDecayAlt.P.B6.inv_eq_hermitian_form_conjTranspose hξ.1.1]
      rw [show q⁻¹ * (q * (Matrix.of ξ.2 : Mat k r) * (Matrix.of ξ.1 : Mat k r)) * (Matrix.of ξ.1 : Mat k r)⁻¹ =
        (q⁻¹ * q) * (Matrix.of ξ.2 : Mat k r) * ((Matrix.of ξ.1 : Mat k r) * (Matrix.of ξ.1 : Mat k r)⁻¹) by
          simp only [Matrix.mul_assoc]]
      rw [Matrix.nonsing_inv_mul _ hyu, Matrix.mul_nonsing_inv _ hhu, Matrix.one_mul, Matrix.mul_one]
    rw [hβ, Set.indicator_of_mem hmem]

    have hAd : ∀ X, unitLie k r X → ‖AdR (pR ξ) X‖ ≤ B := by
      intro X hX
      set s := (Matrix.of ξ.2 : Mat k r) * (Matrix.of ξ.1 : Mat k r) with hs
      have hsG : s ∈ GV k r := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hξ.2.1 hξ.1.1
      have e : AdR (pR ξ) X = s⁻¹ * X * s := by simp [AdR, sR, pR, hs]
      rw [e]
      have g1 : gN (Matrix.of ξ.2 : Mat k r) ≤ |M1| := by
        have := hM1 _ hmem; rw [Real.norm_eq_abs, abs_of_nonneg (Formalism.FourierDecayAlt.P.B6.gN_nonneg _)] at this
        exact this.trans (le_abs_self _)
      have g2 : gN (Matrix.of ξ.1 : Mat k r) ≤ |M2| := by
        have := hM2 _ hξ.1; rw [Real.norm_eq_abs, abs_of_nonneg (Formalism.FourierDecayAlt.P.B6.gN_nonneg _)] at this
        exact this.trans (le_abs_self _)
      have gs : gN s ≤ |M1| * |M2| :=
        (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _).trans (mul_le_mul g1 g2 (Formalism.FourierDecayAlt.P.B6.gN_nonneg _) (abs_nonneg _))
      have gi : gN s⁻¹ ≤ gN (Hpk k r) ^ 2 * gN s := Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.gN_inv_le hsG
      have gX : gN X ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.gN_unit hX.2
      have h0 := Formalism.FourierDecayAlt.P.B6.gN_nonneg s
      calc ‖s⁻¹ * X * s‖ ≤ gN (s⁻¹ * X * s) := Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.norm_le_gN _
        _ ≤ gN (s⁻¹ * X) * gN s := Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _
        _ ≤ (gN s⁻¹ * gN X) * gN s :=
            mul_le_mul_of_nonneg_right (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _) h0
        _ ≤ (gN (Hpk k r) ^ 2 * (|M1| * |M2|) * ((2 * r + k + 1 : ℕ) : ℝ)) * (|M1| * |M2|) := by
            have a1 : gN s⁻¹ ≤ gN (Hpk k r) ^ 2 * (|M1| * |M2|) :=
              gi.trans (mul_le_mul_of_nonneg_left gs (by positivity))
            exact mul_le_mul (mul_le_mul a1 gX (Formalism.FourierDecayAlt.P.B6.gN_nonneg _) (by positivity)) gs h0 (by positivity)
        _ ≤ B := by rw [hBdef]; nlinarith [sq_nonneg (|M1| * |M2|), Formalism.FourierDecayAlt.P.B6.gN_nonneg (Hpk k r)]
    refine (rw_rho_bound Bs hc hp hAd v hv hl hqG).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 hl) hc0
  · rw [rw_rho_zero Bs hC.isClosed hz hp v hv hqG hqC, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => by positivity) ξ

theorem kr_meas (Bs : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} {m : ℕ} {c : ℝ} (hc : CCle 0 m F c)
    (v : List (Mat k r)) (hv : ∀ X ∈ v, unitLie k r X) (hl : v.length ≤ m) {q : Mat k r} (hq : q ∈ GV k r) :
    AEStronglyMeasurable (fun ξ => Rw v (rho Bs (pR ξ) F) q) (Bs.μW'.prod Bs.μN) := by
  have hpRc : Continuous (fun ξ : Mt k r × Mt k r => pR ξ) := continuous_const.prodMk continuous_id
  have hcont := (rhoW_cont Bs hc le_rfl [] v (by simp) hv (by simpa using hl) hq).comp hpRc.continuousOn
    (fun ξ hξ => inSS_pR Bs hξ)
  have hm := hcont.aestronglyMeasurable (μ := Bs.μW'.prod Bs.μN) (isClosed_InR Bs).measurableSet
  rw [Measure.restrict_eq_self_of_ae_mem (ae_inR Bs)] at hm
  refine hm.congr ?_
  filter_upwards [ae_inR Bs] with ξ hξ
  exact (congrFun (Formalism.FourierDecayAlt.P.SandwichRhoAction.dLR_rho Bs (inSS_pR Bs hξ) [] v F) q).symm

theorem xiP_pR (Bs : RealPlaceData k r Wp Wq) (ξ : Mt k r × Mt k r) :
    Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) = star (psi k r Bs.z' cStd (Matrix.of ξ.2)) := by
  simp only [Formalism.FourierDecayAlt.JF.xiP, pR, Equiv.apply_symm_apply, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z_mem, one_mul]

theorem kr_words (Bs : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn ⊤ (GV k r) F)
    {C : Set (Mat k r)} (hC : IsCompact C) (hz : ∀ g ∈ GV k r, g ∉ C → F g = 0) {m : ℕ} {c : ℝ}
    (hc : CCle 0 m F c) :
    ∀ v : List (Mat k r), (∀ X ∈ v, unitLie k r X) → v.length ≤ m → ∀ y ∈ GV k r,
      Integrable (fun ξ => Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • Rw v (rho Bs (pR ξ) F) y) (Bs.μW'.prod Bs.μN) ∧
      Rw v (Kr Bs F) y = ∫ ξ, Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • Rw v (rho Bs (pR ξ) F) y ∂(Bs.μW'.prod Bs.μN) := by
  classical
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  set μ := Bs.μW'.prod Bs.μN with hμ
  have hpRc : Continuous (fun ξ : Mt k r × Mt k r => pR ξ) := continuous_const.prodMk continuous_id
  have hψm : AEStronglyMeasurable (fun ξ => Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ)) μ :=
    ((Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.continuous_xiP Bs).comp hpRc).aestronglyMeasurable
  have hψ : ∀ ξ, ‖Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ)‖ ≤ 1 := fun ξ => Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.norm_xiP Bs _

  have hint : ∀ v : List (Mat k r), (∀ X ∈ v, unitLie k r X) → v.length ≤ m → ∀ y ∈ GV k r,
      Integrable (fun ξ => Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • Rw v (rho Bs (pR ξ) F) y) μ := by
    intro v hv hl y hy
    obtain ⟨β, hβI, hβ0, hβ⟩ := kr_maj Bs hC hz hc (isCompact_singleton (x := y))
      (Set.singleton_subset_iff.2 hy)
    refine hβI.mono' (hψm.smul (kr_meas Bs hc v hv hl hy)) ?_
    filter_upwards [ae_inR Bs] with ξ hξ
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)).trans (hβ v hv hl y rfl ξ hξ)
  intro v
  induction v with
  | nil =>
    intro _ _ y hy
    refine ⟨hint [] (by simp) (by simp) y hy, ?_⟩
    show Kr Bs F y = _
    rw [kr_eq]
    congr 1
    funext ξ
    rw [xiP_pR]
    rfl
  | cons X v ih =>
    intro hv hl y hy
    refine ⟨hint (X :: v) hv hl y hy, ?_⟩
    have hX : unitLie k r X := hv X List.mem_cons_self
    have hv' : ∀ Y ∈ v, unitLie k r Y := fun Y hY => hv Y (List.mem_cons_of_mem _ hY)
    have hl' : v.length ≤ m := by simp at hl; omega
    set G : Mt k r × Mt k r → Mat k r → (Wq →L[ℂ] Wp) :=
      fun ξ => if InR Bs ξ then Rw v (rho Bs (pR ξ) F) else fun _ => 0 with hGdef
    have hGck : ∀ ξ, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (G ξ) := by
      intro ξ
      by_cases hξ : InR Bs ξ
      · simp only [hGdef, if_pos hξ]
        have e : Rw v (rho Bs (pR ξ) F) = W (lr [] v) (rho Bs (pR ξ) F) := Formalism.FourierDecayAlt.P.B4.dLR_eq [] v _
        rw [e]
        refine smooth_on_of_word_derivatives _ (allLie_lr (by simp) hv') 1 (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top ?_)
        exact ckOn_rho Bs (inSS_pR Bs hξ) hF
      · simp only [hGdef, if_neg hξ]; exact Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.ckOn_zero _
    have hopG : ∀ ξ q, InR Bs ξ → op false X (G ξ) q = Rw (X :: v) (rho Bs (pR ξ) F) q := by
      intro ξ q hξ
      simp only [hGdef, if_pos hξ]
      rfl
    have hopG0 : ∀ ξ q, ¬ InR Bs ξ → op false X (G ξ) q = 0 := by
      intro ξ q hξ
      simp only [hGdef, if_neg hξ, op]
      simp

    set K := (fun t : ℝ => cv false X t y) '' Metric.closedBall (0 : ℝ) 1 with hKdef
    have hK : IsCompact K := (isCompact_closedBall (0 : ℝ) 1).image (Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.cv_continuous false X y)
    have hKG : K ⊆ GV k r := by rintro _ ⟨t, _, rfl⟩; exact cv_mem (b := false) hX.1 hy t
    have hmemK : ∀ t ∈ Metric.ball (0 : ℝ) 1, cv false X t y ∈ K := fun t ht =>
      ⟨t, Metric.ball_subset_closedBall ht, rfl⟩
    obtain ⟨β, hβI, hβ0, hβ⟩ := kr_maj Bs hC hz hc hK hKG
    have key := step_loc (μ := μ) (b := false) hX.1 (fun ξ => Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ)) hψ hψm G hGck hy
      one_pos
      (fun t ht => by
        refine (kr_meas Bs hc v hv' hl' (cv_mem (b := false) hX.1 hy t)).congr ?_
        filter_upwards [ae_inR Bs] with ξ hξ
        simp only [hGdef, if_pos hξ])
      (by
        refine (kr_meas Bs hc (X :: v) hv hl hy).congr ?_
        filter_upwards [ae_inR Bs] with ξ hξ
        rw [hopG ξ y hξ])
      β hβI
      (fun ξ => by
        by_cases hξ : InR Bs ξ
        · simp only [hGdef, if_pos hξ]
          have hyK : y ∈ K := by
            have := hmemK 0 (Metric.mem_ball_self one_pos); rwa [cv_zero] at this
          exact hβ v hv' hl' y hyK ξ hξ
        · simp only [hGdef, if_neg hξ, norm_zero]; exact hβ0 ξ)
      (fun t ht ξ => by
        by_cases hξ : InR Bs ξ
        · rw [hopG ξ _ hξ]; exact hβ (X :: v) hv hl _ (hmemK t ht) ξ hξ
        · rw [hopG0 ξ _ hξ, norm_zero]; exact hβ0 ξ)
      (Rw v (Kr Bs F))
      (fun t ht => by
        rw [(ih hv' hl' _ (cv_mem (b := false) hX.1 hy t)).2]
        refine integral_congr_ae ?_
        filter_upwards [ae_inR Bs] with ξ hξ
        simp only [hGdef, if_pos hξ])
    show op false X (Rw v (Kr Bs F)) y = _
    rw [key]
    refine integral_congr_ae ?_
    filter_upwards [ae_inR Bs] with ξ hξ
    rw [hopG ξ y hξ]

end words

section clm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion in
theorem foldT_clm (L : E →L[ℂ] E) (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (f : Mat k r → E)
    {g : Mat k r} (hg : g ∈ GV k r) (hf : Loc (ts.length : ℕ∞) f g) (hLf : Loc (ts.length : ℕ∞) (fun x => L (f x)) g) :
    foldT ts (fun x => L (f x)) g = L (foldT ts f g) := by
  rw [expand_eq ts _ g hg hLf, expand_eq ts f g hg hf, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun cw hcw => ?_
  have hw := expand_words ts cw hcw
  simp only [Function.comp_apply, map_smul]
  rw [Formalism.FourierDecayAlt.P.PBN.JA.rw_clm L cw.2 (fun X hX => (hw.1 X hX).1) f g hg (loc_mono (by exact_mod_cast hw.2) hf)]

theorem qminor_foldT {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (g : Mat k r) :
    qminorOp (EabH (Hpk k r)) a b u f g =
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)) f g := by
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  simp only [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT, List.map_ofFn]
  rfl

open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion in
theorem qminor_clm (L : E →L[ℂ] E) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E)
    {g : Mat k r} (hg : g ∈ GV k r) (hf : Loc (t : ℕ∞) f g) (hLf : Loc (t : ℕ∞) (fun x => L (f x)) g) :
    qminorOp (EabH (Hpk k r)) a b u (fun x => L (f x)) g = L (qminorOp (EabH (Hpk k r)) a b u f g) := by
  rw [qminor_foldT, qminor_foldT, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_smul, foldT_clm L _ f hg (by simpa using hf) (by simpa using hLf)]

theorem AAop_clm (L : E →L[ℂ] E) (m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Mat k r → E) {g : Mat k r} (hg : g ∈ GV k r)
    (hf : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc (m : ℕ∞) f g) (hLf : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc (m : ℕ∞) (fun x => L (f x)) g) :
    C3.AAop k r m hm u (fun x => L (f x)) g = L (C3.AAop k r m hm u f g) := by
  simp only [C3.AAop, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [map_smul, qminor_clm L _ _ u f hg hf hLf]
  · simp

theorem AAvop_clm (L : E →L[ℂ] E) (m : ℕ) (hm : m ≤ r) (ell : ℂ) (f : Mat k r → E) {g : Mat k r}
    (hg : g ∈ GV k r) (hf : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc (m : ℕ∞) f g)
    (hLf : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc (m : ℕ∞) (fun x => L (f x)) g) :
    C3.AAvop k r m hm ell (fun x => L (f x)) g = L (C3.AAvop k r m hm ell f g) := by
  simp only [C3.AAvop, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [map_smul, qminor_clm L _ _ _ f hg hf hLf]
  · simp

end clm

section rhoAA

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

open Formalism.FourierDecayAlt.P.PBN.JA in

theorem rho_AA (Bs : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn ⊤ (GV k r) F) (m : ℕ)
    (hm : m ≤ r) (u ell : ℂ) {p : SS k r} (hp : Bs.inSS p) {g : Mat k r} (hg : g ∈ GV k r) :
    rho Bs p (C3.AAop k r m hm u F) g = C3.AAop k r m hm u (rho Bs p F) g ∧
      rho Bs p (C3.AAvop k r m hm ell F) g = C3.AAvop k r m hm ell (rho Bs p F) g := by
  set s : Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with hsdef
  set s' : Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hs'def
  have hs : s ∈ Sset k r Bs.z :=
    ⟨_, Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.1, _, (Formalism.QuantumDeterminants.nSubgroup k r).2.2 _ hp.2.1, rfl⟩
  have hs' : s' ∈ Sset k r Bs.z' :=
    (Formalism.QuantumDeterminants.sGroup k r Bs.z' Bs.z'_mem).2.1 _ ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw Bs.z', _, hp.2.2.2, by simp⟩ _
      ⟨_, hp.2.2.1, 1, (Formalism.QuantumDeterminants.nSubgroup k r).1, by simp⟩
  have hsG := Formalism.FourierDecayAlt.P.BetaSesquilinearity.Sset_sub hs
  have hs'G := Formalism.FourierDecayAlt.P.BetaSesquilinearity.Sset_sub hs'
  have hsgs : ∀ y : Mat k r, sgs p y = s * y * s' := by
    intro y; simp [sgs, hsdef, hs'def, Matrix.mul_assoc]
  have hSm : SmoothOnH (Hpk k r) F := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hc, he⟩ := hF g₀ hg₀
    exact ⟨U, f', hU, hgU, hc, fun x hx hxG => he x hx hxG⟩
  have hX0 := Formalism.FourierDecayAlt.P.operators_commute_translations' (Wq →L[ℂ] Wp) k r Bs.z Bs.z' m hm u ell F Bs.z_mem Bs.z'_mem hSm
    s hs s' hs' g hg
  set L := postL (Bs.π (Matrix.of p.1.1)) (Bs.π' (Matrix.of p.2.1)⁻¹) with hL
  have e2 : rho Bs p F = fun x => L (F (s * x * s')) := by
    funext x; simp only [rho, hsgs, hL, postL_apply]
  have hloc : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc (m : ℕ∞) (fun x => F (s * x * s')) g :=
    loc_transl hsG hs'G (loc_of_ck hF (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hsG hg) hs'G) _)
  refine ⟨?_, ?_⟩
  · have e1 : rho Bs p (C3.AAop k r m hm u F) g = L (C3.AAop k r m hm u F (s * g * s')) := by
      simp only [rho, hsgs, hL, postL_apply]
    rw [e1, e2, ← hX0.1, AAop_clm L m hm u _ hg hloc (loc_post L hloc)]
  · have e1 : rho Bs p (C3.AAvop k r m hm ell F) g = L (C3.AAvop k r m hm ell F (s * g * s')) := by
      simp only [rho, hsgs, hL, postL_apply]
    rw [e1, e2, ← hX0.2, AAvop_clm L m hm ell _ hg hloc (loc_post L hloc)]

theorem integrable_csmul {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → (Wq →L[ℂ] Wp)} (c : ℂ)
    (hf : Integrable f μ) : Integrable (fun x => c • f x) μ := hf.smul c

theorem foldT_under (Bs : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn ⊤ (GV k r) F)
    {C : Set (Mat k r)} (hC : IsCompact C) (hz : ∀ g ∈ GV k r, g ∉ C → F g = 0) {M : ℕ} {c : ℝ}
    (hc : CCle 0 M F c) (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (hts : ts.length ≤ M)
    {y : Mat k r} (hy : y ∈ GV k r) :
    Integrable (fun ξ => Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT ts (rho Bs (pR ξ) F) y)
      (Bs.μW'.prod Bs.μN) ∧
    Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT ts (Kr Bs F) y =
      ∫ ξ, Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT ts (rho Bs (pR ξ) F) y ∂(Bs.μW'.prod Bs.μN) := by
  classical
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  set μ := Bs.μW'.prod Bs.μN with hμ
  have hW := kr_words Bs hF hC hz hc
  have hwd : ∀ cw ∈ Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r ts, (∀ X ∈ cw.2, unitLie k r X) ∧ cw.2.length ≤ M :=
    fun cw hcw => ⟨(Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_words ts cw hcw).1,
      (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_words ts cw hcw).2.trans hts⟩

  have hae : ∀ᵐ ξ ∂μ, Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT ts (rho Bs (pR ξ) F) y =
      ((Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r ts).map fun cw =>
        cw.1 • (Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • Rw cw.2 (rho Bs (pR ξ) F) y)).sum := by
    filter_upwards [ae_inR Bs] with ξ hξ
    rw [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_eq ts _ y hy
      (Formalism.FourierDecayAlt.P.PBN.JA.loc_of_ck (ckOn_rho Bs (inSS_pR Bs hξ) hF) hy _), List.smul_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun cw _ => ?_
    simp only [Function.comp_apply]
    rw [smul_comm]

  have hlist : ∀ L : List (ℂ × List (Mat k r)), (∀ cw ∈ L, (∀ X ∈ cw.2, unitLie k r X) ∧ cw.2.length ≤ M) →
      Integrable (fun ξ => (L.map fun cw => cw.1 • (Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • Rw cw.2 (rho Bs (pR ξ) F) y)).sum) μ ∧
      ∫ ξ, (L.map fun cw => cw.1 • (Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • Rw cw.2 (rho Bs (pR ξ) F) y)).sum ∂μ =
        (L.map fun cw => cw.1 • Rw cw.2 (Kr Bs F) y).sum := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons cw L ih =>
      intro h
      obtain ⟨hI, hv⟩ := hW cw.2 (h cw List.mem_cons_self).1 (h cw List.mem_cons_self).2 y hy
      obtain ⟨hI', hv'⟩ := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
      simp only [List.map_cons, List.sum_cons]
      have h1 : Integrable (fun ξ => cw.1 • (Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • Rw cw.2 (rho Bs (pR ξ) F) y)) μ :=
        hI.smul cw.1
      refine ⟨h1.add hI', ?_⟩
      rw [integral_add h1 hI', integral_smul, hv', hv]
  obtain ⟨hLI, hLE⟩ := hlist (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r ts) hwd
  refine ⟨hLI.congr (hae.mono fun ξ h => h.symm), ?_⟩
  have hLocK : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc (ts.length : ℕ∞) (Kr Bs F) y :=
    Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_mono le_top (kr_loc_cpt Bs hF hC hz y hy)
  rw [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_eq ts _ y hy hLocK, ← hLE]
  exact (integral_congr_ae hae).symm

theorem qminor_under (Bs : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn ⊤ (GV k r) F)
    {C : Set (Mat k r)} (hC : IsCompact C) (hz : ∀ g ∈ GV k r, g ∉ C → F g = 0) {t : ℕ}
    (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) {y : Mat k r} (hy : y ∈ GV k r) :
    Integrable (fun ξ => Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • qminorOp (EabH (Hpk k r)) a b u (rho Bs (pR ξ) F) y)
      (Bs.μW'.prod Bs.μN) ∧
    qminorOp (EabH (Hpk k r)) a b u (Kr Bs F) y =
      ∫ ξ, Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • qminorOp (EabH (Hpk k r)) a b u (rho Bs (pR ξ) F) y ∂(Bs.μW'.prod Bs.μN) := by
  classical
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hF hC hz 0 t
  have hT := fun σ : Equiv.Perm (Fin t) => foldT_under Bs hF hC hz hc
    (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)) (by simp) hy
  have e : ∀ ξ, Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • qminorOp (EabH (Hpk k r)) a b u (rho Bs (pR ξ) F) y =
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) •
        Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j))
          (rho Bs (pR ξ) F) y) := by
    intro ξ
    rw [qminor_foldT, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_comm]
  have hI : Integrable (fun ξ => ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT
        (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)) (rho Bs (pR ξ) F) y))
      (Bs.μW'.prod Bs.μN) :=
    integrable_finset_sum _ fun σ _ => integrable_csmul _ (hT σ).1
  refine ⟨by simp only [e]; exact hI, ?_⟩
  simp only [e]
  rw [integral_finsetSum _ fun σ _ => integrable_csmul _ (hT σ).1, qminor_foldT]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_smul, (hT σ).2]

theorem kr_AA_cpt (Bs : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn ⊤ (GV k r) F)
    {C : Set (Mat k r)} (hC : IsCompact C) (hz : ∀ g ∈ GV k r, g ∉ C → F g = 0) (m : ℕ) (hm : m ≤ r) (u ell : ℂ)
    {y : Mat k r} (hy : y ∈ GV k r) :
    Kr Bs (C3.AAop k r m hm u F) y = C3.AAop k r m hm u (Kr Bs F) y ∧
      Kr Bs (C3.AAvop k r m hm ell F) y = C3.AAvop k r m hm ell (Kr Bs F) y := by
  classical
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hK : ∀ G : Mat k r → (Wq →L[ℂ] Wp), Kr Bs G y =
      ∫ ξ, Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • rho Bs (pR ξ) G y ∂(Bs.μW'.prod Bs.μN) := by
    intro G
    rw [kr_eq]
    congr 1
    funext ξ
    rw [xiP_pR]
  refine ⟨?_, ?_⟩
  · rw [hK]
    have hae : ∀ᵐ ξ ∂(Bs.μW'.prod Bs.μN), Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • rho Bs (pR ξ) (C3.AAop k r m hm u F) y =
        ∑ c : Fin m → Fin (2 * r + k + 1), (if StrictMono c then
          (Matrix.of fun a l : Fin m => herm (Hpk k r) (y *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))).det •
            (Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • qminorOp (EabH (Hpk k r)) (C3.xR k r m hm) c u (rho Bs (pR ξ) F) y)
          else 0) := by
      filter_upwards [ae_inR Bs] with ξ hξ
      rw [(rho_AA Bs hF m hm u 0 (inSS_pR Bs hξ) hy).1]
      simp only [C3.AAop, Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs
      · rw [smul_comm]
      · simp
    rw [integral_congr_ae hae, integral_finsetSum]
    · simp only [C3.AAop]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs
      · rw [integral_smul, ← (qminor_under Bs hF hC hz _ c u hy).2]
      · simp
    · intro c _
      split_ifs
      · exact integrable_csmul _ (qminor_under Bs hF hC hz _ c u hy).1
      · exact integrable_zero _ _ _
  · rw [hK]
    have hae : ∀ᵐ ξ ∂(Bs.μW'.prod Bs.μN), Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • rho Bs (pR ξ) (C3.AAvop k r m hm ell F) y =
        ∑ B : Fin m → Fin (2 * r + k + 1), (if StrictMono (fun l => C3.keyS k r (B l)) then
          (Matrix.of fun a l : Fin m => (y⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (B l)).det •
            (Formalism.FourierDecayAlt.JF.xiP Bs (pR ξ) • qminorOp (EabH (Hpk k r)) B (C3.sR k r m hm) (ell + (m : ℂ) - 1)
              (rho Bs (pR ξ) F) y)
          else 0) := by
      filter_upwards [ae_inR Bs] with ξ hξ
      rw [(rho_AA Bs hF m hm 0 ell (inSS_pR Bs hξ) hy).2]
      simp only [C3.AAvop, Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs
      · rw [smul_comm]
      · simp
    rw [integral_congr_ae hae, integral_finsetSum]
    · simp only [C3.AAvop]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs
      · rw [integral_smul, ← (qminor_under Bs hF hC hz c _ _ hy).2]
      · simp
    · intro c _
      split_ifs
      · exact integrable_csmul _ (qminor_under Bs hF hC hz c _ _ hy).1
      · exact integrable_zero _ _ _

end rhoAA

end right

end Formalism.FourierDecayAlt.P.PBG
