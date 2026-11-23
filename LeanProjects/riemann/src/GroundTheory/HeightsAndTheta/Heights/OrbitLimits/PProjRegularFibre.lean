import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
import ReciprocityTheory.AnalyticForms.PotentialTheory.PushAFinsumInter
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegular
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegularFibre
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}

omit [∀ k, Fintype (ι k)] in

theorem segre_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ∃ c : ℂ, c ≠ 0 ∧ segre z = c • (segre z' : ((k : K) → ι k) → ℂ) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ => hc k, ?_⟩
  funext i
  simp [segre, Finset.prod_mul_distrib]

theorem segre_lift_eq_smul {e : ℕ} (R : AnLogRes P J e) (x₀ : R.X) {x : R.X} (hx : x ∈ R.U x₀) :
    ∃ c : ℂ, c ≠ 0 ∧ segre (R.lift x x) = c • (segre (R.lift x₀ x) : ((k : K) → ι k) → ℂ) :=
  segre_of_sameOrbit (R.compat x x₀ x ⟨R.mem_U x, hx⟩)

theorem continuousOn_segre_lift {e n : ℕ} (R : AnLogRes P J e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x₀ : R.X) :
    ContinuousOn (fun x => Ψ (segre (R.lift x₀ x))) (R.U x₀) := by
  have hl : ContinuousOn (fun x => R.lift x₀ x) (R.U x₀) :=
    continuousOn_pi.mpr fun p => continuousOn_lift R x₀ p
  have hs : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
    continuous_pi fun i => continuous_finsetProd Finset.univ fun k _ => continuous_apply _
  exact (LinearMap.continuous_of_finiteDimensional Ψ).comp_continuousOn (hs.comp_continuousOn hl)

theorem isClosed_projFibre {n : ℕ} (R : AnLogRes P J (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {V : Set R.X} (hV : IsClosed V)
    (hΨ : ∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) (y : Fin n → ℂ) :
    IsClosed {x | x ∈ V ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ projCoord R Ψ x = y} := by
  refine isClosed_of_closure_subset fun x hx => ?_
  set F := {x | x ∈ V ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ projCoord R Ψ x = y} with hFdef
  have hxV : x ∈ V := closure_minimal (fun z hz => hz.1) hV hx
  set w : R.X → Fin (n + 1) → ℂ := fun z => Ψ (segre (R.lift x z)) with hwdef
  have hw : ContinuousAt w x :=
    (continuousOn_segre_lift R Ψ x).continuousAt ((R.isOpen_U x).mem_nhds (R.mem_U x))
  set h : R.X → Fin n → ℂ := fun z i => w z i.succ - y i * w z 0 with hhdef
  have hh : ContinuousAt h x := continuousAt_pi.mpr fun i =>
    ((continuous_apply _).continuousAt.comp hw).sub
      (continuousAt_const.mul ((continuous_apply _).continuousAt.comp hw))

  have hev : ∀ᶠ z in 𝓝[F] x, h z = 0 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds ((R.isOpen_U x).mem_nhds (R.mem_U x))] with z hz hzU
    obtain ⟨c, hc, hcz⟩ := segre_lift_eq_smul R x hzU
    have h0 : Ψ (segre (R.lift z z)) = c • w z := by simp [w, hcz]
    have hw0 : w z 0 ≠ 0 := fun h' => hz.2.1 (by rw [h0]; simp [h'])
    funext i
    have hi := congrFun hz.2.2 i
    simp only [projCoord, h0, Pi.smul_apply, smul_eq_mul] at hi
    rw [mul_div_mul_left _ _ hc, div_eq_iff hw0] at hi
    simp [h, hi]
  have : (𝓝[F] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hlim : h x = 0 :=
    tendsto_nhds_unique (hh.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hev.mono fun z hz => hz.symm))
  have hi : ∀ i : Fin n, w x i.succ = y i * w x 0 := fun i => by
    have := congrFun hlim i
    simpa [h, sub_eq_zero] using this
  have hw0 : w x 0 ≠ 0 := by
    intro h0
    apply hΨ x hxV
    funext i
    cases i using Fin.cases with
    | zero => simpa [w] using h0
    | succ i => simpa [w, h0] using hi i
  refine ⟨hxV, hw0, funext fun i => ?_⟩
  show w x i.succ / w x 0 = y i
  rw [div_eq_iff hw0]
  exact hi i

theorem ProjRegularFibre.of_found (hReg : ProjRegular.Statement) : ProjRegularFibre.Statement := by
  intro K _ ι _ P J n R Ψ V BV hBV hV hΨ
  have hAn := (hReg K ι P J n R Ψ V BV hBV).2.1
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  set q : V → Fin n → ℂ := projCoord R Ψ ∘ Subtype.val with hqdef
  set f : Fin BV.n → (Fin n → ℂ) → Fin n → ℂ := fun j => q ∘ (BV.chart j).symm with hfdef

  set C : Fin BV.n → Set (Fin n → ℂ) := fun j => {u | u ∈ (BV.chart j).target ∧
      Ψ (segre (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm u).1)) 0 ≠ 0 ∧
      LinearMap.det (fderiv ℂ (f j) u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0} with hCdef
  have hnull : ∀ j, volume (f j '' C j) = 0 := fun j => by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun u => (fderiv ℂ (f j) u).restrictScalars ℝ) (fun u hu => ?_) (fun u hu => ?_)
    · have ha := hAn _ hu.2.1 j ((BV.chart j).map_target hu.1)
      rw [(BV.chart j).right_inv hu.1] at ha
      exact (ha.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · show LinearMap.det ((fderiv ℂ (f j) u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ) = 0
      rw [ReciprocityTheory.AnForm.A.det_restrictScalars_real, hu.2.2, map_zero]
  filter_upwards [compl_mem_ae_iff.mpr (measure_iUnion_null hnull)] with y hy
  set F : Set V := Subtype.val ⁻¹'
    {x | x ∈ V ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ projCoord R Ψ x = y} with hFdef
  have hFc : IsCompact F :=
    ((isClosed_projFibre R Ψ hV hΨ y).preimage continuous_subtype_val).isCompact

  have hFreg : ∀ x ∈ F, x ∈ projRegular R Ψ BV := by
    intro x hx
    refine ⟨hx.2.1, fun j hj hd => hy (Set.mem_iUnion.mpr ⟨j, BV.chart j x,
      ⟨(BV.chart j).map_source hj, ?_, hd⟩, ?_⟩)⟩
    · rw [(BV.chart j).left_inv hj]; exact hx.2.1
    · show projCoord R Ψ ((BV.chart j).symm (BV.chart j x)).1 = y
      rw [(BV.chart j).left_inv hj]; exact hx.2.2

  have hloc : ∀ x ∈ F, ∃ N ∈ 𝓝 x, Set.InjOn q N := by
    intro x hx
    obtain ⟨j, hj⟩ := BV.cover x
    obtain ⟨W, hWo, hxW, hinj⟩ :=
      pushA_locInj (hAn x (hFreg x hx).1 j hj) ((hFreg x hx).2 j hj)
    refine ⟨(BV.chart j).source ∩ BV.chart j ⁻¹' W,
      ((BV.chart j).isOpen_inter_preimage hWo).mem_nhds ⟨hj, hxW⟩, fun a ha b hb hab => ?_⟩
    refine (BV.chart j).injOn ha.1 hb.1 (hinj ha.2 hb.2 ?_)
    show projCoord R Ψ ((BV.chart j).symm (BV.chart j a)).1 =
      projCoord R Ψ ((BV.chart j).symm (BV.chart j b)).1
    rw [(BV.chart j).left_inv ha.1, (BV.chart j).left_inv hb.1]
    exact hab
  choose! N hN hNinj using hloc
  obtain ⟨t, htF, hcov⟩ := hFc.elim_nhds_subcover N hN
  refine t.finite_toSet.subset fun z hz => ?_
  have hzy : projCoord R Ψ z.1 = y := hz.1
  have hzF : z ∈ F := ⟨z.2, hz.2.1, hzy⟩
  obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.mp (hcov hzF)
  have hxF := htF x hxt
  have : z = x := hNinj x hxF hzx (mem_of_mem_nhds (hN x hxF)) (hzy.trans hxF.2.2.symm)
  exact this ▸ hxt

end GroundTheory.Heights₂.Heights.Targets
