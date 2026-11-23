import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialGaugeOfGaugeIdentitySlices
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TopsChoicePartA
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.AmpTensorDSdNonemptyOfSubsingleton
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily

section PartG1

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open scoped InnerProductSpace

section SchurLemma

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def tent (x δ : ℝ) (t : ℝ) : ℝ := max 0 (1 - |t - x| / δ)

theorem tent_cont (x δ : ℝ) : Continuous (tent x δ) := by
  unfold tent
  fun_prop

theorem tent_self (x δ : ℝ) : tent x δ x = 1 := by simp [tent]

theorem tent_mul {x y : ℝ} (h : x ≠ y) (t : ℝ) : tent x (|x - y| / 2) t * tent y (|x - y| / 2) t = 0 := by
  have hd : 0 < |x - y| / 2 := by have := abs_pos.2 (sub_ne_zero.2 h); linarith
  by_cases h1 : |x - y| / 2 ≤ |t - x|
  · have : tent x (|x - y| / 2) t = 0 := by
      unfold tent
      apply max_eq_left
      have := (one_le_div hd).2 h1
      linarith
    rw [this, zero_mul]
  · have h2 : |x - y| / 2 ≤ |t - y| := by
      by_contra h2
      have h1 := not_le.1 h1
      have h2 := not_le.1 h2
      have : |x - y| ≤ |t - x| + |t - y| := by
        have e : x - y = (t - y) - (t - x) := by ring
        rw [e]
        have := abs_sub (t - y) (t - x)
        linarith
      linarith
    have : tent y (|x - y| / 2) t = 0 := by
      unfold tent
      apply max_eq_left
      have := (one_le_div hd).2 h2
      linarith
    rw [this, mul_zero]

theorem schur_selfAdjoint [Nontrivial H] (𝒮 : Set (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ U ∈ 𝒮, ∀ v ∈ S, U v ∈ S) → S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ U ∈ 𝒮, Commute A U) :
    ∃ a : ℝ, A = algebraMap ℝ (H →L[ℂ] H) a := by
  obtain ⟨a, ha⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) A hA
  have hsub : ∀ y ∈ spectrum ℝ A, y = a := by
    intro y hy
    by_contra hne
    set δ := |y - a| / 2 with hδ
    set F := cfc (tent y δ) A with hF
    set G := cfc (tent a δ) A with hG
    have hFG : F * G = 0 := by
      rw [hF, hG, ← cfc_mul (tent y δ) (tent a δ) A (tent_cont _ _).continuousOn (tent_cont _ _).continuousOn]
      have : (fun t => tent y δ t * tent a δ t) = fun _ => (0 : ℝ) := by
        funext t; exact tent_mul hne t
      rw [this, cfc_const_zero]
    have hne0 : ∀ x ∈ spectrum ℝ A, cfc (tent x δ) A ≠ 0 := by
      intro x hx h0
      have h1 : tent x δ x ∈ spectrum ℝ (cfc (tent x δ) A) := by
        rw [cfc_map_spectrum (tent x δ) A hA (tent_cont _ _).continuousOn]
        exact ⟨x, hx, rfl⟩
      rw [h0, spectrum.zero_eq, tent_self] at h1
      exact one_ne_zero h1
    have hGc : ∀ U ∈ 𝒮, Commute G U := fun U hU => (hc U hU).cfc_real _
    set S : Submodule ℂ H := (LinearMap.range (G : H →ₗ[ℂ] H)).topologicalClosure with hS
    have hSinv : ∀ U ∈ 𝒮, ∀ v ∈ S, U v ∈ S := by
      intro U hU v hv
      have hv' : v ∈ closure ((LinearMap.range (G : H →ₗ[ℂ] H)) : Set H) := hv
      refine map_mem_closure U.continuous hv' ?_
      rintro _ ⟨w, rfl⟩
      refine ⟨U w, ?_⟩
      have := congrArg (fun T : H →L[ℂ] H => T w) (hGc U hU).eq
      exact this
    have hSk : S ≤ LinearMap.ker (F : H →ₗ[ℂ] H) := by
      refine Submodule.topologicalClosure_minimal _ ?_ F.isClosed_ker
      rintro _ ⟨w, rfl⟩
      have := congrArg (fun T : H →L[ℂ] H => T w) hFG
      exact this
    rcases hirr S (Submodule.isClosed_topologicalClosure _) hSinv with h | h
    · apply hne0 a ha
      ext w
      have : G w ∈ S := Submodule.le_topologicalClosure _ ⟨w, rfl⟩
      rw [h] at this
      simpa using this
    · apply hne0 y hy
      ext w
      have : w ∈ S := by rw [h]; trivial
      exact hSk this
  refine ⟨a, ?_⟩
  calc A = cfc (id : ℝ → ℝ) A := (cfc_id ℝ A hA).symm
    _ = cfc (fun _ : ℝ => a) A := cfc_congr fun y hy => hsub y hy
    _ = algebraMap ℝ (H →L[ℂ] H) a := cfc_const a A hA

theorem schur_general [Nontrivial H] (𝒮 : Set (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ U ∈ 𝒮, ∀ v ∈ S, U v ∈ S) → S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hc : ∀ U ∈ 𝒮, Commute A U) (hc' : ∀ U ∈ 𝒮, Commute A (star U)) :
    ∃ z : ℂ, ∀ v, A v = z • v := by
  have hs : ∀ U ∈ 𝒮, Commute (star A) U := fun U hU => by
    have := (hc' U hU).star_star
    rwa [star_star] at this
  obtain ⟨a, ha⟩ := schur_selfAdjoint 𝒮 hirr (A + star A) (IsSelfAdjoint.add_star_self A)
    (fun U hU => (hc U hU).add_left (hs U hU))
  have hsa : IsSelfAdjoint (Complex.I • (A - star A)) := by
    rw [isSelfAdjoint_iff, star_smul, star_sub, star_star]
    simp only [RCLike.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]
  obtain ⟨b, hb⟩ := schur_selfAdjoint 𝒮 hirr (Complex.I • (A - star A)) hsa
    (fun U hU => ((hc U hU).sub_left (hs U hU)).smul_left _)
  refine ⟨((a : ℂ) - Complex.I * b) / 2, fun v => ?_⟩
  have h1 : A v + star A v = (a : ℂ) • v := by
    have := congrArg (fun T : H →L[ℂ] H => T v) ha
    simpa [Algebra.algebraMap_eq_smul_one] using this
  have h2 : Complex.I • (A v - star A v) = (b : ℂ) • v := by
    have := congrArg (fun T : H →L[ℂ] H => T v) hb
    simpa [Algebra.algebraMap_eq_smul_one] using this
  have h3 : A v - star A v = -(Complex.I * b) • v := by
    have : A v - star A v = (-Complex.I) • (Complex.I • (A v - star A v)) := by
      rw [smul_smul]; simp
    rw [this, h2, smul_smul]; ring_nf
  have h4 : (2 : ℂ) • A v = ((a : ℂ) - Complex.I * b) • v := by
    have : (2 : ℂ) • A v = (A v + star A v) + (A v - star A v) := by rw [two_smul]; abel
    rw [this, h1, h3, ← add_smul]; ring_nf
  have h5 : A v = (2 : ℂ)⁻¹ • ((2 : ℂ) • A v) := by rw [smul_smul]; simp
  rw [h5, h4, smul_smul]
  congr 1
  ring

end SchurLemma

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartG1

section PartG2

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

section Ortho

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure SqRep (μ : Measure G) (σ : G → (H →L[ℂ] H)) : Prop where
  one : σ 1 = 1
  mul : ∀ a b, σ (a * b) = (σ a).comp (σ b)
  iso : ∀ g v, ‖σ g v‖ = ‖v‖
  cont : ∀ v, Continuous fun g => σ g v
  irr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤
  l2 : ∀ v w : H, MemLp (fun g => ⟪w, σ g v⟫_ℂ) 2 μ

variable {μ : Measure G} {σ : G → (H →L[ℂ] H)}

namespace SqRep

theorem inner_map (h : SqRep μ σ) (g : G) (x y : H) : ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (σ g : H →ₗ[ℂ] H) (h.iso g)).inner_map_map x y

theorem mul_inv_apply (h : SqRep μ σ) (g : G) (x : H) : σ g (σ g⁻¹ x) = x := by
  have := congrArg (fun T : H →L[ℂ] H => T x) (h.mul g g⁻¹)
  simp only [mul_inv_cancel, h.one] at this
  exact this.symm

theorem inner_inv (h : SqRep μ σ) (g : G) (x y : H) : ⟪σ g⁻¹ x, y⟫_ℂ = ⟪x, σ g y⟫_ℂ := by
  rw [← h.inner_map g (σ g⁻¹ x) y, h.mul_inv_apply]

def T (h : SqRep μ σ) (w : H) : H →ₗ[ℂ] Lp ℂ 2 μ where
  toFun v := (h.l2 v w).toLp _
  map_add' v v' := by
    apply Lp.ext
    filter_upwards [(h.l2 (v + v') w).coeFn_toLp, (h.l2 v w).coeFn_toLp, (h.l2 v' w).coeFn_toLp,
      Lp.coeFn_add ((h.l2 v w).toLp _) ((h.l2 v' w).toLp _)] with g h1 h2 h3 h4
    rw [h1, h4, Pi.add_apply, h2, h3, map_add, inner_add_right]
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [(h.l2 (c • v) w).coeFn_toLp, (h.l2 v w).coeFn_toLp,
      Lp.coeFn_smul c ((h.l2 v w).toLp _)] with g h1 h2 h4
    rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h2, map_smul, inner_smul_right, smul_eq_mul]

theorem T_ae (h : SqRep μ σ) (w v : H) : (h.T w v : G → ℂ) =ᵐ[μ] fun g => ⟪w, σ g v⟫_ℂ :=
  (h.l2 v w).coeFn_toLp

theorem T_cont (h : SqRep μ σ) (w : H) : Continuous (h.T w) := by
  refine LinearMap.continuous_of_seq_closed_graph (h.T w) fun u x y hu hy => ?_
  have hm : TendstoInMeasure μ (fun n => ((h.T w (u n) : Lp ℂ 2 μ) : G → ℂ)) atTop (y : G → ℂ) :=
    tendstoInMeasure_of_tendsto_Lp hy
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  apply Lp.ext
  have hall : ∀ᵐ g ∂μ, ∀ n, (h.T w (u n) : G → ℂ) g = ⟪w, σ g (u n)⟫_ℂ :=
    ae_all_iff.2 fun n => h.T_ae w (u n)
  filter_upwards [hae, hall, h.T_ae w x] with g h1 h2 h3
  rw [h3]
  have h4 : Tendsto (fun i => ⟪w, σ g (u (ns i))⟫_ℂ) atTop (𝓝 ⟪w, σ g x⟫_ℂ) := by
    have hc : Continuous fun v : H => ⟪w, σ g v⟫_ℂ := continuous_const.inner (σ g).continuous
    exact (hc.tendsto x).comp (hu.comp hns.tendsto_atTop)
  have h5 : Tendsto (fun i => ⟪w, σ g (u (ns i))⟫_ℂ) atTop (𝓝 (y g)) := by
    refine h1.congr fun i => ?_
    exact h2 (ns i)
  exact tendsto_nhds_unique h5 h4

def Tc (h : SqRep μ σ) (w : H) : H →L[ℂ] Lp ℂ 2 μ := ⟨h.T w, h.T_cont w⟩

def II (μ : Measure G) (σ : G → (H →L[ℂ] H)) (v w v' w' : H) : ℂ :=
  ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ

theorem integrable (h : SqRep μ σ) (v w v' w' : H) :
    Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (h.Tc w' v') (h.Tc w v)).congr ?_
  filter_upwards [h.T_ae w v, h.T_ae w' v'] with g h1 h2
  have e1 : (h.Tc w v : G → ℂ) g = ⟪w, σ g v⟫_ℂ := h1
  have e2 : (h.Tc w' v' : G → ℂ) g = ⟪w', σ g v'⟫_ℂ := h2
  rw [e1, e2, RCLike.inner_apply]
  rfl

theorem inner_Tc (h : SqRep μ σ) (v w v' w' : H) : ⟪h.Tc w' v', h.Tc w v⟫_ℂ = II μ σ v w v' w' := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h.T_ae w v, h.T_ae w' v'] with g h1 h2
  have e1 : (h.Tc w v : G → ℂ) g = ⟪w, σ g v⟫_ℂ := h1
  have e2 : (h.Tc w' v' : G → ℂ) g = ⟪w', σ g v'⟫_ℂ := h2
  rw [e1, e2, RCLike.inner_apply]
  rfl

end SqRep

end Ortho

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartG2

section PartG3

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

section Ortho2

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {μ : Measure G} {σ : G → (H →L[ℂ] H)}

namespace SqRep

theorem II_right [μ.IsMulRightInvariant] (h : SqRep μ σ) (a : G) (v w v' w' : H) :
    II μ σ (σ a v) w (σ a v') w' = II μ σ v w v' w' := by
  unfold II
  have e : ∀ g, ⟪w, σ g (σ a v)⟫_ℂ * star ⟪w', σ g (σ a v')⟫_ℂ =
      (fun x => ⟪w, σ x v⟫_ℂ * star ⟪w', σ x v'⟫_ℂ) (g * a) := by
    intro g
    simp only [h.mul g a, ContinuousLinearMap.comp_apply]
  simp_rw [e]
  exact integral_mul_right_eq_self (fun x => ⟪w, σ x v⟫_ℂ * star ⟪w', σ x v'⟫_ℂ) a

theorem II_inv [μ.IsInvInvariant] (h : SqRep μ σ) (v w v' w' : H) : II μ σ v w v' w' = II μ σ w' v' w v := by
  unfold II
  rw [← integral_inv_eq_self (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show ⟪w, σ g⁻¹ v⟫_ℂ * star ⟪w', σ g⁻¹ v'⟫_ℂ = ⟪v', σ g w'⟫_ℂ * star ⟪v, σ g w⟫_ℂ
  have e1 : ⟪w, σ g⁻¹ v⟫_ℂ = star ⟪v, σ g w⟫_ℂ := by
    rw [← inner_conj_symm, h.inner_inv]; rfl
  have e2 : star ⟪w', σ g⁻¹ v'⟫_ℂ = ⟪v', σ g w'⟫_ℂ := by
    have : star ⟪w', σ g⁻¹ v'⟫_ℂ = ⟪σ g⁻¹ v', w'⟫_ℂ := inner_conj_symm _ _
    rw [this, h.inner_inv]
  rw [e1, e2, mul_comm]

def AA (h : SqRep μ σ) (w w' : H) : H →L[ℂ] H := (ContinuousLinearMap.adjoint (h.Tc w')).comp (h.Tc w)

theorem inner_AA (h : SqRep μ σ) (v w v' w' : H) : ⟪v', h.AA w w' v⟫_ℂ = II μ σ v w v' w' := by
  unfold AA
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, h.inner_Tc]

theorem AA_comm [μ.IsMulRightInvariant] (h : SqRep μ σ) (w w' : H) (a : G) : Commute (h.AA w w') (σ a) := by
  show h.AA w w' * σ a = σ a * h.AA w w'
  ext v
  show h.AA w w' (σ a v) = σ a (h.AA w w' v)
  refine ext_inner_left ℂ fun v' => ?_
  rw [h.inner_AA, ← h.inner_inv, h.inner_AA]
  conv_lhs => rw [← h.mul_inv_apply a v']
  exact h.II_right a v w (σ a⁻¹ v') w'

theorem star_eq (h : SqRep μ σ) (a : G) : star (σ a) = σ a⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  exact fun x y => h.inner_inv a x y

theorem exists_scalar [Nontrivial H] [μ.IsMulRightInvariant] (h : SqRep μ σ) (w w' : H) :
    ∃ z : ℂ, ∀ v v', II μ σ v w v' w' = z * ⟪v', v⟫_ℂ := by
  obtain ⟨z, hz⟩ := schur_general (Set.range σ)
    (fun S hS hinv => h.irr S hS fun g v hv => hinv _ ⟨g, rfl⟩ v hv) (h.AA w w')
    (by rintro _ ⟨a, rfl⟩; exact h.AA_comm w w' a)
    (by rintro _ ⟨a, rfl⟩; rw [h.star_eq]; exact h.AA_comm w w' a⁻¹)
  refine ⟨z, fun v v' => ?_⟩
  rw [← h.inner_AA, hz, inner_smul_right]

theorem ortho [Nontrivial H] [μ.IsMulRightInvariant] [μ.IsInvInvariant] [μ.IsOpenPosMeasure] (h : SqRep μ σ) :
    ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H,
      Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧
      ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by
  obtain ⟨e, he⟩ := exists_ne (0 : H)
  have hN : (0 : ℝ) < ‖e‖ ^ 2 := by positivity
  have hee : ⟪e, e⟫_ℂ = ((‖e‖ ^ 2 : ℝ) : ℂ) := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
  choose z hz using h.exists_scalar

  set J : ℝ := ∫ g, ‖⟪e, σ g e⟫_ℂ‖ ^ 2 ∂μ with hJ
  have hIJ : II μ σ e e e e = (J : ℂ) := by
    unfold II
    rw [hJ, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show ⟪e, σ g e⟫_ℂ * star ⟪e, σ g e⟫_ℂ = ((‖⟪e, σ g e⟫_ℂ‖ ^ 2 : ℝ) : ℂ)
    have := RCLike.mul_conj (⟪e, σ g e⟫_ℂ)
    rw [show star ⟪e, σ g e⟫_ℂ = (starRingEnd ℂ) ⟪e, σ g e⟫_ℂ from rfl, this]
    norm_cast
  have hcontc : Continuous fun g => ‖⟪e, σ g e⟫_ℂ‖ ^ 2 :=
    ((continuous_const.inner (h.cont e)).norm).pow 2
  have hint : Integrable (fun g => ‖⟪e, σ g e⟫_ℂ‖ ^ 2) μ := by
    have := (h.integrable e e e e).norm
    refine this.congr (Eventually.of_forall fun g => ?_)
    show ‖⟪e, σ g e⟫_ℂ * star ⟪e, σ g e⟫_ℂ‖ = ‖⟪e, σ g e⟫_ℂ‖ ^ 2
    rw [norm_mul, norm_star, sq]
  have hJpos : 0 < J := by
    have h0 : 0 ≤ J := integral_nonneg fun g => by positivity
    rcases h0.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have h2 := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hint).1 h1.symm
      have h3 : (fun g => ‖⟪e, σ g e⟫_ℂ‖ ^ 2) = fun _ => (0 : ℝ) :=
        (hcontc.ae_eq_iff_eq μ (continuous_const (y := (0 : ℝ)))).1 h2
      have h4 : ‖⟪e, σ 1 e⟫_ℂ‖ ^ 2 = (0 : ℝ) := congrFun h3 1
      rw [h.one, one_apply_eq_self, hee] at h4
      have h5 : ‖((‖e‖ ^ 2 : ℝ) : ℂ)‖ = ‖e‖ ^ 2 := by
        rw [Complex.norm_real, Real.norm_of_nonneg hN.le]
      rw [h5] at h4
      have : 0 < (‖e‖ ^ 2) ^ 2 := by positivity
      linarith
  have hNc : ((‖e‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'

  have hzw : ∀ w w', z w w' * ((‖e‖ ^ 2 : ℝ) : ℂ) = z e e * ⟪w, w'⟫_ℂ := by
    intro w w'
    rw [← hee, ← hz w w' e e, h.II_inv, hz e e w' w]
  have hzee : z e e * ((‖e‖ ^ 2 : ℝ) : ℂ) = (J : ℂ) := by rw [← hee, ← hz e e e e, hIJ]
  refine ⟨(‖e‖ ^ 2) ^ 2 / J, by positivity, fun v w v' w' => ⟨h.integrable v w v' w', ?_⟩⟩
  have hJc : (J : ℂ) ≠ 0 := by exact_mod_cast hJpos.ne'
  have key : II μ σ v w v' w' = z w w' * ⟪v', v⟫_ℂ := hz w w' v v'
  show II μ σ v w v' w' = _
  rw [key]
  have e1 : z w w' = z e e * ⟪w, w'⟫_ℂ / ((‖e‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hzw]; field_simp
  have e2 : z e e = (J : ℂ) / ((‖e‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hzee]; field_simp
  rw [e1, e2]
  push_cast
  have hne : ((‖e‖ : ℝ) : ℂ) ≠ 0 := by
    have : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
    exact_mod_cast this
  field_simp

end SqRep

end Ortho2

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartG3

section PartA1

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section MultOne

theorem inWb_of_zero {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ)
    (h : ∀ a : Fin r, z (eI k r a) = 0 ∧ z (esI k r a) = 0) : inWb k r z := by
  intro i hi
  rcases hi with hi | hi
  · have := (h ⟨i.val, hi⟩).1
    simpa [eI] using this
  · have hlt : 2 * r + k - i.val < r := by have := i.2; omega
    have := (h ⟨2 * r + k - i.val, hlt⟩).2
    have e : esI k r ⟨2 * r + k - i.val, hlt⟩ = i := by
      apply Fin.ext
      simp only [esI]
      have := i.2
      omega
    rwa [e] at this

theorem haarW_one {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) :
    ∃ μ : Measure (Mt k r), Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ ∧ μ Set.univ = 1 :=
  Inh.haar_probability_compact_subgroup _ (Inh.one_mem_unitary_stabilizer_set _) (Inh.unitary_stabilizer_mul_mem _) (fun a => Hpk k r * aᴴ * Hpk k r)
    ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const)
    (Inh.unitary_stabilizer_inv_mem _) (Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hz hT)

theorem psiS_scale_ne (D : D7) :
    ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
  have h0 : (0 : ℝ) < (D.host.g 0 : ℝ) := by exact_mod_cast (D.host.g_prime 0).pos
  have h1 : (0 : ℝ) < (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).pos
  have hka : 0 < D.host.ka := by unfold Host.ka; exact div_pos Real.pi_pos (Inh.amp_v_pos D)
  have : (0 : ℝ) < 2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by positivity
  exact_mod_cast this.ne'

theorem local_multiplicity_one_of_bounded (h : UnitaryLevelOperators.stJSZ) (D : D7) : LocalBesselAndTopKernel.MultiplicityOneUnitaryBranching D := by
  intro τ u H _ _ σ Wp _ _ π z B1 B2 hσ hπ hz hT hB1 hB2 _ _ _ _
  have hzW : inWb D.R.k D.R.rS z := inWb_of_zero z hz
  obtain ⟨μ, hμ⟩ := haarW_one z hzW hT
  obtain ⟨P, hP, hDS⟩ := id hσ
  have : CompleteSpace H := hDS.1
  obtain ⟨g, hg, hU⟩ := id hπ
  have : FiniteDimensional ℂ Wp := hU.2.1
  let L : LocBessel D.R.k D.R.rS :=
    { ε := epsSH D.R, lam := lamSH D.R (D.hc τ), hlam := Inh.obj_isHCParam_lamSH D.R (D.hc τ), z := z, z' := z,
      hz := ⟨hzW, hT⟩, hz' := ⟨hzW, hT⟩, u := fun i => ((D.hcW u τ).u i : ℝ), u' := fun i => ((D.hcW u τ).u i : ℝ),
      Hs := H, σ := σ, hσ := hσ, Wp := Wp, π := π, hπ := hπ, Wq := Wp, π' := π, hπ' := hπ,
      c := ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ), μW := μ, μW' := μ, hμW := hμ, hμW' := hμ,
      κN := 1 }
  obtain ⟨a, b, hab, hlin⟩ := h D.R.k D.R.rS L B1 B2 (psiS_scale_ne D) hB1 hB2
  by_cases hb : b = 0
  · left
    intro v hv
    have ha : a ≠ 0 := by
      rcases hab with h' | h'
      · exact h'
      · exact absurd hb h'
    have := hlin v hv
    rw [hb, zero_smul, add_zero] at this
    exact (smul_eq_zero.1 this).resolve_left ha
  · right
    refine ⟨-(a / b), fun v hv => ?_⟩
    have h1 := hlin v hv
    have h2 : b • B2 v = -(a • B1 v) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h1
    have h3 : B2 v = b⁻¹ • (b • B2 v) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
    rw [h3, h2, smul_neg, smul_smul, neg_smul]
    congr 2
    field_simp

theorem local_multiplicity_one_family {eps : ℝ} (Fm : FamP eps) (h : BridgeLemma₅.KnownLiterature) : LocalBesselAndTopKernel.FamilyMultiplicityOneHypothesis Fm :=
  fun x i => local_multiplicity_one_of_bounded h.besselModel_unique (Fm.D x i)

end MultOne

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartA1

section PartA2

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants

section Tr

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem conj_mem {P a : MatKR k r} (hP : IsCayleyU k r ε P) (ha : a ∈ UH (Hpk k r)) :
    P * a * P⁻¹ ∈ UJset ε ∧ P⁻¹ * (P * a * P⁻¹) * P = a := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hH : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r := hP.1.2
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  constructor
  · show (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹) = Formalism.REAL.Jm ε
    calc (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹)
        = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * a) * P⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hH, ha']
      _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2]; simp
  · calc P⁻¹ * (P * a * P⁻¹) * P = (P⁻¹ * P) * a * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = a := by rw [h1]; simp

def cjH (P : MatKR k r) (hu : IsUnit P.det) : MatKR k r ≃ₜ MatKR k r where
  toFun x := P⁻¹ * x * P
  invFun y := P * y * P⁻¹
  left_inv x := by
    have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    calc P * (P⁻¹ * x * P) * P⁻¹ = (P * P⁻¹) * x * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [h2]; simp
  right_inv y := by
    have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
    calc P⁻¹ * (P * y * P⁻¹) * P = (P⁻¹ * P) * y * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [h1]; simp
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def ioP (P : MatKR k r) (g : Formalism.REAL.UJ ε) : Mt k r := P⁻¹ * umat g * P

theorem measurableEmbedding_conjCayley {P : MatKR k r} (hP : IsCayleyU k r ε P) : MeasurableEmbedding (ioP (ε := ε) P) := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : Topology.IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => (cjH P hu) (umat g)) :=
    (cjH P hu).isClosedEmbedding.comp (Formalism.REAL.isClosedEmbeddingMatrix _ ε).1
  have h2 : Topology.IsClosedEmbedding (ioP (ε := ε) P) := h1
  exact h2.measurableEmbedding

theorem conj_mem_unitaryGroup {P : MatKR k r} (hP : IsCayleyU k r ε P) (g : Formalism.REAL.UJ ε) :
    Matrix.of (ioP P g) ∈ UH (Hpk k r) := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hH : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r := hP.1.2
  have hg : (umat g)ᴴ * Formalism.REAL.Jm ε * umat g = Formalism.REAL.Jm ε := g.2
  show (P⁻¹ * umat g * P)ᴴ * Hpk k r * (P⁻¹ * umat g * P) = Hpk k r
  rw [← hH]
  calc (P⁻¹ * umat g * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * (P⁻¹ * umat g * P)
      = Pᴴ * ((umat g)ᴴ * ((P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹)) * umat g) * P := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * ((umat g)ᴴ * Formalism.REAL.Jm ε * umat g) * P := by rw [h2]; simp
    _ = Pᴴ * Formalism.REAL.Jm ε * P := by rw [hg]

theorem isHaarOn_map_conjCayley {P : MatKR k r} (hP : IsCayleyU k r ε P) :
    Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) ((Formalism.REAL.muG ε).map (ioP P)) := by
  have hemb := measurableEmbedding_conjCayley hP
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  refine ⟨hemb.sigmaFinite_map, ?_, ?_, ?_⟩
  · intro h0
    rw [Measure.map_eq_zero_iff hemb.measurable.aemeasurable] at h0
    exact (NeZero.ne (Formalism.REAL.muG ε)) h0
  · rw [hemb.map_apply]
    have : ioP P ⁻¹' {x | Matrix.of x ∉ UH (Hpk k r)} = (∅ : Set (Formalism.REAL.UJ ε)) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact conj_mem_unitaryGroup hP g
    rw [this, measure_empty]
  · intro s hs
    have hm : Measurable (lmulM (k := k) (r := r) s) := by
      unfold lmulM
      refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply]
      refine Finset.measurable_sum _ fun l _ => ?_
      have h0 : Measurable fun x : Mt k r => x l j := by fun_prop
      exact h0.const_mul _
    rw [Measure.map_map hm hemb.measurable]
    set s' : Formalism.REAL.UJ ε := Formalism.REAL.indefiniteUnitaryMk ε (P * s * P⁻¹) (conj_mem hP hs).1 with hs'
    have hcomp : lmulM s ∘ ioP (ε := ε) P = ioP P ∘ fun g => s' * g := by
      funext g
      show s * (P⁻¹ * umat g * P) = P⁻¹ * (P * s * P⁻¹ * umat g) * P
      calc s * (P⁻¹ * umat g * P) = (P⁻¹ * P) * s * (P⁻¹ * umat g * P) := by rw [h1]; simp
        _ = P⁻¹ * (P * s * P⁻¹ * umat g) * P := by simp only [Matrix.mul_assoc]
    rw [hcomp, ← Measure.map_map hemb.measurable (measurable_const_mul s'), map_mul_left_eq_self]

theorem transport {P : MatKR k r} (hP : IsCayleyU k r ε P) {μ : Measure (Mt k r)}
    (hμ : Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • (Formalism.REAL.muG ε).map (ioP P) := by
  obtain ⟨ν, hν⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨c1, a1, a2, e1⟩ := BridgeLemma₃.hu_eq_smul (Formalism.FourierDecayAlt.P.unitary_group_closed k r) hν hμ
  obtain ⟨c2, b1, b2, e2⟩ := BridgeLemma₃.hu_eq_smul (Formalism.FourierDecayAlt.P.unitary_group_closed k r) hν (isHaarOn_map_conjCayley hP)
  refine ⟨c1 / c2, ENNReal.div_ne_zero.2 ⟨a1, b2⟩, ENNReal.div_ne_top a2 b1, ?_⟩
  rw [e1, e2, smul_smul, ENNReal.div_mul_cancel b1 b2]

theorem schur_hpk {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : MatKR k r → (H →L[ℂ] H)}
    {P : MatKR k r} (hP : IsCayleyU k r ε P) {d : ℝ} (hd : IsFdeg (Formalism.REAL.muG ε) (fun g => σ (P⁻¹ * g * P)) d)
    {μG : Measure (Mt k r)} (hμ : Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG) :
    ∃ d' : ℝ, 0 < d' ∧ ∀ v w v' w' : H,
      Integrable (fun x => inner ℂ w (σ (Matrix.of x) v) * star (inner ℂ w' (σ (Matrix.of x) v'))) μG ∧
      ∫ x, inner ℂ w (σ (Matrix.of x) v) * star (inner ℂ w' (σ (Matrix.of x) v')) ∂μG =
        inner ℂ v' v * inner ℂ w w' / (d' : ℂ) := by
  obtain ⟨c, c0, ctop, hc⟩ := transport hP hμ
  have hc' : 0 < c.toReal := ENNReal.toReal_pos c0 ctop
  obtain ⟨hd0, hS⟩ := hd
  refine ⟨d / c.toReal, div_pos hd0 hc', fun v w v' w' => ?_⟩
  obtain ⟨hi, he⟩ := hS v w v' w'
  have hemb := measurableEmbedding_conjCayley (ε := ε) hP
  constructor
  · rw [hc]
    refine Integrable.smul_measure ?_ ctop
    rw [hemb.integrable_map_iff]
    exact hi
  · rw [hc, integral_smul_measure, hemb.integral_map]
    have : (∫ g, inner ℂ w (σ (Matrix.of (ioP P g)) v) * star (inner ℂ w' (σ (Matrix.of (ioP P g)) v'))
        ∂(Formalism.REAL.muG ε)) = inner ℂ v' v * inner ℂ w w' / (d : ℂ) := he
    rw [this, Complex.real_smul]
    push_cast
    have h1 : (c.toReal : ℂ) ≠ 0 := by exact_mod_cast hc'.ne'
    have h2 : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    field_simp

end Tr

theorem schur_relations_of_formal_degree (D : D7) (h : CayleySignature.adm6 D) : LocalBesselAndTopKernel.NonvanishingBesselPeriod D := by
  intro τ H _ _ σ hσ μG hμ
  obtain ⟨P, hP, hDS⟩ := hσ
  have : CompleteSpace H := hDS.1
  obtain ⟨d, hd⟩ := h _ _ _ H _ hDS
  exact schur_hpk hP hd hμ

theorem schur_relations_of_formal_degree_family {eps : ℝ} (Fm : FamP eps) (h : CayleySignature.admF6 Fm) : LocalBesselAndTopKernel.UnfoldingCount Fm :=
  fun x i => schur_relations_of_formal_degree (Fm.D x i) (h x i)

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartA2

section PartG4

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants

section Fdeg

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

instance muG_right : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩

instance muG_inv : (Formalism.REAL.muG ε).IsInvInvariant :=
  ⟨Formalism.REAL.invInvariant_of Formalism.REAL.indefinite_unitary_unimodular n ε⟩

instance muG_open : (Formalism.REAL.muG ε).IsOpenPosMeasure := by unfold Formalism.REAL.muG; infer_instance

theorem sqRep_of_isDS [CompleteSpace H] {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (h : IsDS ε lam σ) : SqRep (Formalism.REAL.muG ε) (fun g : Formalism.REAL.UJ ε => σ (umat g)) := by
  obtain ⟨-, -, ⟨⟨h1, hm⟩, hiso, hcont⟩, hirr, hl2, -⟩ := h
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  refine ⟨h1, fun a b => hm _ (hmem a) _ (hmem b), fun g v => hiso _ (hmem g) v, fun v => ?_, fun S hS hinv => ?_, hl2⟩
  · exact (hcont v).comp_continuous (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.continuous hmem
  · refine hirr S hS fun g hg v hv => ?_
    exact hinv (Formalism.REAL.indefiniteUnitaryMk ε g hg) v hv

theorem fdeg_exists {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsDS ε lam σ) :
    ∃ d : ℝ, IsFdeg (Formalism.REAL.muG ε) σ d := by
  have : CompleteSpace H := h.1
  have : Nontrivial H := h.2.1
  obtain ⟨d, hd, ho⟩ := (sqRep_of_isDS h).ortho
  exact ⟨d, hd, ho⟩

end Fdeg

theorem schur_formal_degree_exists (D : D7) : CayleySignature.adm6 D := fun _ _ _ _ _ _ _ _ h => fdeg_exists h

theorem formal_degree_exists_local (D : D7) : PlaceDegreeData.adm1 D := fun _ _ _ _ _ _ _ _ _ h => fdeg_exists h

theorem nonvanishingBesselPeriod (D : D7) : LocalBesselAndTopKernel.NonvanishingBesselPeriod D := schur_relations_of_formal_degree D (schur_formal_degree_exists D)

theorem formal_degree_family {eps : ℝ} (Fm : FamP eps) : CayleySignature.admF6 Fm := fun x i => schur_formal_degree_exists (Fm.D x i)

theorem schur_relations_family {eps : ℝ} (Fm : FamP eps) : LocalBesselAndTopKernel.UnfoldingCount Fm := fun x i => nonvanishingBesselPeriod (Fm.D x i)

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartG4

section PartR1

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open Formalism.MainNotions.S.Loc Formalism.MainNotions.BridgeLemma ValuativeRel IsDedekindDomain NumberField Topology

section Resid

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)

def intMap : 𝓞 F →+* 𝒪[A.Fp] :=
  (A.ιF.comp (algebraMap (𝓞 F) F)).codRestrict 𝒪[A.Fp] fun a =>
    (mem_OF_iff A _).2 (p.valuation_le_one a)

theorem intMap_coe (a : 𝓞 F) : ((intMap A a : 𝒪[A.Fp]) : A.Fp) = A.ιF (a : F) := rfl

def redMap : 𝓞 F →+* 𝓀[A.Fp] :=
  have := A.lf
  (IsLocalRing.residue 𝒪[A.Fp]).comp (intMap A)

theorem res_eq_zero_iff (x : 𝒪[A.Fp]) :
    (have := A.lf; IsLocalRing.residue 𝒪[A.Fp] x = 0) ↔ valuation A.Fp (x : A.Fp) < 1 := by
  have := A.lf
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation A.Fp)).isUnit_iff_valuation_eq_one]
  have hx : valuation A.Fp (x : A.Fp) ≤ 1 := x.2
  exact ⟨fun h => lt_of_le_of_ne hx h, fun h => h.ne⟩

theorem redMap_ker : RingHom.ker (redMap A) = p.asIdeal := by
  ext a
  rw [RingHom.mem_ker]
  show (have := A.lf; IsLocalRing.residue 𝒪[A.Fp] (intMap A a) = 0) ↔ _
  rw [res_eq_zero_iff, intMap_coe]
  constructor
  · intro h
    by_contra ha
    rw [vFp_eq_one A _ (val_eq_one a ha)] at h
    exact lt_irrefl _ h
  · intro ha
    have h1 : p.valuation F (a : F) < 1 := (p.valuation_lt_one_iff_mem a).2 ha
    by_contra h
    have h2 : valuation A.Fp (A.ιF 1) ≤ valuation A.Fp (A.ιF (a : F)) := by
      rw [map_one, map_one]; exact not_lt.1 h
    have h3 := (val_iff A 1 (a : F)).1 h2
    rw [map_one] at h3
    exact absurd h1 (not_lt.2 h3)

theorem redMap_surj : Function.Surjective (redMap A) := by
  have := A.lf
  intro ρ
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective ρ

  have hs : ((x : A.Fp) + ·) '' {z | valuation A.Fp z < ((1 : (ValueGroupWithZero A.Fp)ˣ) : ValueGroupWithZero A.Fp)} ∈
      𝓝 (x : A.Fp) := IsValuativeTopology.mem_nhds_iff.2 ⟨1, subset_rfl⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, ⟨y, hy⟩⟩ := mem_closure_iff_nhds.1 (A.dense (x : A.Fp)) _ hs
  have hz1 : valuation A.Fp z < 1 := by simpa using hz
  have hyO : A.ιF y ∈ 𝒪[A.Fp] := by
    rw [hy]
    exact 𝒪[A.Fp].add_mem x.2 (Valuation.mem_integer_iff _ _ |>.2 hz1.le)
  have hyv : p.valuation F y ≤ 1 := (mem_OF_iff A y).1 hyO
  obtain ⟨a, ha, z0, hz0⟩ := exists_den p y hyv
  have hmax : p.asIdeal.IsMaximal := p.isMaximal
  obtain ⟨b, i, hi, hbi⟩ := hmax.exists_inv ha
  have hri : redMap A i = 0 := by
    rw [← RingHom.mem_ker, redMap_ker]; exact hi
  have hba : redMap A b * redMap A a = 1 := by
    have := congrArg (redMap A) hbi
    rwa [map_add, map_mul, hri, add_zero, map_one] at this

  set Y : 𝒪[A.Fp] := ⟨A.ιF y, hyO⟩ with hY
  have hYx : IsLocalRing.residue 𝒪[A.Fp] Y = IsLocalRing.residue 𝒪[A.Fp] x := by
    rw [← sub_eq_zero, ← map_sub]
    refine (res_eq_zero_iff A (Y - x)).2 ?_
    have : ((Y - x : 𝒪[A.Fp]) : A.Fp) = z := by
      show A.ιF y - (x : A.Fp) = z
      rw [hy]; ring
    rw [this]; exact hz1
  have haY : intMap A a * Y = intMap A z0 := by
    apply Subtype.ext
    show A.ιF (a : F) * A.ιF y = A.ιF (z0 : F)
    rw [← map_mul, hz0]
  refine ⟨b * z0, ?_⟩
  have h1 : redMap A z0 = redMap A a * IsLocalRing.residue 𝒪[A.Fp] Y := by
    show IsLocalRing.residue 𝒪[A.Fp] (intMap A z0) = _
    rw [← haY, map_mul]; rfl
  rw [map_mul, h1, ← mul_assoc, hba, one_mul, hYx]

theorem card_resid : Nat.card 𝓀[A.Fp] = Ideal.absNorm p.asIdeal := by
  have e := RingHom.quotientKerEquivOfSurjective (redMap_surj A)
  rw [← Nat.card_congr e.toEquiv, redMap_ker, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end Resid

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartR1

section PartR2

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.BridgeLemma ValuativeRel IsDedekindDomain NumberField Ideal

section PrimeSum

theorem primeSum_fin (F : Type) [Field F] [NumberField F] (s : ℝ) (hs : 2 ≤ s) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∑ p ∈ S, ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-s) ≤ (Module.finrank ℚ F : ℝ) * 2 ^ (2 - s) := by
  classical
  have hq_prime : ∀ p : HeightOneSpectrum (𝓞 F), (absNorm (under ℤ p.asIdeal)).Prime := fun p => by
    have : NeZero p.asIdeal := ⟨p.ne_bot⟩
    have := p.isPrime
    exact Nat.absNorm_under_prime p.asIdeal
  have hq_le : ∀ p : HeightOneSpectrum (𝓞 F), absNorm (under ℤ p.asIdeal) ≤ absNorm p.asIdeal := fun p =>
    Nat.le_of_dvd (Nat.pos_of_ne_zero (by rw [Ne, absNorm_eq_zero_iff]; exact p.ne_bot))
      (Int.absNorm_under_dvd_absNorm p.asIdeal)
  calc ∑ p ∈ S, ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-s)
      ≤ ∑ p ∈ S, ((absNorm (under ℤ p.asIdeal) : ℕ) : ℝ) ^ (-s) := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        refine Real.rpow_le_rpow_of_nonpos ?_ (by exact_mod_cast hq_le p) (by linarith)
        exact_mod_cast (hq_prime p).pos
    _ = ∑ n ∈ S.image (fun p => absNorm (under ℤ p.asIdeal)),
          (S.filter (fun p => absNorm (under ℤ p.asIdeal) = n)).card • ((n : ℝ) ^ (-s)) :=
        Finset.sum_comp (fun n : ℕ => (n : ℝ) ^ (-s)) (fun p : HeightOneSpectrum (𝓞 F) => absNorm (under ℤ p.asIdeal))
    _ ≤ ∑ n ∈ S.image (fun p => absNorm (under ℤ p.asIdeal)), (Module.finrank ℚ F : ℝ) * ((n : ℝ) ^ (-s)) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hn
        rw [nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_primes_over_rational_le F S _ (hq_prime p)
    _ = (Module.finrank ℚ F : ℝ) * ∑ n ∈ S.image (fun p => absNorm (under ℤ p.asIdeal)), (n : ℝ) ^ (-s) := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ F : ℝ) * 2 ^ (2 - s) := by
        refine mul_le_mul_of_nonneg_left (sum_rpow_neg_le_two_pow _ (fun n hn => ?_) s hs) (by positivity)
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hn
        exact (hq_prime p).two_le

theorem primeSum_summable (F : Type) [Field F] [NumberField F] (s : ℝ) (hs : 2 ≤ s) :
    Summable fun p : HeightOneSpectrum (𝓞 F) => ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-s) :=
  summable_of_sum_le (fun p => by positivity) (primeSum_fin F s hs)

theorem two_le_absNorm {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) : 2 ≤ absNorm p.asIdeal := by
  have h0 : absNorm p.asIdeal ≠ 0 := by rw [Ne, absNorm_eq_zero_iff]; exact p.ne_bot
  have h1 : absNorm p.asIdeal ≠ 1 := by rw [Ne, absNorm_eq_one_iff]; exact p.isPrime.ne_top
  omega

theorem num_pow (k m f : ℕ) (hm : 2 ≤ m) (h1 : m ^ 4 ≤ f) (h2 : f ≤ k) : 32 * f ≤ 2 ^ (k - m) := by
  have h8 : 8 * m ≤ m ^ 4 := by
    have : 8 ≤ m ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ m ^ 3 := Nat.pow_le_pow_left hm 3
    calc 8 * m ≤ m ^ 3 * m := Nat.mul_le_mul_right m this
      _ = m ^ 4 := by ring
  have h16 : 16 ≤ m ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ m ^ 4 := Nat.pow_le_pow_left hm 4
  have hk : k < 4 * 2 ^ (k / 4) := by
    have := Nat.lt_two_pow_self (n := k / 4)
    omega
  have he : k / 4 + 7 ≤ k - m := by omega
  calc 32 * f ≤ 32 * k := by omega
    _ ≤ 32 * (4 * 2 ^ (k / 4)) := by omega
    _ = 2 ^ (k / 4 + 7) := by rw [pow_add]; ring
    _ ≤ 2 ^ (k - m) := Nat.pow_le_pow_right (by norm_num) he

theorem prime_sum_step_of_ranks (D : D7) (Ce : ℝ) (hCe : 4 ≤ Ce) (h1 : D.R.m ^ 4 ≤ D.R.f) (h2 : D.R.f ≤ D.R.k) :
    PrimeSumStep D Ce := by
  have hm := D.R.two_le_m
  have hmr : 2 * D.R.rS + 2 = D.R.m := std_two_rS D
  have hnum := num_pow D.R.k D.R.m D.R.f hm h1 h2
  have h16 : 16 ≤ D.R.m ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm 4
  have h8 : 8 * D.R.m ≤ D.R.m ^ 4 := by
    have : 8 ≤ D.R.m ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ D.R.m ^ 3 := Nat.pow_le_pow_left hm 3
    calc 8 * D.R.m ≤ D.R.m ^ 3 * D.R.m := Nat.mul_le_mul_right _ this
      _ = D.R.m ^ 4 := by ring
  set s : ℕ := D.R.k - D.R.m with hs
  have hs3 : 3 ≤ s := by omega
  have hsZ : (D.R.k : ℤ) - 2 * D.R.rS - 2 = (s : ℤ) := by omega
  have hsR : (D.R.k : ℝ) - 2 * D.R.rS - 3 = (s : ℝ) - 1 := by
    have : (D.R.k : ℝ) = (s : ℝ) + (2 * D.R.rS + 2 : ℕ) := by
      rw [hmr, hs, Nat.cast_sub (by omega)]; ring
    rw [this]; push_cast; ring

  have hterm : ∀ p : PlF D, (Nat.card 𝓀[(D.s.atP p).Fp] : ℝ) ^ (-((D.R.k : ℤ) - 2 * D.R.rS - 2)) =
      ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-(s : ℝ)) := by
    intro p
    rw [card_resid, hsZ, zpow_neg, zpow_natCast, Real.rpow_neg (by positivity), Real.rpow_natCast]
  simp_rw [PrimeSumStep, hterm]
  have hsum := primeSum_summable D.host.F (s : ℝ) (by exact_mod_cast (by omega : 2 ≤ s))
  have hsum' := primeSum_summable D.host.F ((s : ℝ) - 1) (by
    have : (3 : ℝ) ≤ s := by exact_mod_cast hs3
    linarith)
  set SS : ℝ := ∑' p : PlF D, ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-(s : ℝ)) with hSdef
  have hS0 : 0 ≤ SS := tsum_nonneg fun p => by positivity
  have hSle : SS ≤ (D.R.f : ℝ) * 2 ^ (2 - (s : ℝ)) := by
    have := prime_ideal_norm_rpow_sum_le D.host.F (s : ℝ) (by exact_mod_cast (by omega : 2 ≤ s))
    rwa [finrank_base_field_eq_degree D] at this
  have hx : 4 * SS ≤ 1 / 2 := by
    have e : (2 : ℝ) ^ (2 - (s : ℝ)) = 4 / 2 ^ s := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]; norm_num
    have hn : (32 : ℝ) * D.R.f ≤ 2 ^ s := by exact_mod_cast hnum
    have hp : (0 : ℝ) < 2 ^ s := by positivity
    have : (D.R.f : ℝ) * (4 / 2 ^ s) ≤ 1 / 8 := by
      rw [mul_div_assoc', div_le_iff₀ hp]; linarith
    rw [e] at hSle
    linarith
  have hexp : Real.exp (4 * SS) ≤ 1 + 8 * SS := by
    have h0 : 0 ≤ 4 * SS := by positivity
    have hb := Real.exp_bound_div_one_sub_of_interval h0 (by linarith : 4 * SS < 1)
    refine le_trans hb ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  refine ⟨hsum, by linarith, le_trans hexp ?_⟩
  unfold eSum
  rw [hsR]
  have h2S : 2 * SS ≤ ∑' p : HeightOneSpectrum (𝓞 D.host.F), ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-((s : ℝ) - 1)) := by
    rw [hSdef, ← tsum_mul_left]
    refine hsum.mul_left 2 |>.tsum_le_tsum (fun p => ?_) hsum'
    have hN : (2 : ℝ) ≤ ((absNorm p.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm p
    have hN0 : (0 : ℝ) < ((absNorm p.asIdeal : ℕ) : ℝ) := by linarith
    have e : ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-((s : ℝ) - 1)) =
        ((absNorm p.asIdeal : ℕ) : ℝ) * ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-(s : ℝ)) := by
      rw [show -((s : ℝ) - 1) = 1 + -(s : ℝ) by ring, Real.rpow_add hN0, Real.rpow_one]
    rw [e]
    exact mul_le_mul_of_nonneg_right hN (by positivity)
  nlinarith

theorem density_factor_absorbed (D : D7) (Ce : ℝ) (hCe : 8 ≤ Ce) (h1 : D.R.m ^ 4 ≤ D.R.f) (h2 : D.R.f ≤ D.R.k) :
    (1 + eSum D 4) * Real.exp (8 * BridgeLemma.qS D) ≤ 1 + eSum D Ce := by
  have hm := D.R.two_le_m
  have hmr : 2 * D.R.rS + 2 = D.R.m := std_two_rS D
  have hnum := num_pow D.R.k D.R.m D.R.f hm h1 h2
  have h16 : 16 ≤ D.R.m ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm 4
  have h8 : 8 * D.R.m ≤ D.R.m ^ 4 := by
    have : 8 ≤ D.R.m ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ D.R.m ^ 3 := Nat.pow_le_pow_left hm 3
    calc 8 * D.R.m ≤ D.R.m ^ 3 * D.R.m := Nat.mul_le_mul_right _ this
      _ = D.R.m ^ 4 := by ring
  set s : ℕ := D.R.k - D.R.m with hs
  have hs3 : 3 ≤ s := by omega
  have hsR : (D.R.k : ℝ) - 2 * D.R.rS - 3 = (s : ℝ) - 1 := by
    have : (D.R.k : ℝ) = (s : ℝ) + (2 * D.R.rS + 2 : ℕ) := by
      rw [hmr, hs, Nat.cast_sub (by omega)]; ring
    rw [this]; push_cast; ring
  have hkR : (D.R.k : ℝ) = ((s : ℝ) - 1) + ((D.R.m : ℝ) + 1) := by
    have : D.R.k = s + D.R.m := by omega
    rw [this]; push_cast; ring
  set X : ℝ := ∑' p : HeightOneSpectrum (𝓞 D.host.F), ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-((s : ℝ) - 1)) with hXdef
  have hsumX := primeSum_summable D.host.F ((s : ℝ) - 1) (by
    have : (3 : ℝ) ≤ s := by exact_mod_cast hs3
    linarith)
  have hX0 : 0 ≤ X := tsum_nonneg fun p => by positivity
  have hXle : X ≤ 1 / 4 := by
    have hle := prime_ideal_norm_rpow_sum_le D.host.F ((s : ℝ) - 1) (by
      have : (3 : ℝ) ≤ s := by exact_mod_cast hs3
      linarith)
    rw [finrank_base_field_eq_degree D] at hle
    have e : (2 : ℝ) ^ (2 - ((s : ℝ) - 1)) = 8 / 2 ^ s := by
      rw [show (2 : ℝ) - ((s : ℝ) - 1) = 3 - (s : ℝ) by ring, Real.rpow_sub (by norm_num), Real.rpow_natCast]; norm_num
    have hn : (32 : ℝ) * D.R.f ≤ 2 ^ s := by exact_mod_cast hnum
    have hp : (0 : ℝ) < 2 ^ s := by positivity
    have : (D.R.f : ℝ) * (8 / 2 ^ s) ≤ 1 / 4 := by
      rw [mul_div_assoc', div_le_iff₀ hp]; linarith
    rw [e] at hle
    linarith
  have hterm : ∀ p : PlF D, (Nat.card 𝓀[(D.s.atP p).Fp] : ℝ) ^ (-(D.R.k : ℤ)) =
      ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-(D.R.k : ℝ)) := by
    intro p
    rw [card_resid, zpow_neg, zpow_natCast, Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hle8 : ∀ p : HeightOneSpectrum (𝓞 D.host.F), ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-(D.R.k : ℝ)) ≤
      ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-((s : ℝ) - 1)) / 8 := by
    intro p
    have hN : (2 : ℝ) ≤ ((absNorm p.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm p
    have hN0 : (0 : ℝ) < ((absNorm p.asIdeal : ℕ) : ℝ) := by linarith
    rw [hkR, neg_add, Real.rpow_add hN0]
    have hm3 : (3 : ℝ) ≤ (D.R.m : ℝ) + 1 := by
      have : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
      linarith
    have h8' : ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-((D.R.m : ℝ) + 1)) ≤ 1 / 8 := by
      rw [Real.rpow_neg hN0.le]
      have : (8 : ℝ) ≤ ((absNorm p.asIdeal : ℕ) : ℝ) ^ ((D.R.m : ℝ) + 1) := by
        calc (8 : ℝ) = 2 ^ (3 : ℝ) := by norm_num
          _ ≤ 2 ^ ((D.R.m : ℝ) + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hm3
          _ ≤ _ := Real.rpow_le_rpow (by norm_num) hN (by positivity)
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      linarith
    have hpos : 0 ≤ ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-((s : ℝ) - 1)) := by positivity
    calc ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-((s : ℝ) - 1)) * ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-((D.R.m : ℝ) + 1))
        ≤ ((absNorm p.asIdeal : ℕ) : ℝ) ^ (-((s : ℝ) - 1)) * (1 / 8) := mul_le_mul_of_nonneg_left h8' hpos
      _ = _ := by ring
  have hqS : BridgeLemma.qS D ≤ X / 8 := by
    unfold BridgeLemma.qS
    simp_rw [hterm]
    rw [hXdef, ← tsum_div_const]
    exact Summable.tsum_le_tsum hle8
      (Summable.of_nonneg_of_le (fun p => by positivity) hle8 (hsumX.div_const 8)) (hsumX.div_const 8)
  have hq0 : 0 ≤ BridgeLemma.qS D := by
    unfold BridgeLemma.qS
    exact tsum_nonneg fun p => zpow_nonneg (Nat.cast_nonneg _) _
  have hE : Real.exp (8 * BridgeLemma.qS D) ≤ 1 + 2 * X := by
    have h0 : 0 ≤ 8 * BridgeLemma.qS D := by positivity
    have h1' : 8 * BridgeLemma.qS D ≤ X := by linarith
    have hb := Real.exp_bound_div_one_sub_of_interval h0 (by linarith : 8 * BridgeLemma.qS D < 1)
    refine le_trans hb ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  unfold eSum
  rw [hsR]
  rw [← hXdef]
  have h4 : (0 : ℝ) ≤ 1 + 4 * X := by linarith
  calc (1 + 4 * X) * Real.exp (8 * BridgeLemma.qS D) ≤ (1 + 4 * X) * (1 + 2 * X) := mul_le_mul_of_nonneg_left hE h4
    _ ≤ 1 + Ce * X := by nlinarith

end PrimeSum

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartR2

section PartS1

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.LocalBesselAndTopKernel Formalism.MainNotions.BridgeLemma

section S27

theorem schur_family_of_open {eps : ℝ} (Fm : FamP eps) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Cw : ℝ)
    (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) u u', LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' Cw)
    (Z : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (X x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ) (Vm : ∀ k r, ValMap k r)
    {C0 Cg cb Cu cT CT Ca Cq CA CA' Ce : ℝ} (hCA : 0 ≤ CA) (hCl : 8 ≤ sCl Fm) (hCe : 8 ≤ Ce)
    (S : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      hyp (Fm.D x i) (Fm.L x i) C0 (sC' Fm) (sCl Fm) Cg cb Cu cT CT →
        AmplitudeIsBesselCoefficient (Fm.D x i) (Fm.L x i) (X x hx i) Cw (Y x hx i) ∧
        ColumnDecomposition (Fm.D x i) (Fm.L x i) (X x hx i) Cw (Y x hx i) (Vm _ _) ∧
        ParamsBound (Fm.D x i) (Fm.L x i) (X x hx i) Cw (Y x hx i) (Z x hx i) (cN x i)) :
    PeriodFamilyStatement Fm X Cw Y Z cN Vm C0 Cg cb Cu cT CT Ca Cq CA CA' Ce := by
  obtain ⟨x0, hS⟩ := S
  refine family_theorem_S_of_estimates (Ce₀ := 4) Fm X Cw Y Z cN Vm hCA hCl ⟨x0, fun x hx hx1 i hH => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hS x hx hx1 i hH
  have h1 : (Fm.D x i).R.m ^ 4 ≤ (Fm.D x i).R.f := hH.2.1.2.2.1
  have h2 : (Fm.D x i).R.f ≤ (Fm.D x i).R.k := hH.2.1.2.2.2.1
  exact ⟨a1, prime_sum_step_of_ranks (Fm.D x i) 4 le_rfl h1 h2, density_factor_absorbed (Fm.D x i) Ce hCe h1 h2, a2, a3⟩

end S27

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartS1

section PartM1

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants

section Homog

variable {k r : ℕ}

theorem muS_smul (μW μN : Measure (Mt k r)) [SFinite μN] (c : ℝ≥0∞) : muS μW (c • μN) = c • muS μW μN := by
  unfold muS
  rw [Measure.prod_smul_right, Measure.map_smul]

theorem quot_smul {μG μS ν : Measure (Mt k r)} (h : IsQuotMeas μG μS ν) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc1 : c ≠ ⊤) :
    IsQuotMeas μG (c • μS) (c⁻¹ • ν) := by
  intro f hf
  rw [h f hf, lintegral_smul_measure]
  simp_rw [lintegral_smul_measure]
  simp only [smul_eq_mul]
  rw [lintegral_const_mul' _ _ hc1, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hc1, one_mul]

theorem l2SG_const_smul {Wp : Type*} [NormedAddCommGroup Wp] (ν : Measure (Mt k r)) (c : ℝ≥0∞)
    (W : MatKR k r → Wp) : l2SG (c • ν) W = c * l2SG ν W := by
  unfold l2SG; rw [lintegral_smul_measure]; rfl

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (t : ℝ) (A : Wq →L[ℂ] Wp) :
    hsNormSq ((t : ℂ) • A) = t ^ 2 * hsNormSq A := by
  unfold hsNormSq hsInner
  simp only [_root_.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_assoc]
  have : ((t : ℂ) * (t : ℂ)) = ((t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.re_ofReal_mul]

end Homog

section Scale

variable (D : D7)

theorem kapN_eq (θ : ℝ) (hθ : 0 < θ) : kapN D 1 = (ENNReal.ofReal θ)⁻¹ * kapN D θ := by
  unfold kapN
  have h0 : 0 ≤ (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) := by
    have := Inh.amp_v_pos D; positivity
  rw [mul_one, ENNReal.ofReal_mul h0, ← mul_assoc, mul_comm (ENNReal.ofReal θ)⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel (by simpa using hθ) ENNReal.ofReal_ne_top, mul_one]

def Wone (θ : ℝ) (W : LocW D.R.k D.R.rS) : LocW D.R.k D.R.rS :=
  { W with μN := (ENNReal.ofReal θ)⁻¹ • W.μN, νS := ENNReal.ofReal θ • W.νS, νS' := ENNReal.ofReal θ • W.νS' }

def Aone (θ : ℝ) {W : LocW D.R.k D.R.rS} (A : LocS W) : LocS (Wone D θ W) :=
  { H := A.H, σ := A.σ, B := A.B, B' := A.B', v0 := A.v0, cN := θ * A.cN, deg := A.deg }

theorem goodW_one {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} (hθ : 0 < θ) {W : LocW D.R.k D.R.rS}
    (hW : GoodW D τ w w' θ W) : GoodW D τ w w' 1 (Wone D θ W) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hW
  have hc0 : (ENNReal.ofReal θ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hc1 : (ENNReal.ofReal θ)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by simpa using hθ)
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, ?_, ?_⟩
  · show (ENNReal.ofReal θ)⁻¹ • W.μN = haarLie (Nset D.R.k D.R.rS) (kapN D 1)
    rw [h12, kapN_eq D θ hθ]
    unfold haarLie
    rw [smul_smul]
  · show IsQuotMeas W.μG (muS W.μW ((ENNReal.ofReal θ)⁻¹ • W.μN)) (ENNReal.ofReal θ • W.νS)
    have : SFinite W.μN := by rw [h12]; unfold haarLie; infer_instance
    rw [muS_smul]
    have := quot_smul h13 hc0 hc1
    rwa [inv_inv] at this
  · show IsQuotMeas W.μG (muS W.μW' ((ENNReal.ofReal θ)⁻¹ • W.μN)) (ENNReal.ofReal θ • W.νS')
    have : SFinite W.μN := by rw [h12]; unfold haarLie; infer_instance
    rw [muS_smul]
    have := quot_smul h14 hc0 hc1
    rwa [inv_inv] at this

theorem goodS_one {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {θ : ℝ} (hθ : 0 < θ) {W : LocW D.R.k D.R.rS}
    {A : LocS W} (hA : GoodS D lam A) : GoodS D lam (Aone D θ A) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hA
  refine ⟨h1, h2, h3, h4, h5, h6, h7, mul_pos hθ h8, ?_, ?_, h11⟩
  · show l2SG (ENNReal.ofReal θ • W.νS) A.Φ = ENNReal.ofReal (θ * A.cN * Module.finrank ℂ W.Wp)
    rw [l2SG_const_smul, h9, ← ENNReal.ofReal_mul hθ.le, mul_assoc]
  · show l2SG (ENNReal.ofReal θ • W.νS') A.Φ' = ENNReal.ofReal (θ * A.cN * Module.finrank ℂ W.Wq)
    rw [l2SG_const_smul, h10, ← ENNReal.ofReal_mul hθ.le, mul_assoc]

theorem ampJ_mul {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [CompleteSpace Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (ν : Measure (Mt D.R.k D.R.rS)) (θ c : ℝ) (Φ : MatKR D.R.k D.R.rS → Wp)
    (Φ' : MatKR D.R.k D.R.rS → Wq) (γ : MatKR D.R.k D.R.rS) :
    ampJ ν (θ * c) Φ Φ' γ = ((θ⁻¹ : ℝ) : ℂ) • ampJ ν c Φ Φ' γ := by
  unfold ampJ
  rw [smul_smul]
  congr 1
  push_cast
  rw [mul_inv]

theorem MMv_one {θ : ℝ} (hθ : 0 < θ) {W : LocW D.R.k D.R.rS} (w w' : D.what₂.Word) (A : LocS W)
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) :
    MMv D w w' A μsec = ENNReal.ofReal (θ ^ 2) * MMv D w w' (Aone D θ A) μsec := by
  show ∫⁻ q : (Fin D.R.rS → ℂ) × ℂ, ENNReal.ofReal (bcWeight D.R.k D.R.rS (Tr D w) (Tr D w') q *
      hsNormSq (ampJ W.μG A.cN A.Φ A.Φ' (bigCell D.R.k D.R.rS q.1 (μsec q.2)))) =
    ENNReal.ofReal (θ ^ 2) * ∫⁻ q : (Fin D.R.rS → ℂ) × ℂ, ENNReal.ofReal (bcWeight D.R.k D.R.rS (Tr D w) (Tr D w') q *
      hsNormSq (ampJ W.μG (θ * A.cN) A.Φ A.Φ' (bigCell D.R.k D.R.rS q.1 (μsec q.2))))
  simp_rw [ampJ_mul D, hsNormSq_smul]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext q
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end Scale

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartM1

section PartM2

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Formalism.MainNotions.UniformConstantsAndStatements ValuativeRel IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main

variable (D : D7)

def dimU (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  vand (uS D u τ) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)

def schurB (u u' : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  (Tr D u * Tr D u') ^ (D.R.k - 1) *
    (dimU D u τ * dimU D u' τ * UnitaryVolumeMass.volU D.R.r * UnitaryVolumeMass.volU (D.R.k - 1) /
      (D.dsig τ * UnitaryVolumeMass.volU D.R.k ^ 2 * (2 * D.host.v) ^ (2 * D.R.rS * D.R.k)))

def MainCount (large₂ : SizeData₂ D) (h : LargenessConstants) (C Cb Ce : ℝ) : Prop :=
  Hyp D large₂ h → ∀ u u' : D.what₂.Word,
    ∃ (cInf : ℝ) (constP : HeightOneSpectrum (𝓞 D.host.F) → ℝ)
      (dens : Cnt.GramM D → HeightOneSpectrum (𝓞 D.host.F) → ℝ),
      0 < cInf ∧ (∀ p, 0 < constP p) ∧ Multipliable constP ∧ 0 < ∏' p, constP p ∧
      (∀ Z p, |dens Z p - 1| ≤ C * (Ideal.absNorm p.asIdeal : ℝ) ^ (-((D.R.k : ℝ) - 2 * D.R.rS - 3))) ∧
      (∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
        ∀ what₂ : Finset (Cnt.LatV D), IsRowReps D F0 what₂ →
        ∀ Z : Cnt.GramM D, (∀ τ, 0 < Cnt.Gz D (Tr D u) (Tr D u') Z τ) →
          (∃ Λ ∈ what₂, ∃ F' : Cnt.FlagU D u', IsNormFrame D Λ (lf D F0) F' ∧ Lat.ZhatL (lf D F0) F' = Z) →
          Multipliable (dens Z) ∧
          nuTot D u u' F0 what₂ Z =
            ENNReal.ofReal (cInf * (∏' p, constP p) * (∏' p, dens Z p) *
              ∏ τ, Cnt.Gz D (Tr D u) (Tr D u') Z τ ^ ((D.R.k : ℝ) - 1))) ∧
      ENNReal.ofReal (gaG D * (cInf * ∏' p, constP p)) * ∏ τ, ENNReal.ofReal (schurB D u u' τ) ≤
        ENNReal.ofReal (large₂.sc.b ^ (Cb * (D.R.m : ℝ) ^ 2 * (Fintype.card D.what₂.Tau : ℝ)) *
          ((1 + eSum D Ce) * ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar))

variable {D}

theorem hypTT_all (u u' : D.what₂.Word) : HypTT D u u' := by
  have hg0 := (D.host.g_prime 0).two_le
  have hg1 := (D.host.g_prime 1).two_le
  set G := D.host.g 0 * D.host.g 1 with hG
  have hG4 : 4 ≤ G := by nlinarith
  have hGG : 1 < G ^ 2 := by nlinarith
  have t1 := T_mod D u
  have t2 := T_mod D u'
  rw [Nat.mod_eq_of_lt hGG] at t1 t2
  have p1 := (D.mem u).A.T_prime
  have p2 := (D.mem u').A.T_prime
  have three : ∀ T : ℕ, T.Prime → T % G ^ 2 = 1 → 3 ≤ T := by
    intro T hT hm
    by_contra h3
    have : T < 3 := by omega
    interval_cases T
    · exact Nat.not_prime_zero hT
    · exact Nat.not_prime_one hT
    · rw [Nat.mod_eq_of_lt (by nlinarith)] at hm; omega
  refine ⟨p1, p2, three _ p1 t1, three _ p2 t2, ?_⟩
  have hm : (D.mem u).A.T ≡ (D.mem u').A.T [MOD G ^ 2] := by
    unfold Nat.ModEq; rw [t1, t2]
  have hm' : (D.mem u).A.T ≡ (D.mem u').A.T [MOD G] := Nat.ModEq.of_dvd (Dvd.intro_left _ (sq G).symm) hm
  exact Int.natCast_modEq_iff.2 hm'

theorem finrank_cols (hW : LocalBesselAndTopKernel.AdmittedWeylDimension) {u : D.what₂.Word} {τ : D.what₂.Tau} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ} {π : MatKR D.R.k D.R.rS → (H →L[ℂ] H)}
    (h : IsColsType D u τ z π) : (Module.finrank ℂ H : ℝ) = dimU D u τ := by
  obtain ⟨g, -, hU⟩ := h
  exact hW D.R.k (uS D u τ) H _ (Inh.obj_isHCParam_u D.R (D.hcW u τ)).1 hU

theorem MMv_le (hWe : LocalBesselAndTopKernel.AdmittedWeylDimension) {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 CS : ℝ}
    (hS : UnitaryVolumeMass.stSchur D large₂ C' Cl Cg cb Cu cT CT C0 0 CS) (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    {τ : D.what₂.Tau} {u u' : D.what₂.Word} {θ : ℝ} (hθ : 0 < θ) {W : LocW D.R.k D.R.rS} (hW : GoodW D τ u u' θ W)
    {A : LocS W} (hA : GoodS D (lamD D τ) A) (hdeg : A.deg = D.dsig τ)
    {μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ} (hsec : IsSection D.R.k D.R.rS W.z W.z' μsec) :
    MMv D u u' A μsec ≤ ENNReal.ofReal (θ ^ 2) * (ENNReal.ofReal (schurB D u u' τ) *
      ENNReal.ofReal (large₂.sc.b ^ (CS * (D.R.m : ℝ) ^ 2))) := by
  rw [MMv_one D hθ u u' A μsec]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  have hwin : normWin D large₂ 0 1 := by unfold normWin; simp
  have := hS hH τ u u' (hypTT_all u u') 1 hwin (Wone D θ W) (goodW_one D hθ hW) (Aone D θ A) (goodS_one D hθ hA)
    μsec hsec
  refine le_trans this (le_of_eq ?_)
  have e1 : (Module.finrank ℂ (Wone D θ W).Wp : ℝ) = dimU D u τ := finrank_cols hWe hW.1
  have e2 : (Module.finrank ℂ (Wone D θ W).Wq : ℝ) = dimU D u' τ := finrank_cols hWe hW.2.1
  have e3 : (Aone D θ A).deg = D.dsig τ := hdeg
  rw [e1, e2, e3, ← ENNReal.ofReal_mul' (by unfold Scale.b; positivity)]
  rfl

end Main

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartM2

section PartM3

noncomputable section

namespace Formalism.MainNotions.SchurRelationsDiscreteSeries

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Formalism.MainNotions.UniformConstantsAndStatements ValuativeRel IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main2

variable {D : D7}

theorem rpow_le_of_exp {b x y : ℝ} (hb : 1 ≤ b) (h : x ≤ y) : b ^ x ≤ b ^ y := Real.rpow_le_rpow_of_exponent_le hb h

theorem lemma_M_prime_hypothesis (hWe : LocalBesselAndTopKernel.AdmittedWeylDimension) {large₂ : SizeData₂ D} {h : LargenessConstants} {C Cb Ce CS : ℝ}
    (hS : UnitaryVolumeMass.stSchur D large₂ h.C' h.Cl h.Cg h.cb h.Cu h.cT h.CT h.C0 0 CS) (hM : MainCount D large₂ h C Cb Ce)
    (hle : CS + Cb ≤ C) : adm8 D large₂ h C Ce := by
  intro hH u u'
  obtain ⟨cInf, constP, dens, p1, p2, p3, p4, p5, p6, pK⟩ := hM hH u u'
  refine ⟨cInf, constP, dens, p1, p2, p3, p4, p5, p6, fun θ hθ W hW A hA hdeg μsec hsec => ?_⟩
  have hH0 : Cnt.Hyp0 D large₂ h.C' h.Cl h.Cg h.cb h.Cu h.cT h.CT h.C0 := ⟨hH.2.1, hH.1, hH.2.2⟩
  have hb0 : 0 < large₂.sc.b := by unfold Scale.b; positivity
  have hb1 : 1 ≤ large₂.sc.b := (BridgeLemma.std_b_gt D large₂).le
  set f := Fintype.card D.what₂.Tau with hf
  set m2 : ℝ := (D.R.m : ℝ) ^ 2 with hm2
  set X : ℝ := (1 + eSum D Ce) * ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar with hX
  set G := ENNReal.ofReal (gaG D * (cInf * ∏' p, constP p)) with hG
  have hprod : ∏ τ, MMv D u u' (A τ) (μsec τ) ≤
      ∏ τ, (ENNReal.ofReal (θ ^ 2) * (ENNReal.ofReal (schurB D u u' τ) * ENNReal.ofReal (large₂.sc.b ^ (CS * m2)))) :=
    Finset.prod_le_prod' fun τ _ => MMv_le hWe hS hH0 hθ (hW τ) (hA τ) (hdeg τ) (hsec τ)
  have hsplit : ∏ τ, (ENNReal.ofReal (θ ^ 2) * (ENNReal.ofReal (schurB D u u' τ) * ENNReal.ofReal (large₂.sc.b ^ (CS * m2)))) =
      ENNReal.ofReal (θ ^ (2 * f)) * ENNReal.ofReal (large₂.sc.b ^ (CS * m2 * (f : ℝ))) *
        ∏ τ, ENNReal.ofReal (schurB D u u' τ) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Finset.card_univ,
      ← hf, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by positivity), ← pow_mul,
      ← Real.rpow_natCast (large₂.sc.b ^ (CS * m2)), ← Real.rpow_mul hb0.le]
    ring
  calc G * ∏ τ, MMv D u u' (A τ) (μsec τ)
      ≤ G * (ENNReal.ofReal (θ ^ (2 * f)) * ENNReal.ofReal (large₂.sc.b ^ (CS * m2 * (f : ℝ))) *
          ∏ τ, ENNReal.ofReal (schurB D u u' τ)) := by rw [← hsplit]; exact mul_le_mul_of_nonneg_left hprod zero_le
    _ = ENNReal.ofReal (θ ^ (2 * f)) * ENNReal.ofReal (large₂.sc.b ^ (CS * m2 * (f : ℝ))) *
          (G * ∏ τ, ENNReal.ofReal (schurB D u u' τ)) := by ring
    _ ≤ ENNReal.ofReal (θ ^ (2 * f)) * ENNReal.ofReal (large₂.sc.b ^ (CS * m2 * (f : ℝ))) *
          ENNReal.ofReal (large₂.sc.b ^ (Cb * m2 * (f : ℝ)) * X) := mul_le_mul_of_nonneg_left pK zero_le
    _ = ENNReal.ofReal (θ ^ (2 * f) * large₂.sc.b ^ ((CS + Cb) * m2 * (f : ℝ)) * X) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show (CS + Cb) * m2 * (f : ℝ) = CS * m2 * f + Cb * m2 * f by ring, Real.rpow_add hb0]
        ring
    _ ≤ ENNReal.ofReal (θ ^ (2 * f) * large₂.sc.b ^ (C * m2 * (f : ℝ)) * X) := by
        rcases le_or_gt 0 X with hX0 | hX0
        · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hX0)
          refine mul_le_mul_of_nonneg_left (rpow_le_of_exp hb1 ?_) (by positivity)
          have : 0 ≤ m2 * (f : ℝ) := by positivity
          nlinarith
        · rw [ENNReal.ofReal_of_nonpos]
          · exact zero_le
          · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hX0.le

variable {eps : ℝ} (Fm : FamP eps)

theorem pMain_of_open (g : Given) (hWe : LocalBesselAndTopKernel.AdmittedWeylDimension) {C Cb Ce CS : ℝ} (hle : CS + Cb ≤ C)
    (hS : OwnEv Fm fun C' Cl x i => UnitaryVolumeMass.stSchur (Fm.D x i) (Fm.L x i) C' Cl g.Cg g.cb g.Cu g.cT g.CT g.C0 0 CS)
    (hM : OwnEv Fm fun C' Cl x i => MainCount (Fm.D x i) (Fm.L x i) (g.wth C' Cl) C Cb Ce) :
    PX.MainF Fm g C Ce := by
  obtain ⟨x1, h1⟩ := hS
  obtain ⟨x2, h2⟩ := hM
  exact ⟨max x1 x2, fun x hx i => lemma_M_prime_hypothesis hWe (h1 x (le_trans (le_max_left _ _) hx) i)
    (h2 x (le_trans (le_max_right _ _) hx) i) hle⟩

theorem pMain_of_fields (C0 : ℝ) (h1 : 1 ≤ C0) (hWe : LocalBesselAndTopKernel.FirstSizeStatement) {CM Ce : ℝ}
    (hS : ∀ Cg cb Cu cT CT C0 C1', PX.Schur Fm Cg cb Cu cT CT C0 C1')
    (hM : ∀ CS : ℝ, OwnEv Fm fun C' Cl x i => MainCount (Fm.D x i) (Fm.L x i) ((gS Fm C0 h1).wth C' Cl) CM (CM - CS) Ce) :
    PX.MainF Fm (gS Fm C0 h1) CM Ce := by
  obtain ⟨CS, hCS⟩ := hS (gS Fm C0 h1).Cg (gS Fm C0 h1).cb (gS Fm C0 h1).Cu (gS Fm C0 h1).cT (gS Fm C0 h1).CT
    (gS Fm C0 h1).C0 0
  exact pMain_of_open Fm (gS Fm C0 h1) hWe (by linarith) hCS (hM CS)

end Main2

end Formalism.MainNotions.SchurRelationsDiscreteSeries

end

end PartM3
