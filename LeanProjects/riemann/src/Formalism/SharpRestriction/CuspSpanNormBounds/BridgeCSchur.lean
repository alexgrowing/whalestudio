import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.BridgeCSchur

open Formalism.MainNotions.S

section Schur

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem schur_selfAdjoint (𝒰 : Set (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ U ∈ 𝒰, ∀ v ∈ S, U v ∈ S) → S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hcomm : ∀ U ∈ 𝒰, Commute A U) : ∃ c : ℝ, A = (c : ℂ) • (1 : H →L[ℂ] H) := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · exact ⟨0, by
      ext x
      exact Subsingleton.elim _ _⟩
  haveI : Nontrivial (H →L[ℂ] H) := by
    obtain ⟨e, he⟩ := exists_ne (0 : H)
    exact ⟨⟨0, 1, fun h0 => he (by simpa using (congrArg (fun T : H →L[ℂ] H => T e) h0).symm)⟩⟩
  have hcom : ∀ (φ : ℝ → ℝ), ∀ U ∈ 𝒰, Commute (cfc φ A) U := by
    intro φ U hU
    first
    | exact (hcomm U hU).cfc_real φ
    | exact Commute.cfc_real (hcomm U hU) φ
    | exact (hcomm U hU).cfc (by rw [hA.star_eq]; exact hcomm U hU) φ
  have hne0 : ∀ (φ : ℝ → ℝ) (u : ℝ), Continuous φ → u ∈ spectrum ℝ A → φ u ≠ 0 → cfc φ A ≠ 0 := by
    intro φ u hφ hu hφu h0
    have hmem : φ u ∈ spectrum ℝ (cfc φ A) := by
      first
      | (rw [cfc_map_spectrum φ A hA hφ.continuousOn]; exact ⟨u, hu, rfl⟩)
      | (rw [cfc_map_spectrum φ A]; exact ⟨u, hu, rfl⟩)
    rw [h0, spectrum.zero_eq, Set.mem_singleton_iff] at hmem
    exact hφu hmem
  have hsub : (spectrum ℝ A).Subsingleton := by
    intro s hs t ht
    by_contra hst
    have hδ : 0 < |s - t| / 2 := by
      have : 0 < |s - t| := abs_pos.2 (sub_ne_zero.2 hst)
      linarith
    have key : ∀ f g : ℝ → ℝ, Continuous f → Continuous g → (∀ x, f x * g x = 0) →
        f s ≠ 0 → g t ≠ 0 → False := by
      intro f g hf hg hfg hfs hgt
      have hF0 : cfc f A ≠ 0 := hne0 f s hf hs hfs
      have hG0 : cfc g A ≠ 0 := hne0 g t hg ht hgt
      have hz : (fun x => f x * g x) = fun _ => (0 : ℝ) := funext hfg
      have hFG : cfc f A * cfc g A = 0 := by
        first
        | rw [← cfc_mul f g A hf.continuousOn hg.continuousOn, hz, cfc_const (0 : ℝ) A hA, map_zero]
        | rw [← cfc_mul f g A, hz, cfc_const (0 : ℝ) A hA, map_zero]
      let K : Submodule ℂ H := LinearMap.ker ((cfc f A : H →L[ℂ] H) : H →ₗ[ℂ] H)
      have hKc : IsClosed (K : Set H) := (cfc f A).isClosed_ker
      have hKi : ∀ U ∈ 𝒰, ∀ v ∈ K, U v ∈ K := by
        intro U hU v hv
        have hv' : cfc f A v = 0 := LinearMap.mem_ker.1 hv
        apply LinearMap.mem_ker.2
        show cfc f A (U v) = 0
        have hc := congrArg (fun T : H →L[ℂ] H => T v) (hcom f U hU).eq
        simp only [ContinuousLinearMap.mul_apply] at hc
        rw [hc, hv', map_zero]
      rcases hirr K hKc hKi with hbot | htop
      · apply hG0
        ext y
        have hy : cfc g A y ∈ K := by
          apply LinearMap.mem_ker.2
          show cfc f A (cfc g A y) = 0
          rw [← ContinuousLinearMap.mul_apply, hFG, ContinuousLinearMap.zero_apply]
        rw [hbot, Submodule.mem_bot] at hy
        rw [hy, ContinuousLinearMap.zero_apply]
      · apply hF0
        ext y
        have hy : y ∈ K := by
          rw [htop]
          exact Submodule.mem_top
        rw [ContinuousLinearMap.zero_apply]
        exact LinearMap.mem_ker.1 hy
    have hfc : Continuous fun x : ℝ => max 0 (|s - t| / 2 - |x - s|) := by
      first
      | fun_prop
      | exact continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).abs)
    have hgc : Continuous fun x : ℝ => max 0 (|s - t| / 2 - |x - t|) := by
      first
      | fun_prop
      | exact continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).abs)
    refine key _ _ hfc hgc (fun x => ?_) ?_ ?_
    · have hst' : |s - t| ≤ |x - s| + |x - t| := by
        have h3 := abs_sub_le s x t
        rw [abs_sub_comm s x] at h3
        exact h3
      by_cases h1 : |s - t| / 2 ≤ |x - s|
      · rw [max_eq_left (show |s - t| / 2 - |x - s| ≤ 0 by linarith), zero_mul]
      · push_neg at h1
        rw [max_eq_left (show |s - t| / 2 - |x - t| ≤ 0 by linarith), mul_zero]
    · show max 0 (|s - t| / 2 - |s - s|) ≠ 0
      rw [sub_self, abs_zero, sub_zero, max_eq_right hδ.le]
      exact hδ.ne'
    · show max 0 (|s - t| / 2 - |t - t|) ≠ 0
      rw [sub_self, abs_zero, sub_zero, max_eq_right hδ.le]
      exact hδ.ne'
  have hne : (spectrum ℝ A).Nonempty := by
    first
    | exact CFC.spectrum_nonempty ℝ A hA
    | exact CFC.spectrum_nonempty ℝ A
  obtain ⟨c, hc⟩ := hne
  refine ⟨c, ?_⟩
  have h1 : cfc (fun x : ℝ => x) A = cfc (fun _ : ℝ => c) A :=
    cfc_congr (fun x hx => hsub hx hc)
  rw [cfc_id' ℝ A hA, cfc_const c A hA, Algebra.algebraMap_eq_smul_one] at h1
  rw [h1]
  first
  | exact (Complex.coe_smul c (1 : H →L[ℂ] H)).symm
  | exact RCLike.real_smul_eq_coe_smul (K := ℂ) c (1 : H →L[ℂ] H)
  | simp

theorem schur_bounded (𝒰 : Set (H →L[ℂ] H)) (hstar : ∀ U ∈ 𝒰, star U ∈ 𝒰)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ U ∈ 𝒰, ∀ v ∈ S, U v ∈ S) → S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hcomm : ∀ U ∈ 𝒰, Commute A U) : ∃ c : ℂ, A = c • (1 : H →L[ℂ] H) := by
  have hst : ∀ U ∈ 𝒰, Commute (star A) U := fun U hU => by
    have := (hcomm _ (hstar U hU)).star_star
    rwa [star_star] at this
  obtain ⟨c₁, h₁⟩ := schur_selfAdjoint 𝒰 hirr (realPart A : H →L[ℂ] H) (realPart A).2 (fun U hU => by
    rw [realPart_apply_coe]
    exact ((hcomm U hU).add_left (hst U hU)).smul_left _)
  obtain ⟨c₂, h₂⟩ := schur_selfAdjoint 𝒰 hirr (imaginaryPart A : H →L[ℂ] H) (imaginaryPart A).2
    (fun U hU => by
      rw [imaginaryPart_apply_coe]
      exact (((hcomm U hU).sub_left (hst U hU)).smul_left _).smul_left _)
  refine ⟨(c₁ : ℂ) + Complex.I * c₂, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart A]
  rw [h₁, h₂, smul_smul, ← add_smul]

end Schur

section Orth

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure SqRep (μ : Measure G) (ρ : G → (H →L[ℂ] H)) : Prop where
  one : ρ 1 = 1
  mul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)
  iso : ∀ g v, ‖ρ g v‖ = ‖v‖
  cont : ∀ v, Continuous fun g => ρ g v
  sq : ∀ v w, MemLp (fun g => ⟪w, ρ g v⟫_ℂ) 2 μ

variable {μ : Measure G} {ρ : G → (H →L[ℂ] H)}

theorem SqRep.inner_map (h : SqRep μ ρ) (g : G) (x y : H) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  first
  | exact (⟨(ρ g : H →ₗ[ℂ] H), h.iso g⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y
  | exact LinearIsometry.inner_map_map { toLinearMap := (ρ g : H →ₗ[ℂ] H), norm_map' := h.iso g } x y

theorem SqRep.inv_apply (h : SqRep μ ρ) (g : G) (x : H) : ρ g (ρ g⁻¹ x) = x := by
  have e : ρ (g * g⁻¹) x = ρ g (ρ g⁻¹ x) := by
    rw [h.mul] <;> rfl
  rw [← e]
  simp [h.one]

theorem SqRep.inner_left (h : SqRep μ ρ) (g : G) (x y : H) : ⟪ρ g x, y⟫_ℂ = ⟪x, ρ g⁻¹ y⟫_ℂ := by
  rw [← h.inner_map g x (ρ g⁻¹ y), h.inv_apply]

private theorem star_inner_lemma_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) :
    star ⟪x, y⟫_ℂ = ⟪y, x⟫_ℂ := by
  first
  | exact inner_conj_symm y x
  | exact inner_conj_symm x y
  | simp

theorem SqRep.memLp' (h : SqRep μ ρ) (v w : H) : MemLp (fun g => ⟪ρ g v, w⟫_ℂ) 2 μ := by
  have e : (fun g => ⟪ρ g v, w⟫_ℂ) = fun g => star ⟪w, ρ g v⟫_ℂ := by
    funext g
    exact (star_inner_lemma_2 w (ρ g v)).symm
  rw [e]
  first
  | exact (h.sq v w).congr_norm (h.sq v w).1.star (ae_of_all _ fun g => (norm_star _).symm)
  | exact (h.sq v w).star
  | exact (h.sq v w).congr_norm (continuous_star.comp_aestronglyMeasurable (h.sq v w).1)
      (ae_of_all _ fun g => (norm_star _).symm)

def Tlin (h : SqRep μ ρ) (v : H) : H →ₗ[ℂ] Lp ℂ 2 μ where
  toFun w := (h.memLp' v w).toLp _
  map_add' w w' := by
    rw [← MemLp.toLp_add]
    congr 1
    funext g
    simp [inner_add_right]
  map_smul' c w := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    congr 1
    funext g
    simp [inner_smul_right]

theorem Tlin_coe (h : SqRep μ ρ) (v w : H) : (Tlin h v w : G → ℂ) =ᵐ[μ] fun g => ⟪ρ g v, w⟫_ℂ := by
  first
  | exact (h.memLp' v w).coeFn_toLp
  | exact MemLp.coeFn_toLp _

variable [CompleteSpace H]

theorem Tlin_cont (h : SqRep μ ρ) (v : H) : Continuous (Tlin h v) := by
  refine LinearMap.continuous_of_seq_closed_graph (Tlin h v) ?_
  intro u x y hu hy
  have h2 : Filter.Tendsto (fun n => eLpNorm (⇑(Tlin h v (u n)) - ⇑y) 2 μ) Filter.atTop (nhds 0) := by
    first
    | exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n => Tlin h v (u n)) y).1 hy
    | exact Lp.tendsto_Lp_iff_tendsto_eLpNorm'.1 hy
  have hm : TendstoInMeasure μ (fun n => ⇑(Tlin h v (u n))) Filter.atTop ⇑y :=
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun n => Lp.aestronglyMeasurable _)
      (Lp.aestronglyMeasurable _) h2
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  have hall : ∀ᵐ g ∂μ, ∀ n, (Tlin h v (u n) : G → ℂ) g = ⟪ρ g v, u n⟫_ℂ :=
    ae_all_iff.2 fun n => Tlin_coe h v (u n)
  refine Lp.ext ?_
  filter_upwards [hae, hall, Tlin_coe h v x] with g hg hg' hx
  rw [hx]
  have ht : Filter.Tendsto (fun i => ⟪ρ g v, u (ns i)⟫_ℂ) Filter.atTop (nhds ⟪ρ g v, x⟫_ℂ) :=
    (tendsto_const_nhds (x := ρ g v)).inner (hu.comp hns.tendsto_atTop)
  have hg2 : Filter.Tendsto (fun i => ⟪ρ g v, u (ns i)⟫_ℂ) Filter.atTop (nhds (y g)) := by
    simpa only [hg'] using hg
  exact tendsto_nhds_unique hg2 ht

def Tcl (h : SqRep μ ρ) (v : H) : H →L[ℂ] Lp ℂ 2 μ := ⟨Tlin h v, Tlin_cont h v⟩

private theorem innerC_lemma (a b : ℂ) : ⟪a, b⟫_ℂ = star a * b := by
  first
  | (simp only [RCLike.inner_apply, starRingEnd_apply]; done)
  | (simp only [RCLike.inner_apply, starRingEnd_apply]; ring)
  | simp [mul_comm]

theorem Tcl_inner (h : SqRep μ ρ) (v v' w w' : H) :
    ⟪Tcl h v w, Tcl h v' w'⟫_ℂ = ∫ g, ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ ∂μ := by
  show ⟪(Tlin h v w : Lp ℂ 2 μ), Tlin h v' w'⟫_ℂ = _
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Tlin_coe h v w, Tlin_coe h v' w'] with g h1 h2
  rw [h1, h2, innerC_lemma, star_inner_lemma_2 (ρ g v) w, star_inner_lemma_2 w' (ρ g v')]

end Orth

section Orth

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul G] [MeasurableInv G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {μ : Measure G} {ρ : G → (H →L[ℂ] H)}

def Iint (μ : Measure G) (ρ : G → (H →L[ℂ] H)) (v w v' w' : H) : ℂ := ∫ g, ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ ∂μ

theorem Iint_left [μ.IsMulLeftInvariant] (h : SqRep μ ρ) (a : G) (v w v' w' : H) :
    Iint μ ρ v (ρ a w) v' (ρ a w') = Iint μ ρ v w v' w' := by
  unfold Iint
  have e : ∀ g, ⟪ρ a w, ρ g v⟫_ℂ * star ⟪ρ a w', ρ g v'⟫_ℂ
      = ⟪w, ρ (a⁻¹ * g) v⟫_ℂ * star ⟪w', ρ (a⁻¹ * g) v'⟫_ℂ := by
    intro g
    rw [h.inner_left a w, h.inner_left a w', h.mul] <;> rfl
  simp_rw [e]
  first
  | exact integral_mul_left_eq_self (fun g => ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ) a⁻¹
  | exact integral_mul_left_eq_self (μ := μ) (fun g => ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ) a⁻¹

theorem Iint_inv [μ.IsInvInvariant] (h : SqRep μ ρ) (v w v' w' : H) : Iint μ ρ v w v' w' = Iint μ ρ w' v' w v := by
  unfold Iint
  have e : ∀ g, ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ
      = ⟪v', ρ g⁻¹ w'⟫_ℂ * star ⟪v, ρ g⁻¹ w⟫_ℂ := by
    intro g
    rw [← h.inner_left g v' w', ← h.inner_left g v w, star_inner_lemma_2 w' (ρ g v'),
      star_inner_lemma_2 (ρ g v) w]
    exact mul_comm _ _
  simp_rw [e]
  first
  | exact integral_inv_eq_self (fun g => ⟪v', ρ g w'⟫_ℂ * star ⟪v, ρ g w⟫_ℂ) μ
  | exact integral_inv_eq_self (fun g => ⟪v', ρ g w'⟫_ℂ * star ⟪v, ρ g w⟫_ℂ)

theorem Iint_integrable (h : SqRep μ ρ) (v w v' w' : H) :
    Integrable (fun g => ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ) μ := by
  have hi := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (Tlin h v w) (Tlin h v' w')
  refine hi.congr ?_
  filter_upwards [Tlin_coe h v w, Tlin_coe h v' w'] with g h1 h2
  rw [h1, h2, innerC_lemma, star_inner_lemma_2 (ρ g v) w, star_inner_lemma_2 w' (ρ g v')]

variable [CompleteSpace H]

def Aop (h : SqRep μ ρ) (v v' : H) : H →L[ℂ] H := (ContinuousLinearMap.adjoint (Tcl h v)).comp (Tcl h v')

theorem Aop_inner (h : SqRep μ ρ) (v v' w w' : H) : ⟪w, Aop h v v' w'⟫_ℂ = Iint μ ρ v w v' w' := by
  exact (ContinuousLinearMap.adjoint_inner_right (Tcl h v) w (Tcl h v' w')).trans (Tcl_inner h v v' w w')

theorem Aop_comm [μ.IsMulLeftInvariant] (h : SqRep μ ρ) (v v' : H) (a : G) : Commute (Aop h v v') (ρ a) := by
  have key : ∀ w w' : H, ⟪w, Aop h v v' (ρ a w')⟫_ℂ = ⟪w, ρ a (Aop h v v' w')⟫_ℂ := by
    intro w w'
    have e1 : ⟪w, ρ a (Aop h v v' w')⟫_ℂ = ⟪ρ a⁻¹ w, Aop h v v' w'⟫_ℂ := by
      rw [h.inner_left a⁻¹ w, inv_inv]
    rw [e1, Aop_inner h v v' w (ρ a w'), Aop_inner h v v' (ρ a⁻¹ w) w',
      ← Iint_left h a v (ρ a⁻¹ w) v' w', h.inv_apply]
  show Aop h v v' * ρ a = ρ a * Aop h v v'
  ext w'
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  exact key w w'

theorem star_rho (h : SqRep μ ρ) (a : G) : star (ρ a) = ρ a⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [h.inner_left a⁻¹ x, inv_inv]

theorem schur_orth [μ.IsMulLeftInvariant] [μ.IsInvInvariant] [μ.IsOpenPosMeasure] [Nontrivial H] (h : SqRep μ ρ)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤) :
    ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H,
      Integrable (fun g => ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ) μ ∧
      ∫ g, ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by
  have hscal : ∀ v v' : H, ∃ c : ℂ, Aop h v v' = c • (1 : H →L[ℂ] H) := by
    intro v v'
    refine schur_bounded (Set.range ρ) ?_ ?_ (Aop h v v') ?_
    · rintro _ ⟨a, rfl⟩
      exact ⟨a⁻¹, (star_rho h a).symm⟩
    · intro S hS hinv
      exact hirr S hS (fun g x hx => hinv (ρ g) ⟨g, rfl⟩ x hx)
    · rintro _ ⟨a, rfl⟩
      exact Aop_comm h v v' a
  choose c hc using hscal
  have hI : ∀ v w v' w' : H, Iint μ ρ v w v' w' = c v v' * ⟪w, w'⟫_ℂ := by
    intro v w v' w'
    rw [← Aop_inner h v v' w w', hc v v', ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, inner_smul_right]
  obtain ⟨e, he⟩ := exists_ne (0 : H)
  have hn : (0 : ℝ) < ‖e‖ := norm_pos_iff.2 he
  have hc0 : Continuous fun g => ρ g e := h.cont e
  have hfc : Continuous fun g => ‖⟪e, ρ g e⟫_ℂ‖ ^ 2 := by
    first
    | exact (continuous_const.inner hc0).norm.pow 2
    | fun_prop
  have hfi : Integrable (fun g => ‖⟪e, ρ g e⟫_ℂ‖ ^ 2) μ := by
    have hi := (Iint_integrable h e e e e).norm
    refine hi.congr (ae_of_all _ fun g => ?_)
    simp only [norm_mul, norm_star, sq]
  have hpos : 0 < ∫ g, ‖⟪e, ρ g e⟫_ℂ‖ ^ 2 ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun g => sq_nonneg _) hfi]
    refine hfc.isOpen_support.measure_pos μ ⟨1, ?_⟩
    simp only [Function.mem_support, h.one, ContinuousLinearMap.one_apply]
    first
    | exact pow_ne_zero 2 (norm_ne_zero_iff.2 (inner_self_ne_zero.2 he))
    | simpa using he
  have hIe : Iint μ ρ e e e e = ((∫ g, ‖⟪e, ρ g e⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    unfold Iint
    first
    | rw [← integral_ofReal]
    | rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    show ⟪e, ρ g e⟫_ℂ * star ⟪e, ρ g e⟫_ℂ = ((‖⟪e, ρ g e⟫_ℂ‖ ^ 2 : ℝ) : ℂ)
    first
    | rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    | exact RCLike.mul_conj _
    | simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.star_def]
    | (rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_abs]; push_cast; ring)
  have hee : ⟪e, e⟫_ℂ = ((‖e‖ ^ 2 : ℝ) : ℂ) := by
    first
    | (rw [inner_self_eq_norm_sq_to_K]; norm_cast)
    | simp [inner_self_eq_norm_sq_to_K]
  have key : ∀ v v' : H, c v v' * ((‖e‖ ^ 2 : ℝ) : ℂ) = c e e * ⟪v', v⟫_ℂ := by
    intro v v'
    rw [← hee, ← hI v e v' e, Iint_inv h v e v' e, hI e v' e v]
  have hce : c e e * ((‖e‖ ^ 2 : ℝ) : ℂ) = ((∫ g, ‖⟪e, ρ g e⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← hee, ← hI e e e e, hIe]
  have hn' : ((‖e‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (pow_pos hn 2).ne'
  have hE : ((‖e‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
  have hI0 : ((∫ g, ‖⟪e, ρ g e⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  refine ⟨(‖e‖ ^ 2) ^ 2 / ∫ g, ‖⟪e, ρ g e⟫_ℂ‖ ^ 2 ∂μ, div_pos (pow_pos (pow_pos hn 2) 2) hpos,
    fun v w v' w' => ⟨Iint_integrable h v w v' w', ?_⟩⟩
  show Iint μ ρ v w v' w' = _
  have hcv : c v v' = c e e * ⟪v', v⟫_ℂ / ((‖e‖ ^ 2 : ℝ) : ℂ) := by
    rw [eq_div_iff hn', key v v']
  have hcee : c e e = ((∫ g, ‖⟪e, ρ g e⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) / ((‖e‖ ^ 2 : ℝ) : ℂ) := by
    rw [eq_div_iff hn', hce]
  rw [hI v w v' w', hcv, hcee]
  push_cast
  first
  | (field_simp; ring)
  | field_simp

end Orth

section Orth2

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul G] [MeasurableInv G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {μ : Measure G} {ρ : G → (H →L[ℂ] H)} {ρ' : G → (H' →L[ℂ] H')}

theorem Tcl_inner2 (h : SqRep μ ρ) (h' : SqRep μ ρ') (v w : H) (v' w' : H') :
    ⟪Tcl h v w, Tcl h' v' w'⟫_ℂ = ∫ g, ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ' g v'⟫_ℂ ∂μ := by
  show ⟪(Tlin h v w : Lp ℂ 2 μ), Tlin h' v' w'⟫_ℂ = _
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Tlin_coe h v w, Tlin_coe h' v' w'] with g h1 h2
  rw [h1, h2, innerC_lemma, star_inner_lemma_2 (ρ g v) w, star_inner_lemma_2 w' (ρ' g v')]

def Bop (h : SqRep μ ρ) (h' : SqRep μ ρ') (v : H) (v' : H') : H' →L[ℂ] H :=
  (ContinuousLinearMap.adjoint (Tcl h v)).comp (Tcl h' v')

theorem Bop_inner (h : SqRep μ ρ) (h' : SqRep μ ρ') (v w : H) (v' w' : H') :
    ⟪w, Bop h h' v v' w'⟫_ℂ = ∫ g, ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ' g v'⟫_ℂ ∂μ := by
  exact (ContinuousLinearMap.adjoint_inner_right (Tcl h v) w (Tcl h' v' w')).trans (Tcl_inner2 h h' v w v' w')

theorem Bop_tw [μ.IsMulLeftInvariant] (h : SqRep μ ρ) (h' : SqRep μ ρ') (v : H) (v' : H') (a : G) (w' : H') :
    Bop h h' v v' (ρ' a w') = ρ a (Bop h h' v v' w') := by
  apply ext_inner_left ℂ
  intro w
  have hinv : ∀ x : H', ρ' a⁻¹ (ρ' a x) = x := fun x => by
    have := h'.inv_apply a⁻¹ x
    rwa [inv_inv] at this
  have e1 : ⟪w, ρ a (Bop h h' v v' w')⟫_ℂ = ⟪ρ a⁻¹ w, Bop h h' v v' w'⟫_ℂ := by
    rw [h.inner_left a⁻¹ w, inv_inv]
  rw [e1, Bop_inner h h' v w v' (ρ' a w'), Bop_inner h h' v (ρ a⁻¹ w) v' w']
  have e : ∀ g, ⟪ρ a⁻¹ w, ρ g v⟫_ℂ * star ⟪w', ρ' g v'⟫_ℂ
      = ⟪w, ρ (a * g) v⟫_ℂ * star ⟪ρ' a w', ρ' (a * g) v'⟫_ℂ := by
    intro g
    rw [h.inner_left a⁻¹ w, inv_inv, h'.inner_left a w', h.mul, h'.mul,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hinv]
  simp_rw [e]
  first
  | exact (integral_mul_left_eq_self (fun g => ⟪w, ρ g v⟫_ℂ * star ⟪ρ' a w', ρ' g v'⟫_ℂ) a).symm
  | exact (integral_mul_left_eq_self (μ := μ) (fun g => ⟪w, ρ g v⟫_ℂ * star ⟪ρ' a w', ρ' g v'⟫_ℂ) a).symm

theorem equiv_of_intertwiner (h : SqRep μ ρ) (h' : SqRep μ ρ')
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hirr' : ∀ S : Submodule ℂ H', IsClosed (S : Set H') → (∀ g, ∀ v ∈ S, ρ' g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (B : H' →L[ℂ] H) (htw : ∀ a w', B (ρ' a w') = ρ a (B w')) (hB : B ≠ 0) :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g v, U (ρ g v) = ρ' g (U v) := by
  have hadj : ∀ a (x : H), (ContinuousLinearMap.adjoint B) (ρ a x)
      = ρ' a ((ContinuousLinearMap.adjoint B) x) := by
    intro a x
    apply ext_inner_left ℂ
    intro y
    have e1 : ⟪B y, ρ a x⟫_ℂ = ⟪ρ a⁻¹ (B y), x⟫_ℂ := by
      rw [h.inner_left a⁻¹ (B y), inv_inv]
    have e2 : ⟪y, ρ' a ((ContinuousLinearMap.adjoint B) x)⟫_ℂ
        = ⟪ρ' a⁻¹ y, (ContinuousLinearMap.adjoint B) x⟫_ℂ := by
      rw [h'.inner_left a⁻¹ y, inv_inv]
    rw [ContinuousLinearMap.adjoint_inner_right, e1, ← htw, e2, ContinuousLinearMap.adjoint_inner_right]
  obtain ⟨c, hc⟩ := schur_bounded (Set.range ρ')
    (by
      rintro _ ⟨a, rfl⟩
      exact ⟨a⁻¹, (star_rho h' a).symm⟩)
    (fun S hS hinv => hirr' S hS (fun g x hx => hinv (ρ' g) ⟨g, rfl⟩ x hx))
    ((ContinuousLinearMap.adjoint B).comp B)
    (by
      rintro _ ⟨a, rfl⟩
      show (ContinuousLinearMap.adjoint B).comp B * ρ' a = ρ' a * (ContinuousLinearMap.adjoint B).comp B
      ext w
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, htw, hadj])
  have hnorm : ∀ w : H', ((‖B w‖ ^ 2 : ℝ) : ℂ) = c * ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    intro w
    have e1 : ⟪w, ((ContinuousLinearMap.adjoint B).comp B) w⟫_ℂ = ⟪B w, B w⟫_ℂ := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    rw [hc, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right,
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e1
    push_cast
    exact e1.symm
  obtain ⟨w₀, hw₀⟩ : ∃ w, B w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hB (ContinuousLinearMap.ext hcon)
  have hw₀' : w₀ ≠ 0 := fun h0 => hw₀ (by rw [h0, map_zero])
  obtain ⟨r, hr, hBr⟩ : ∃ r : ℝ, 0 < r ∧ ∀ w, ‖B w‖ = r * ‖w‖ := by
    have hw0 : 0 < ‖w₀‖ := norm_pos_iff.2 hw₀'
    have hBw0 : 0 < ‖B w₀‖ := norm_pos_iff.2 hw₀
    refine ⟨‖B w₀‖ / ‖w₀‖, div_pos hBw0 hw0, fun w => ?_⟩
    have hc' : c = (((‖B w₀‖ / ‖w₀‖) ^ 2 : ℝ) : ℂ) := by
      have h0 := hnorm w₀
      have hne : ((‖w₀‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (pow_pos hw0 2).ne'
      rw [div_pow, Complex.ofReal_div, eq_div_iff hne, h0]
    have hreal : ‖B w‖ ^ 2 = (‖B w₀‖ / ‖w₀‖) ^ 2 * ‖w‖ ^ 2 := by
      have h1 := hnorm w
      rw [hc'] at h1
      exact_mod_cast h1
    calc ‖B w‖ = Real.sqrt (‖B w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt ((‖B w₀‖ / ‖w₀‖ * ‖w‖) ^ 2) := by rw [hreal, mul_pow]
      _ = ‖B w₀‖ / ‖w₀‖ * ‖w‖ := Real.sqrt_sq (mul_nonneg (div_pos hBw0 hw0).le (norm_nonneg _))
  let V : H' →ₗᵢ[ℂ] H :=
    { toLinearMap := ((((r⁻¹ : ℝ) : ℂ) • B : H' →L[ℂ] H) : H' →ₗ[ℂ] H)
      norm_map' := fun w => by
        show ‖(((r⁻¹ : ℝ) : ℂ) • B) w‖ = ‖w‖
        rw [ContinuousLinearMap.smul_apply, norm_smul, hBr w, Complex.norm_real, Real.norm_eq_abs,
          abs_inv, abs_of_pos hr, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul] }
  have hVtw : ∀ a w, V (ρ' a w) = ρ a (V w) := by
    intro a w
    show (((r⁻¹ : ℝ) : ℂ) • B) (ρ' a w) = ρ a ((((r⁻¹ : ℝ) : ℂ) • B) w)
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, htw, map_smul]
  have hsurj : Function.Surjective V := by
    have hcl : IsClosed (Set.range V) := by
      first
      | exact V.isometry.antilipschitz.isClosed_range V.isometry.uniformContinuous
      | exact V.isometry.isClosedEmbedding.isClosed_range
    let S : Submodule ℂ H := LinearMap.range V.toLinearMap
    have hS : (S : Set H) = Set.range V := by
      first
      | exact LinearMap.coe_range _
      | exact LinearMap.range_coe _
      | (ext x; exact LinearMap.mem_range)
    have hinv : ∀ g, ∀ x ∈ S, ρ g x ∈ S := by
      intro g x hx
      obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hx
      exact LinearMap.mem_range.2 ⟨ρ' g w, hVtw g w⟩
    rcases hirr S (by rw [hS]; exact hcl) hinv with hbot | htop
    · exfalso
      have hm : V.toLinearMap w₀ ∈ S := LinearMap.mem_range_self _ w₀
      rw [hbot, Submodule.mem_bot] at hm
      have h0 : V w₀ = 0 := hm
      have hn := V.norm_map w₀
      rw [h0, norm_zero] at hn
      exact hw₀' (norm_eq_zero.1 hn.symm)
    · intro x
      have hx : x ∈ S := by
        rw [htop]
        exact Submodule.mem_top
      obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hx
      exact ⟨w, hw⟩
  let E : H' ≃ₗᵢ[ℂ] H := LinearIsometryEquiv.ofSurjective V hsurj
  have hE : ∀ x, E x = V x := fun x => by
    first
    | rfl
    | simp [E]
  refine ⟨E.symm, fun g v => E.injective ?_⟩
  rw [LinearIsometryEquiv.apply_symm_apply, hE, hVtw, ← hE, LinearIsometryEquiv.apply_symm_apply]

theorem schur_orth_ineq [μ.IsMulLeftInvariant] (h : SqRep μ ρ) (h' : SqRep μ ρ')
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hirr' : ∀ S : Submodule ℂ H', IsClosed (S : Set H') → (∀ g, ∀ v ∈ S, ρ' g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hne : ¬ ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g v, U (ρ g v) = ρ' g (U v)) (v w : H) (v' w' : H') :
    ∫ g, ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ' g v'⟫_ℂ ∂μ = 0 := by
  have hB : Bop h h' v v' = 0 := by
    by_contra hB
    exact hne (equiv_of_intertwiner h h' hirr hirr' _ (fun a w' => Bop_tw h h' v v' a w') hB)
  rw [← Bop_inner h h' v w v' w', hB, ContinuousLinearMap.zero_apply, inner_zero_right]

end Orth2

section UJ

variable {n : ℕ} {ε : Fin n → Bool}

instance instInvInvMuG : (Formalism.REAL.muG ε).IsInvInvariant :=
  ⟨Formalism.REAL.invInvariant_of Formalism.REAL.indefinite_unitary_unimodular n ε⟩

theorem continuous_umat : Continuous (fun g : Formalism.REAL.UJ ε => umat g) := by
  first
  | exact Units.continuous_val.comp continuous_subtype_val
  | fun_prop
  | continuity

theorem umat_mem (g : Formalism.REAL.UJ ε) : umat g ∈ UJset ε := by
  first
  | exact g.2
  | exact g.prop

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sqRep_of {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : IsURepOn (UJset ε) σ) (hS : IsSqIntOn ε σ) :
    SqRep (Formalism.REAL.muG ε) (fun g : Formalism.REAL.UJ ε => σ (umat g)) where
  one := hU.1.1
  mul a b := hU.1.2 _ (umat_mem a) _ (umat_mem b)
  iso g v := hU.2.1 _ (umat_mem g) v
  cont v := (hU.2.2 v).comp_continuous continuous_umat umat_mem
  sq v w := hS v w

private theorem umat_surj_lemma {n : ℕ} {ε : Fin n → Bool} (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : g ∈ UJset ε) : ∃ u : Formalism.REAL.UJ ε, umat u = g := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    first
    | (unfold Formalism.REAL.Jm
       rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
       congr 1
       funext a
       split_ifs <;> norm_num)
    | (unfold Formalism.REAL.Jm
       ext i j
       by_cases hij : i = j
       · subst hij
         simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
         split_ifs <;> norm_num
       · simp [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij])
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have hl : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    calc (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g
        = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [hg']
      _ = 1 := hJ
  have hr : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := by
    first
    | exact mul_eq_one_comm.1 hl
    | (have h3 := Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse hl)
       rwa [Matrix.inv_eq_left_inv hl] at h3)
  first
  | exact ⟨⟨⟨g, _, hr, hl⟩, hg⟩, rfl⟩
  | exact ⟨⟨⟨g, _, hr, hl⟩, hg'⟩, rfl⟩

theorem irr_of {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hI : IsIrredOn (UJset ε) σ) :
    ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g : Formalism.REAL.UJ ε, ∀ v ∈ S, σ (umat g) v ∈ S) → S = ⊥ ∨ S = ⊤ := by
  intro S hS hinv
  refine hI S hS (fun g hg v hv => ?_)
  obtain ⟨u, rfl⟩ := umat_surj_lemma g hg
  exact hinv u v hv

theorem schur_UJ [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hN : Nontrivial H)
    (hU : IsURepOn (UJset ε) σ) (hI : IsIrredOn (UJset ε) σ) (hS : IsSqIntOn ε σ) :
    ∃ d : ℝ, IsFdeg (Formalism.REAL.muG ε) σ d := by
  haveI := hN
  haveI : (Formalism.REAL.muG ε).IsMulLeftInvariant := by
    first
    | infer_instance
    | (unfold Formalism.REAL.muG; infer_instance)
  haveI : (Formalism.REAL.muG ε).IsOpenPosMeasure := by
    first
    | infer_instance
    | (unfold Formalism.REAL.muG; infer_instance)
  obtain ⟨d, hd, hrel⟩ := schur_orth (μ := Formalism.REAL.muG ε) (sqRep_of hU hS) (irr_of hI)
  exact ⟨d, hd, hrel⟩

theorem fdeg_of_DS [CompleteSpace H] (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsDS ε lam σ) :
    ∃ d : ℝ, IsFdeg (Formalism.REAL.muG ε) σ d := by
  obtain ⟨_, hN, hU, hI, hS, _⟩ := h
  exact schur_UJ σ hN hU hI hS

end UJ

end Formalism.MainNotions.BridgeCSchur

end
