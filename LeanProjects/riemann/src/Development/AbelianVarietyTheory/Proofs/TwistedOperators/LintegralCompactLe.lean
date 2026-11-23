import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevIteratedOneParameterSubgroups

noncomputable section

open MeasureTheory
open scoped Topology Pointwise ENNReal

namespace GlobalTheory.ThetaGrowth

theorem sobolev_iter {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] (N : ℕ) :
    ∀ (P₀ : ℕ) (c : Fin N → ℝ → G) (A : ℕ → Set (G → ℂ)) (B : ℝ) (y : G), (∀ i, Continuous (c i)) → Monotone A →
    (∀ p, ∀ u ∈ A p, Continuous u ∧ ∀ i, ∃ v ∈ A (p + 1), ∀ x, ‖u x‖ ^ 2 ≤
      2 * (∫ r in (0 : ℝ)..1, ‖u (x + c i r)‖ ^ 2) + 2 * ∫ r in (0 : ℝ)..1, ‖v (x + c i r)‖ ^ 2) →
    (∀ u ∈ A (P₀ + N), ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) 1),
      ‖u (y + ∑ i, c i (t i))‖ ^ 2 ≤ B) → ∀ u ∈ A P₀, ‖u y‖ ^ 2 ≤ 4 ^ N * B := by
  induction N with
  | zero =>
    intro P₀ c A B y hc hA hF hI u hu
    have := hI u (by simpa using hu)
    rw [volume_pi, Measure.restrict_pi_pi] at this
    simpa [Measure.real] using this
  | succ N ih =>
    intro P₀ c A B y hc hA hF hI u hu
    have main := ih P₀ (fun i => c i.castSucc) A (4 * B) y (fun i => hc _) hA
      (fun p v hv => ⟨(hF p v hv).1, fun i => (hF p v hv).2 _⟩) ?_ u hu
    · calc _ ≤ _ := main
        _ = _ := by ring
    intro v hv
    obtain ⟨v', hw1, pt⟩ := (hF _ v hv).2 (Fin.last N)
    have hv1 : v ∈ A (P₀ + (N + 1)) := hA (by omega) hv
    have hΘ : Continuous fun t : Fin (N + 1) → ℝ => ∑ i, c i (t i) :=
      continuous_finsetSum _ fun i _ => (hc i).comp (continuous_apply i)
    have hΘ' : Continuous fun t : Fin N → ℝ => ∑ i, c i.castSucc (t i) :=
      continuous_finsetSum _ fun i _ => (hc _).comp (continuous_apply i)
    have hsn : ∀ (t : Fin N → ℝ) (r : ℝ),
        y + ∑ i, c i (Fin.snoc (α := fun _ => ℝ) t r i) = y + ∑ i : Fin N, c i.castSucc (t i) + c (Fin.last N) r := by
      intro t r
      rw [Fin.sum_univ_castSucc, add_assoc]
      simp
    have fub : ∀ w ∈ A (P₀ + (N + 1)),
        IntegrableOn (fun t : Fin N → ℝ => ∫ r in (0 : ℝ)..1,
          ‖w (y + ∑ i : Fin N, c i.castSucc (t i) + c (Fin.last N) r)‖ ^ 2)
          (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) 1)) ∧
        ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) 1), ∫ r in (0 : ℝ)..1,
          ‖w (y + ∑ i : Fin N, c i.castSucc (t i) + c (Fin.last N) r)‖ ^ 2 ≤ B := by
      intro w hw
      have hcw : Continuous w := (hF _ w hw).1
      have h := integral_cube_succ_last N 1 (fun t => ‖w (y + ∑ i, c i (t i))‖ ^ 2)
        ((hcw.comp (continuous_const.add hΘ)).norm.pow 2)
      simp only [hsn] at h
      simp only [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
      exact ⟨h.1, h.2 ▸ hI w hw⟩
    obtain ⟨i1, b1⟩ := fub v hv1
    obtain ⟨i2, b2⟩ := fub _ hw1
    have i0 : IntegrableOn (fun t : Fin N → ℝ => ‖v (y + ∑ i : Fin N, c i.castSucc (t i))‖ ^ 2)
        (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) 1)) :=
      (((hF _ v hv).1.comp (continuous_const.add hΘ')).norm.pow 2).continuousOn.integrableOn_compact
        (isCompact_univ_pi fun _ => isCompact_Icc)
    have key := integral_mono i0 ((i1.const_mul 2).add (i2.const_mul 2)) (fun t => pt _)
    simp only [Pi.add_apply] at key
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul] at key
    linarith

theorem lintegral_compact_le {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] [Countable Γ] (μ : Measure G)
    [μ.IsAddHaarMeasure] {𝓕 : Set G} (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) {K : Set G} (hK : IsCompact K) :
    ∃ M : ℕ, ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ γ ∈ Γ, ∀ w, φ (γ + w) = φ w) →
      ∫⁻ w in K, φ w ∂μ ≤ M * ∫⁻ w in 𝓕, φ w ∂μ := by
  classical
  have hKK : IsCompact (K - K) := by
    rw [sub_eq_add_neg]; exact hK.add hK.neg
  have hfin := tendsto_cofinite_cocompact_iff.1 (Γ.tendsto_coe_cofinite_of_discrete ⟨‹_›⟩) _ hKK
  refine ⟨hfin.toFinset.card, fun φ hφ hp => ?_⟩
  have hm : Measurable (K.indicator φ) := hφ.indicator hK.measurableSet
  rw [← lintegral_indicator hK.measurableSet, h𝓕.lintegral_eq_tsum'', ← lintegral_tsum, ← lintegral_const_mul _ hφ]
  · refine lintegral_mono fun w => ?_
    by_cases h : ∃ γ : Γ, (γ : G) + w ∈ K
    · obtain ⟨γ₀, h₀⟩ := h
      rw [tsum_eq_sum (s := hfin.toFinset.image (· + γ₀))]
      · refine (Finset.sum_le_card_nsmul _ _ (φ w) fun γ _ => ?_).trans ?_
        · exact (Set.indicator_le_self _ _ _).trans (hp γ γ.2 w).le
        · rw [nsmul_eq_mul]
          exact mul_le_mul_left (Nat.cast_le.2 Finset.card_image_le) _
      · intro γ hγ
        refine Set.indicator_of_notMem (fun hk => hγ ?_) _
        refine Finset.mem_image.2 ⟨γ - γ₀, ?_, sub_add_cancel _ _⟩
        rw [Set.Finite.mem_toFinset]
        refine ⟨_, hk, _, h₀, ?_⟩
        show (γ : G) + w - (γ₀ + w) = γ - γ₀
        abel
    · have : ∀ γ : Γ, K.indicator φ (γ +ᵥ w) = 0 := fun γ => Set.indicator_of_notMem (fun hk => h ⟨γ, hk⟩) _
      simp only [this, tsum_zero, zero_le]
  · intro γ
    exact (hm.comp (measurable_const_add (γ : G))).aemeasurable

theorem lintegral_real_le {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] {N : ℕ} (ι : (Fin N → ℝ) →+ G)
    (π : G →+ (Fin N → ℝ)) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ t, π (ι t) = t) {K₀ : Set G}
    (hK₀ : IsCompact K₀) (h0 : K₀ ∈ 𝓝 (0 : G)) {B : Set (Fin N → ℝ)} (hB : IsCompact B) :
    ∃ (c : NNReal) (K : Set G), IsCompact K ∧ ∀ φ : G → ℝ≥0∞, Measurable φ →
      (∀ w, w - ι (π w) ∈ K₀ → φ w = φ (ι (π w))) → ∫⁻ t in B, φ (ι t) ≤ c * ∫⁻ w in K, φ w ∂μ := by
  let V : Set G := {w | w - ι (π w) ∈ K₀}
  have hp : Continuous fun w => w - ι (π w) := continuous_id.sub (hι.comp hπ)
  have hV : MeasurableSet V := (hK₀.isClosed.preimage hp).measurableSet
  have hV0 : V ∈ 𝓝 (0 : G) := hp.continuousAt.preimage_mem_nhds (by simpa using h0)
  have hsub : ∀ B : Set (Fin N → ℝ), π ⁻¹' B ∩ V ⊆ K₀ + ι '' B := fun B w hw =>
    ⟨_, hw.2, _, ⟨_, hw.1, rfl⟩, sub_add_cancel _ _⟩
  let ν : Measure (Fin N → ℝ) := (μ.restrict V).map π
  have hν : ∀ A, MeasurableSet A → ν A = μ (π ⁻¹' A ∩ V) := fun A hA => by
    rw [Measure.map_apply hπ.measurable hA, Measure.restrict_apply (hπ.measurable hA)]
  have : IsFiniteMeasureOnCompacts ν := ⟨fun A hA => by
    rw [hν A hA.measurableSet]
    exact (measure_mono (hsub A)).trans_lt (hK₀.add (hA.image hι)).measure_lt_top⟩
  have : ν.IsAddLeftInvariant := (forall_measure_preimage_add_iff ν).1 fun t A hA => by
    rw [hν A hA, hν _ (measurable_const_add t hA), ← measure_preimage_add μ (ι t) (π ⁻¹' A ∩ V)]
    congr 1
    ext w
    simp only [V, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, map_add, hπι, add_sub_add_left_eq_sub]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • volume := ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := hν Set.univ MeasurableSet.univ
    rw [hc, zero_smul, Set.preimage_univ, Set.univ_inter] at h1
    exact (Measure.measure_pos_of_mem_nhds μ hV0).ne h1
  refine ⟨c⁻¹, K₀ + ι '' B, hK₀.add (hB.image hι), fun φ hφ hl => ?_⟩
  have e1 : ∫⁻ t in B, φ (ι t) ∂ν = c * ∫⁻ t in B, φ (ι t) := by
    rw [hc, Measure.restrict_smul, lintegral_smul_measure]; rfl
  have e2 : ∫⁻ t in B, φ (ι t) ∂ν ≤ ∫⁻ w in K₀ + ι '' B, φ w ∂μ := by
    rw [setLIntegral_map (f := fun t => φ (ι t)) hB.measurableSet (hφ.comp hι.measurable) hπ.measurable,
      Measure.restrict_restrict (hπ.measurable hB.measurableSet),
      ← setLIntegral_congr_fun ((hπ.measurable hB.measurableSet).inter hV) fun w hw => hl w hw.2]
    exact lintegral_mono_set (hsub B)
  rw [e1] at e2
  rw [ENNReal.coe_inv hc0]
  exact (ENNReal.mul_le_iff_le_inv (ENNReal.coe_ne_zero.2 hc0) ENNReal.coe_ne_top).1 e2

theorem words_bound {R M X : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] [AddCommGroup M]
    [Module ℝ M] (Dv : R →ₗ[ℝ] M →ₗ[ℝ] M) (ev : X → M →ₗ[ℝ] ℂ) (hb : ∀ m, ∃ C : ℝ, ∀ x, ‖ev x m‖ ≤ C) (p : ℕ) :
    ∀ m, ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 1 ≤ ρ → ∀ l : List R, l.length ≤ p → (∀ u ∈ l, ‖u‖ ≤ ρ) →
      ∀ x, ‖ev x (l.foldl (fun m u => Dv u m) m)‖ ≤ C * ρ ^ p := by
  have lin : ∀ l : List R, ∃ L : M →ₗ[ℝ] M, ∀ m, l.foldl (fun m u => Dv u m) m = L m := by
    intro l
    induction l with
    | nil => exact ⟨LinearMap.id, fun _ => rfl⟩
    | cons u l ih =>
      obtain ⟨L, hL⟩ := ih
      exact ⟨L ∘ₗ Dv u, fun m => hL _⟩
  induction p with
  | zero =>
    intro m
    obtain ⟨C, hC⟩ := hb m
    refine ⟨max C 0, le_max_right _ _, fun ρ _ l hl _ x => ?_⟩
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl), pow_zero, mul_one]
    exact (hC x).trans (le_max_left _ _)
  | succ p ih =>
    intro m
    let b := Module.finBasis ℝ R
    obtain ⟨C₀, h₀, hC₀⟩ := ih m
    choose C h1 hC using fun i => ih (Dv (b i) m)
    let κ := ‖b.equivFunL.toContinuousLinearMap‖
    have hs : 0 ≤ ∑ i, κ * C i := Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (h1 i)
    refine ⟨C₀ + ∑ i, κ * C i, add_nonneg h₀ hs, fun ρ hρ l hl hu x => ?_⟩
    have hρp : 0 ≤ ρ ^ p := by positivity
    cases l with
    | nil =>
      refine (hC₀ ρ hρ [] (Nat.zero_le _) hu x).trans ?_
      exact mul_le_mul (le_add_of_nonneg_right hs) (pow_le_pow_right₀ hρ p.le_succ) hρp (add_nonneg h₀ hs)
    | cons u l =>
      obtain ⟨L, hL⟩ := lin l
      have hl' : l.length ≤ p := by simpa using hl
      rw [List.foldl_cons, hL, ← b.sum_repr u, map_sum, LinearMap.sum_apply, map_sum, map_sum]
      refine (norm_sum_le _ _).trans (le_trans ?_ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left h₀) (by positivity)))
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [map_smul, LinearMap.smul_apply, map_smul, map_smul, norm_smul, ← hL]
      have a1 := hC i ρ hρ l hl' (fun v hv => hu v (List.mem_cons_of_mem _ hv)) x
      have a2 : ‖b.repr u i‖ ≤ κ * ρ :=
        (norm_le_pi_norm (b.equivFunL.toContinuousLinearMap u) i).trans ((b.equivFunL.toContinuousLinearMap.le_opNorm u).trans
          (mul_le_mul_of_nonneg_left (hu u List.mem_cons_self) (norm_nonneg _)))
      calc _ ≤ (κ * ρ) * (C i * ρ ^ p) := mul_le_mul a2 a1 (norm_nonneg _) ((norm_nonneg _).trans a2)
        _ = _ := by ring

theorem one_le_sum_norm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (h : A * B = 1) (i : Fin n) :
    1 ≤ ∑ a, ∑ b, (‖A a b‖ + ‖B a b‖) := by
  set S := ∑ a, ∑ b, (‖A a b‖ + ‖B a b‖) with hS
  have hS0 : 0 ≤ S := by positivity
  have hle : ∀ a b, ‖A a b‖ + ‖B a b‖ ≤ S := fun a b =>
    (Finset.single_le_sum (f := fun b => ‖A a b‖ + ‖B a b‖) (fun _ _ => by positivity) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, (‖A a b‖ + ‖B a b‖)) (fun _ _ => by positivity) (Finset.mem_univ a))
  have hrow : ∑ b, ‖A i b‖ ≤ S :=
    (Finset.sum_le_sum fun b _ => le_add_of_nonneg_right (norm_nonneg (B i b))).trans
      (Finset.single_le_sum (f := fun a => ∑ b, (‖A a b‖ + ‖B a b‖)) (fun _ _ => by positivity) (Finset.mem_univ i))
  have h1 : (1 : ℝ) ≤ S * S := by
    have e : (1 : ℂ) = ∑ b, A i b * B b i := by rw [← Matrix.mul_apply, h, Matrix.one_apply_eq]
    calc (1 : ℝ) = ‖∑ b, A i b * B b i‖ := by rw [← e, norm_one]
      _ ≤ ∑ b, ‖A i b‖ * S := (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left (norm_nonneg (A b i))).trans (hle b i))
            (norm_nonneg _))
      _ ≤ S * S := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hrow hS0
  nlinarith

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℝ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  add_mem' := theta_add
  zero_mem' := theta_zero
  smul_mem' c _ hf := theta_smul (c : ℂ) hf

def dv (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D) (S T : HSp D) (u : RW T S) (f : WO S T → ℂ) :
    WO S T → ℂ := hD (iotaW σ T S) (piW θ T S) (omO S T) u f

theorem exists_line (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (u : RW T S) : ∃ L : ℝ →+ WO S T, IsRealDir T S L ∧
    (∀ t, L t = iotaW σ T S (t • u)) ∧ ∀ f, dv θ σ S T u f = dLine ψ S T L f := by
  obtain ⟨L, hL, e⟩ := (smooth_iff_sm_and_real_lines D θ σ h T S).2.2 u
  refine ⟨L, hL, e, fun f => ?_⟩
  rw [dLine_eq_hD h hψ hL, e, one_smul, h.pi_iota]
  rfl

theorem theta_dv (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (u : RW T S) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (dv θ σ S T u f) := by
  obtain ⟨L, hL, -, e⟩ := exists_line h hψ u
  rw [e]
  exact theta_dLine h.inf hψ hL hf

theorem dv_apply (h : Chart θ σ) (u : RW T S) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    dv θ σ S T u f w = -(Real.pi * Complex.I) * (omO S T (piW θ T S w) u : ℝ) * f w +
      fderiv ℝ (fun x : RW T S => f (w + iotaW σ T S x)) 0 u :=
  hD_eq_fderiv _ _ _ f (theta_sm h hf) u w

def dvL (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) :
    RW T S →ₗ[ℝ] thetaSub ψ S T →ₗ[ℝ] thetaSub ψ S T :=
  LinearMap.mk₂ ℝ (fun u f => ⟨dv θ σ S T u f.1, theta_dv h hψ u f.2⟩)
    (fun u v f => Subtype.ext (funext fun w => by
      show dv θ σ S T (u + v) f.1 w = dv θ σ S T u f.1 w + dv θ σ S T v f.1 w
      rw [dv_apply h _ f.2, dv_apply h _ f.2, dv_apply h _ f.2, map_add, map_add]
      push_cast
      ring))
    (fun c u f => Subtype.ext (funext fun w => by
      show dv θ σ S T (c • u) f.1 w = c • dv θ σ S T u f.1 w
      rw [dv_apply h _ f.2, dv_apply h _ f.2, map_smul, map_smul, Complex.real_smul, Complex.real_smul, smul_eq_mul]
      push_cast
      ring))
    (fun u f g => Subtype.ext (funext fun w => by
      show dv θ σ S T u (f + g).1 w = dv θ σ S T u f.1 w + dv θ σ S T u g.1 w
      have e := fderiv_add (((theta_sm h f.2 w).differentiable (by simp)) 0) (((theta_sm h g.2 w).differentiable (by simp)) 0)
      rw [dv_apply h _ (f + g).2, dv_apply h _ f.2, dv_apply h _ g.2]
      erw [e]
      rw [ContinuousLinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
      ring))
    (fun c u f => Subtype.ext (funext fun w => by
      show dv θ σ S T u (c • f).1 w = c • dv θ σ S T u f.1 w
      have e := fderiv_const_smul (((theta_sm h f.2 w).differentiable (by simp)) 0) c
      rw [dv_apply h _ (c • f).2, dv_apply h _ f.2]
      erw [e]
      rw [ContinuousLinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, Complex.real_smul, Complex.real_smul,
        Complex.real_smul]
      ring))

theorem dv_level (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (z : RW T S) {f : WO S T → ℂ} {u : WO S T}
    (h0 : u.map (infPart D) = 0) (hu : heisO ψ S T u f = f) :
    heisO ψ S T u (dv θ σ S T z f) = dv θ σ S T z f := by
  obtain ⟨L, hL, -, e⟩ := exists_line h hψ z
  rw [e]
  funext w
  have : (fun t => heisO ψ S T (L t) f w) = fun t => heisO ψ S T u (heisO ψ S T (L t) f) w := by
    funext t; rw [heisO_comm_fin_real h0 (hL.2 t) hu]
  conv_rhs => unfold dLine; rw [this]
  unfold dLine
  rw [heisO, ← deriv_const_mul_field]
  rfl

theorem sobolev_step (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (z : RW T S) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (x : WO S T) :
    ‖f x‖ ^ 2 ≤ 2 * (∫ r in (0 : ℝ)..1, ‖f (x + iotaW σ T S (r • z))‖ ^ 2) +
      2 * ∫ r in (0 : ℝ)..1, ‖dv θ σ S T z f (x + iotaW σ T S (r • z))‖ ^ 2 := by
  obtain ⟨L, hL, e, e'⟩ := exists_line h hψ z
  have := sobolev_endpoint_one_variable ℂ _ _ 1 one_pos (fun t _ => hasDerivAt_heisO h.inf hψ hL hf x t)
    (fun t _ => (hasDerivAt_heisO h.inf hψ hL (theta_dLine h.inf hψ hL hf) x t).continuousAt.continuousWithinAt)
  rw [L.map_zero, heisO_zero] at this
  simpa only [GlobalTheory.HeisOrtho.norm_heisO hψ.1, e, e', div_one, mul_one] using this

theorem actO_mul (g g' : GA D S) (h h' : GA D T) (u : WO S T) :
    actO S T g h (actO S T g' h' u) = actO S T (g * g') (h * h') u := by
  unfold actO
  simp only [mul_inv_rev, GlobalTheory.WeilVacMove.mt_mul, Matrix.mul_assoc]

theorem actO_one (u : WO S T) : actO S T 1 1 u = u := by
  unfold actO
  simp only [inv_one, GlobalTheory.WeilVacMove.mt_one, Matrix.one_mul, Matrix.mul_one]

def mov (θ : InfFam D) (g : GA D S) (h : GA D T) (u : RW T S) : RW T S := fun τ =>
  (compAt θ τ (Formalism.L2.Theta.mt T h) * Matrix.of (u τ) * compAt θ τ (Formalism.L2.Theta.mt S g⁻¹) :
    Matrix (Fin T.rank) (Fin S.rank) ℂ)

theorem actO_iota (hc : Chart θ σ) (g : GA D S) (h : GA D T) (t : ℝ) (u : RW T S) :
    iotaW σ T S (t • mov θ g h u) = actO S T g h (iotaW σ T S (t • u)) := by
  refine hc.real_ext (V := T) (W := S) (hc.real_iota T S _) ?_ ?_
  · show (actO S T g h (iotaW σ T S (t • u))).map (finPart D) = 0
    have : (iotaW σ T S (t • u)).map (finPart D) = 0 := hc.real_iota T S _
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, this, Matrix.mul_zero, Matrix.zero_mul]
  · funext τ
    have e : compAt θ τ (iotaW σ T S (t • u)) = t • Matrix.of (u τ) := congrFun (hc.pi_iota T S (t • u)) τ
    rw [hc.pi_iota]
    show _ = compAt θ τ (actO S T g h (iotaW σ T S (t • u)))
    rw [GlobalTheory.WeilVacMove.compAt_actO, e, Matrix.mul_smul, Matrix.smul_mul]
    rfl

theorem mov_mov_inv (hc : Chart θ σ) (g : GA D S) (h : GA D T) (u : RW T S) : mov θ g h (mov θ g⁻¹ h⁻¹ u) = u := by
  have e := actO_iota hc g h 1 (mov θ g⁻¹ h⁻¹ u)
  rw [actO_iota hc g⁻¹, actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one, one_smul, one_smul] at e
  rw [← hc.pi_iota T S (mov θ g h _), e, hc.pi_iota]

variable {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem dv_om (hom : IsWeilDatumO ψ S T χS χT om) (hc : Chart θ σ) (g : GA D S) (h : GA D T) (u : RW T S)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    dv θ σ S T u (om (g, h) f) = om (g, h) (dv θ σ S T (mov θ g⁻¹ h⁻¹ u) f) := by
  obtain ⟨L, hL, e, e'⟩ := exists_line hc hom.std (mov θ g⁻¹ h⁻¹ u)
  obtain ⟨L', hL', d, d'⟩ := exists_line hc hom.std u
  rw [e', d', om_dLine hom hc.inf g h hL hL' (fun t => by rw [e, d, ← actO_iota hc, mov_mov_inv hc]) hf]

theorem norm_mov_le (g : GA D S) (x y : GA D T) (u : RW T S) :
    ‖mov θ g (x * y)⁻¹ u‖ ≤ ‖mov θ g x⁻¹ u‖ * normInf θ T y := by
  have h0 : 0 ≤ normInf θ T y := by unfold normInf; positivity
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun τ => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have e : mov θ g (x * y)⁻¹ u τ i j = ∑ k, compAt θ τ (Formalism.L2.Theta.mt T y⁻¹) i k * mov θ g x⁻¹ u τ k j := by
    unfold mov
    rw [mul_inv_rev, GlobalTheory.WeilVacMove.mt_mul, GlobalTheory.WeilVacMove.compAt_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_apply, Matrix.mul_assoc]
  have h1 : ∑ k, ‖compAt θ τ (Formalism.L2.Theta.mt T y⁻¹) i k‖ ≤ normInf θ T y :=
    (Finset.sum_le_sum fun k _ => le_add_of_nonneg_left (norm_nonneg (infMat D.sp.cm.sig T.gram (θ τ) y i k))).trans
      ((Finset.single_le_sum (f := fun i => ∑ j, (‖infMat D.sp.cm.sig T.gram (θ τ) y i j‖ +
        ‖infMat D.sp.cm.sig T.gram (θ τ) y⁻¹ i j‖)) (fun _ _ => by positivity) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, (‖infMat D.sp.cm.sig T.gram (θ τ) y i j‖ +
        ‖infMat D.sp.cm.sig T.gram (θ τ) y⁻¹ i j‖)) (fun _ _ => by positivity) (Finset.mem_univ τ)))
  rw [e]
  refine (norm_sum_le _ _).trans (le_trans ?_ (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ k).trans (norm_le_pi_norm _ τ)))
    (norm_nonneg _)

theorem continuous_mov (hθ : IsInfFam θ) (x : GA D T) (u : RW T S) : Continuous fun g : GA D S => mov θ g⁻¹ x u := by
  refine continuous_pi fun τ => ?_
  unfold mov
  simp only [inv_inv]
  exact continuous_const.matrix_mul ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp (GlobalTheory.RealWeil.continuous_mt S).1)

theorem one_le_normInf (h : Module.finrank ℝ (RW T S) ≠ 0) (g : GA D T) : 1 ≤ normInf θ T g := by
  have := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero h)
  obtain ⟨u, hu⟩ := exists_ne (0 : RW T S)
  obtain ⟨τ, hτ⟩ := Function.ne_iff.1 hu
  obtain ⟨i, -⟩ := Function.ne_iff.1 hτ
  exact (one_le_sum_norm _ _ (GlobalTheory.WeilVacMove.compAt_mt_mul_inv θ τ T g) i).trans
    (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, (‖infMat D.sp.cm.sig T.gram (θ τ) g i j‖ +
      ‖infMat D.sp.cm.sig T.gram (θ τ) g⁻¹ i j‖)) (fun _ _ => by positivity) (Finset.mem_univ τ))

theorem uniform_level (hom : IsWeilDatumO ψ S T χS χT om) (hc : Chart θ σ) {U : AddSubgroup (WO S T)}
    (hU : IsOpen (U : Set (WO S T))) (x : GA D T) {C : Set (GA D S)} (hC : IsCompact C) :
    ∃ K₀ ∈ 𝓝 (0 : WO S T), IsCompact K₀ ∧ ∀ h ∈ C, ∀ g ∈ GinfC T, ∀ φ, IsThetaFunO ψ S T φ →
      (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u φ = φ) → ∀ w, w - iotaW σ T S (piW θ T S w) ∈ K₀ →
        ‖om (h, x * g) φ w‖ = ‖om (h, x * g) φ (iotaW σ T S (piW θ T S w))‖ := by
  obtain ⟨i1, i2, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have hcont : Continuous fun z : WO S T × GA D S => actO S T z.2⁻¹ x⁻¹ z.1 := by
    unfold actO
    simp only [inv_inv]
    exact (continuous_const.matrix_mul continuous_fst).matrix_mul
      ((GlobalTheory.RealWeil.continuous_mt S).1.comp continuous_snd)
  have hev : ∀ᶠ u in 𝓝 (0 : WO S T), ∀ h ∈ C, actO S T h⁻¹ x⁻¹ u ∈ U := by
    refine hC.eventually_forall_of_forall_eventually fun h _ => ?_
    refine hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds ?_)
    show actO S T h⁻¹ x⁻¹ 0 ∈ U
    unfold actO
    rw [Matrix.mul_zero, Matrix.zero_mul]
    exact U.zero_mem
  obtain ⟨K₀, h0, hsub, hK₀⟩ := LocallyCompactSpace.local_compact_nhds (X := WA T S) 0 _ hev
  refine ⟨K₀, h0, hK₀, fun h hh g hg φ hφ hl w hw => ?_⟩
  generalize hu : w - iotaW σ T S (piW θ T S w) = u at hw
  have hinf : u.map (infPart D) = 0 := by
    have hp : piW θ T S u = 0 := by
      rw [← hu, AddMonoidHom.map_sub, hc.pi_iota, sub_self]
    ext i j
    exact ThetaCont.infPart_eq_zero hc _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
  have hv : (actO S T h⁻¹ x⁻¹ u).map (infPart D) = 0 := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hinf, Matrix.mul_zero, Matrix.zero_mul]
  have e := hom.om_heis h (x * g) (actO S T h⁻¹ x⁻¹ u) φ hφ
  have e1 : actO S T h (x * g) (actO S T h⁻¹ x⁻¹ u) = u := by
    conv_lhs => rw [← mul_one h, ← actO_mul, GlobalTheory.RealWeil.actO_fin hc (one_mem _) hg (by rw [mul_one]; exact hv)]
    rw [actO_mul, mul_one, mul_inv_cancel, mul_inv_cancel, actO_one]
  rw [hl _ (hsub hw h hh) hv, e1] at e
  conv_rhs => rw [e, GlobalTheory.HeisOrtho.norm_heisO hom.std.1, ← hu, add_sub_cancel]

theorem words_level (hc : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {u : WO S T} (h0 : u.map (infPart D) = 0)
    (l : List (RW T S)) : ∀ m : thetaSub ψ S T, heisO ψ S T u m.1 = m.1 →
      heisO ψ S T u (l.foldl (fun m z => dvL hc hψ S T z m) m).1 = (l.foldl (fun m z => dvL hc hψ S T z m) m).1 := by
  induction l with
  | nil => exact fun _ h => h
  | cons z l ih => exact fun m h => ih _ (dv_level hc hψ z h0 h)

theorem cube_bound (hom : IsWeilDatumO ψ S T χS χT om) (hc : Chart θ σ) {N : ℕ} (b : Module.Basis (Fin N) ℝ (RW T S))
    {K₀ : Set (WO S T)} (h0 : K₀ ∈ 𝓝 (0 : WO S T)) (hK₀ : IsCompact K₀) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ p φ, IsThetaFunO ψ S T φ → (∀ w, w - iotaW σ T S (piW θ T S w) ∈ K₀ →
        ‖om p φ w‖ = ‖om p φ (iotaW σ T S (piW θ T S w))‖) → ∀ B : ℝ, (∀ w, ‖φ w‖ ≤ B) →
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) 1),
        ‖om p φ (0 + ∑ i, iotaW σ T S (t i • b i))‖ ^ 2 ≤ c * B ^ 2 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WA T S) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, h1⟩, -⟩ := GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WA T S) (ratL T S) K hK hcov
  have : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let ι : (Fin N → ℝ) →+ WA T S := (iotaW σ T S).comp b.equivFun.symm.toLinearMap.toAddMonoidHom
  let π : WA T S →+ (Fin N → ℝ) := b.equivFun.toLinearMap.toAddMonoidHom.comp (piW θ T S)
  have hι : Continuous ι := (hc.continuous_iota T S).comp b.equivFunL.symm.continuous
  have hπ : Continuous π := b.equivFunL.continuous.comp (continuous_pi' hc.inf T S)
  have hπι : ∀ t, π (ι t) = t := fun t => by
    show b.equivFun (piW θ T S (iotaW σ T S (b.equivFun.symm t))) = t
    rw [hc.pi_iota, LinearEquiv.apply_symm_apply]
  have hιπ : ∀ w, ι (π w) = iotaW σ T S (piW θ T S w) := fun w => by
    show iotaW σ T S (b.equivFun.symm (b.equivFun (piW θ T S w))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hsum : ∀ t : Fin N → ℝ, 0 + ∑ i, iotaW σ T S (t i • b i) = ι t := fun t => by
    show _ = iotaW σ T S (b.equivFun.symm t)
    rw [zero_add, Module.Basis.equivFun_symm_apply, map_sum]
  obtain ⟨c, K₁, hK₁, hreal⟩ := lintegral_real_le (G := WA T S) μ ι π hι hπ hπι hK₀ h0
    (isCompact_univ_pi fun _ : Fin N => isCompact_Icc (a := (0 : ℝ)) (b := 1))
  obtain ⟨M, hM⟩ := lintegral_compact_le (G := WA T S) (ratL T S) μ h𝓕 hK₁
  refine ⟨c * M, by positivity, fun p φ hφ hl B hB => ?_⟩
  have hF := hom.om_pres p φ hφ
  have en : ∀ z : ℂ, ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hm : Measurable fun w : WA T S => ‖om p φ w‖ₑ ^ 2 := hF.cont.measurable.enorm.pow_const 2
  have a1 := hreal _ hm fun w hw => by
    rw [hιπ] at hw ⊢
    rw [← en, ← en, hl w hw]
  have a2 := hM _ hm fun γ hγ w => by rw [← en, ← en, theta_norm_periodic hom.std hF γ hγ w]
  have a3 := hom.om_unit μ 𝓕 hμ h𝓕 p φ hφ
  have a4 : ∫⁻ w in 𝓕, ‖φ w‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (B ^ 2) := by
    refine (lintegral_mono (g := fun _ => ENNReal.ofReal (B ^ 2)) fun w => ?_).trans ?_
    · show ‖φ w‖ₑ ^ 2 ≤ _
      rw [← en]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hB w) 2)
    · rw [setLIntegral_const, h1, mul_one]
  simp only [hsum]
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun t => ‖om p φ (ι t)‖ ^ 2)
    (Filter.Eventually.of_forall fun w => by positivity) ((hF.cont.comp hι).norm.pow 2).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  simp only [en]
  refine a1.trans ?_
  rw [mul_assoc, ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_mul M.cast_nonneg, ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_natCast]
  exact mul_le_mul_right (a2.trans (mul_le_mul_right (a3.le.trans a4) _)) _

theorem thetaKO_growth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ →
    ∃ N : ℕ, ∀ f, IsThetaFunO ψ S T f → ∀ (x : GA D T) (C : Set (GA D S)), IsCompact C →
      ∃ c : ℝ, ∀ h ∈ C, ∀ g ∈ GinfC T, ‖thetaKO om h (x * g) f‖ ≤ c * normInf θ T g ^ N := by
  intro D ψ S T χS χT om hom θ hθ
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hψ := hom.std
  refine ⟨Module.finrank ℝ (RW T S), fun f hf x C hC => ?_⟩
  have hone := one_le_normInf (θ := θ) (S := S) (T := T)
  have b := Module.finBasis ℝ (RW T S)
  generalize Module.finrank ℝ (RW T S) = N at hone b ⊢
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨K₀, h0, hK₀, hlev⟩ := uniform_level hom hc hU x hC
  obtain ⟨c, hc0, hcube⟩ := cube_bound hom hc b h0 hK₀
  obtain ⟨C₁, hC₁0, hC₁⟩ := words_bound (dvL hc hψ S T) (fun w => (LinearMap.proj w).comp (thetaSub ψ S T).subtype)
    (fun m => theta_bounded hψ m.2) N ⟨f, hf⟩
  obtain ⟨κ, hκ⟩ := hC.exists_bound_of_continuousOn
    (continuous_pi fun i => continuous_mov hθ x⁻¹ (b i)).continuousOn
  refine ⟨√(4 ^ N * c) * C₁ * max 1 κ ^ N, fun h hh g hg => ?_⟩
  have hn0 : 0 ≤ normInf θ T g := by unfold normInf; positivity
  obtain ⟨ρ, hρ1, hρ2, hρ3⟩ : ∃ ρ : ℝ, 1 ≤ ρ ∧ κ * normInf θ T g ≤ ρ ∧ ρ ^ N ≤ max 1 κ ^ N * normInf θ T g ^ N := by
    refine ⟨max 1 (κ * normInf θ T g), le_max_left _ _, le_max_right _ _, ?_⟩
    rcases eq_or_ne N 0 with rfl | hN
    · simp
    · rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (hone hN g))
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hn0)) _
  let wd : List (RW T S) → thetaSub ψ S T := fun l => l.foldl (fun m z => dvL hc hψ S T z m) ⟨f, hf⟩
  let A : ℕ → Set (WO S T → ℂ) := fun p =>
    {F | ∃ l : List (RW T S), l.length ≤ p ∧ (∀ u ∈ l, ‖u‖ ≤ ρ) ∧ F = om (h, x * g) (wd l).1}
  have key := sobolev_iter N 0 (fun i r => iotaW σ T S (r • b i)) A (c * (C₁ * ρ ^ N) ^ 2) 0
    (fun i => (hc.continuous_iota T S).comp (continuous_id.smul continuous_const))
    (fun p q hpq F ⟨l, h1, h2⟩ => ⟨l, h1.trans hpq, h2⟩) ?_ ?_ (om (h, x * g) f) ⟨[], le_rfl, by simp, rfl⟩
  · have e : 4 ^ N * (c * (C₁ * ρ ^ N) ^ 2) = (√(4 ^ N * c) * C₁ * ρ ^ N) ^ 2 := by
      rw [mul_assoc, mul_pow (√_), Real.sq_sqrt (by positivity), mul_assoc]
    rw [e] at key
    refine ((pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 key).trans ?_
    rw [mul_assoc _ (_ ^ N)]
    exact mul_le_mul_of_nonneg_left hρ3 (by positivity)
  · rintro p _ ⟨l, h1, h2, rfl⟩
    have hF := hom.om_pres (h, x * g) _ (wd l).2
    refine ⟨hF.cont, fun i => ⟨_, ⟨l ++ [mov θ h⁻¹ (x * g)⁻¹ (b i)], by simpa using h1, fun u hu => ?_, ?_⟩,
      sobolev_step hc hψ (b i) hF⟩⟩
    · rcases List.mem_append.1 hu with hu | hu
      · exact h2 u hu
      · rw [List.mem_singleton.1 hu]
        exact (norm_mov_le _ _ _ _).trans ((mul_le_mul_of_nonneg_right
          ((norm_le_pi_norm (fun i => mov θ h⁻¹ x⁻¹ (b i)) i).trans (hκ h hh)) hn0).trans hρ2)
    · rw [dv_om hom hc h (x * g) (b i) (wd l).2]
      simp only [wd, List.foldl_append]
      rfl
  · rintro _ ⟨l, h1, h2, rfl⟩
    exact hcube _ _ (wd l).2 (hlev h hh g hg _ (wd l).2 fun u hu h0 => words_level hc hψ h0 l _ (hl u hu h0)) _
      (hC₁ ρ hρ1 l (by simpa using h1) h2)

end GlobalTheory.ThetaGrowth

end
