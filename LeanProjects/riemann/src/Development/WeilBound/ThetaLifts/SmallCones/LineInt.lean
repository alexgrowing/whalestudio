import Development.WeilBound.ThetaLifts.SmallCones.NormPiInfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSum

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField.mixedEmbedding
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.HeisSchA PositivityTheory.ThKCT.Ad PositivityTheory.ThKEst
open GlobalTheory.Doubling (absE)

namespace Line

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def soSub (B : Base F E) (M : Model σ X W) : Submodule ℂ ((Fin n × Fin d → Af F) → ℂ) where
  carrier := soFin B M
  zero_mem' := ⟨zero_mem _, fun f => by rw [GlobalTheory.ThK.Dbl.Dense.pureA_zero]; exact zero_mem _⟩
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, fun f => by rw [GlobalTheory.ThK.Dbl.Dense.pureA_add]; exact add_mem (ha.2 f) (hb.2 f)⟩
  smul_mem' c a ha := ⟨Submodule.smul_mem _ _ ha.1, fun f => by
    rw [GlobalTheory.ThK.Dbl.Dense.pureA_smul]; exact Submodule.smul_mem _ _ (ha.2 f)⟩

theorem contract {B : Base F E} {M : Model σ X W} (hM : M.IsGood B.ψ) {Φ : Fn F n d} (hΦ : Φ ∈ M.So B.ψ B.τ₁)
    (x : Fin n × Fin d → mixedSpace F) : (fun y : Fin n × Fin d → Af F => Φ fun i => pt (x i) (y i)) ∈ soSub B M := by
  induction hΦ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨f, φ, h1, h2, h3, rfl⟩ := h
    have : GlobalTheory.ThK.Dbl.Dense.pf φ ∈ soSub B M := ⟨GlobalTheory.ThK.Dbl.Dense.pf_mem ⟨h1, by
      filter_upwards [h2, hM.std] with v a b using a.trans b⟩, fun f' => Submodule.subset_span ⟨f', φ, h1, h2, h3, rfl⟩⟩
    convert Submodule.smul_mem _ (f x) this using 1
    exact funext fun y => pureA_pt f (GlobalTheory.ThK.Dbl.Dense.pf φ) x y
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

theorem exists_so {B : Base F E} {M : Model σ X W} (hM : M.IsGood B.ψ) {ι : Type} [Fintype ι]
    (φ : ι → (Fin n × Fin d → Af F) → ℂ) : ∃ φ' : ι → (Fin n × Fin d → Af F) → ℂ, (∀ i, φ' i ∈ soFin B M) ∧
      ∀ g : ι → SInf F (Fin n × Fin d), ∑ i, pureA F (g i) (φ i) ∈ M.So B.ψ B.τ₁ →
        ∑ i, pureA F (g i) (φ i) = ∑ i, pureA F (g i) (φ' i) := by
  obtain ⟨q, hq⟩ := (soSub B M).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  refine ⟨fun i => q (φ i), fun i => (q (φ i)).2, fun g hg => funext fun w => ?_⟩
  let x : Fin n × Fin d → mixedSpace F := fun i => evI F (w i)
  have h1 : ∑ i, g i x • φ i ∈ soSub B M := by
    convert contract hM hg x using 1
    funext y
    simp only [Finset.sum_apply, pureA_pt, Pi.smul_apply, smul_eq_mul]
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hq ⟨_, h1⟩)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_sum, map_smul, LinearMap.id_apply, Submodule.coe_sum,
    Submodule.coe_smul] at h2
  have h3 := congrFun h2 fun i => (w i).2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3 ⊢
  exact h3.symm

theorem dom_int {M : Model σ X W} {om : Rep σ X W} (hom : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F _)
    {𝓕 : Set ((Fin n × Fin d → Af F) → ℂ)} (hD : Dom M om 𝓕) {ι : Type} [Fintype ι] {φ : ι → (Fin n × Fin d → Af F) → ℂ}
    (h1 : ∀ i, φ i ∈ SB _) (h2 : ∀ i, φ i ∈ 𝓕) {α : Type} [MeasurableSpace α] (μ : Measure α) (g : ι → α → SInf F (Fin n × Fin d))
    (t : α → ℝ) (ht0 : ∀ l, 0 ≤ t l)
    (hg : ∀ q : Seminorm ℂ (SInf F (Fin n × Fin d)), Continuous q → ∀ i, Integrable (fun l => q (g i l) * t l) μ) (h : UA σ W.J) :
    ∫⁻ l, (∫⁻ x in M.dom, ‖theta om (∑ i, pureA F (g i l) (φ i)) x h‖ₑ ∂M.μ) * ENNReal.ofReal (t l) ∂μ < ⊤ := by
  choose p k G hp hG hG' hb using fun i => hD _ (h2 i)
  obtain ⟨l₀, -, hl₀⟩ := exists_adm_eq_thetaSum_of_locallyCompact F (Fin n × Fin d)
  refine lt_of_le_of_lt (lintegral_mono (g := fun l => ∑ i, ENNReal.ofReal (p i (g i l) * t l) *
    (ENNReal.ofReal ((ht h : ℝ) ^ k i) * ∫⁻ x in M.dom, G i x ∂M.μ)) fun l => ?_) ?_
  · refine (mul_le_mul_left (lintegral_mono (g := fun x => ∑ i, ENNReal.ofReal (p i (g i l) * (ht h : ℝ) ^ k i) * G i x)
      fun x => ?_) _).trans (le_of_eq ?_)
    · refine le_trans (le_of_eq ?_) ((enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hb i (g i l) x h))
      rw [theta, ← hl₀ _ (hom _ _ (Submodule.sum_mem _ fun i _ => pureA_mem _ (h1 i))), map_sum, map_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => hl₀ _ (hom _ _ (pureA_mem _ (h1 i)))
    · rw [lintegral_finsetSum _ fun i _ => (hG i).const_mul _, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [lintegral_const_mul _ (hG i), ENNReal.ofReal_mul (apply_nonneg _ _), ENNReal.ofReal_mul (apply_nonneg _ _)]
      ring
  · rw [lintegral_finsetSum' _ fun i _ => (hg _ (hp i) i).aemeasurable.ennreal_ofReal.mul_const _]
    refine ENNReal.sum_lt_top.2 fun i _ => ?_
    have hc := ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := (ht h : ℝ) ^ k i)) (hG' i)
    rw [lintegral_mul_const' _ _ hc.ne]
    exact ENNReal.mul_lt_top (hg _ (hp i) i).lintegral_lt_top hc

end Line

open Line

theorem lineInt_of (hS : Slice) (hI : SchInt) (hT : TateAbs) : LineInt := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he v₀ z₀ hz₀ hu τ hτ μ hμ z ν hz hν Ψ hΨ
  obtain ⟨κ, _, φ, g, h1, h2, h3, h4⟩ := nice hS hT hB hM hM₁ he hz₀ hu τ
    (by rcases hτ with rfl | rfl; exacts [fun _ => rfl, cA_cA hB.cm]) μ hμ hz hΨ
  beta_reduce at h3
  refine ⟨fun om₁ hom hD h₁ => ?_, ?_⟩
  · rcases hD with hD | ⟨hD, hso⟩
    · simp only [h3]
      exact dom_int hom hD h1 h1 μ (fun i l => g i l) _ (fun l => by positivity) h4 h₁
    · obtain ⟨φ', hφ', h5⟩ := exists_so hM₁ φ
      have h6 : ∀ a, e (M.co.rho B.ψ (τ a • incM F v₀) Ψ) = ∑ i, pureA F (g i a) (φ' i) := fun a => by
        rw [h3, h5 _ (h3 a ▸ hso _)]
      simp only [h6]
      exact dom_int hom hD (fun i => (hφ' i).1) hφ' μ (fun i l => g i l) _ (fun l => by positivity) h4 h₁
  obtain ⟨-, -, _, -, -, _, -⟩ := ideleTop F E
  let c : (AE F E)ˣ → ℂ := fun l => (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z
  have hc : Continuous c := (continuous_subtype_val.comp hν).mul
    ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow z)
  choose f hf using fun i => hI _ _ μ (fun l : (AE F E)ˣ => c l • g i l) (hc.smul ((h2 i).comp Units.continuous_val)) fun k j =>
    (h4 _ ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (k, j)) i).congr (.of_forall fun l => by
      simp only [map_smul_eq_mul, c, norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, NNReal.norm_eq]
      exact mul_comm _ _)
  refine ⟨∑ i, pureA F (f i) (φ i), Submodule.sum_mem _ fun i _ => pureA_mem _ (h1 i), fun l₁ hl₁ => ?_⟩
  choose T hT using fun i => hl₁ _ (h1 i)
  have e1 : (fun l : (AE F E)ˣ => l₁ (e (M.co.rho B.ψ (τ l.1 • incM F v₀) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) =
      fun l => ∑ i, T i (c l • g i l) := funext fun l => by
    rw [h3, map_sum, mul_assoc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hT, map_smul, smul_eq_mul, mul_comm]
  rw [e1]
  refine ⟨integrable_finsetSum _ fun i _ => (hf i (T i)).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => (hf i (T i)).1, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hT, (hf i (T i)).2]

end PositivityTheory.ThKCT

end
