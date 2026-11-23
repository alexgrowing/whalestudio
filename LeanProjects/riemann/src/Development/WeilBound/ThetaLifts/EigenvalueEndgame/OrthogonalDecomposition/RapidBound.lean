import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.HodgeTateFromSandwich
import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames

noncomputable section

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

open PositivityTheory.ThKEst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

section Gen

variable {G H : Type} [TopologicalSpace G] [TopologicalSpace H] [SecondCountableTopology G] [MeasurableSpace H] [BorelSpace H]
  {ν : Measure H} [IsFiniteMeasure ν] {k : G × H → ℂ}

theorem gen_cont [LocallyCompactSpace G] (hk : Continuous k)
    (hb : ∀ Ω, IsCompact Ω → ∃ K : ℝ, ∀ g ∈ Ω, ∀ h, ‖k (g, h)‖ ≤ K) : Continuous fun g => ∫ h, k (g, h) ∂ν :=
  continuous_iff_continuousAt.2 fun g₀ => by
    obtain ⟨Ω, hΩ, hg⟩ := exists_compact_mem_nhds g₀
    obtain ⟨K, hK⟩ := hb Ω hΩ
    exact continuousAt_of_dominated (bound := fun _ => K)
      (.of_forall fun g => (hk.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (by filter_upwards [hg] with g hg using .of_forall (hK g hg)) (integrable_const _)
      (.of_forall fun h => (hk.comp (continuous_id.prodMk continuous_const)).continuousAt)

theorem gen_perp [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsFiniteMeasure μ] (hk : Continuous k) {f : H → ℂ}
    (hf : Continuous f) (hi : ∀ h, Integrable (fun g => k (g, h)) μ) {K : ℝ} (hK : ∀ h, ‖f h‖ * ∫ g, ‖k (g, h)‖ ∂μ ≤ K)
    (z : ∀ g, ∫ h, f h * star (k (g, h)) ∂ν = 0) : ∫ h, (∫ g, k (g, h) ∂μ) * starRingEnd ℂ (f h) ∂ν = 0 := by
  have m : AEStronglyMeasurable (fun x : G × H => f x.2 * star (k x)) (μ.prod ν) :=
    ((hf.comp continuous_snd).mul hk.star).aestronglyMeasurable
  have i : Integrable (fun x : G × H => f x.2 * star (k x)) (μ.prod ν) := by
    refine (integrable_prod_iff' m).2 ⟨.of_forall fun h => (Integrable.mono (hi h) (hi h).1.star (.of_forall fun _ => (norm_star _).le)).const_mul (f h),
      .of_bound m.norm.prod_swap.integral_prod_right' K (.of_forall fun h => ?_)⟩
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simpa only [norm_mul, norm_star, integral_const_mul] using hK h
  have e := integral_integral_swap (f := fun g h => f h * star (k (g, h))) i
  simp only [z, integral_zero, integral_const_mul] at e
  have := congrArg (starRingEnd ℂ) e.symm
  rw [map_zero, ← integral_conj] at this
  rw [← this]
  refine integral_congr_ae (.of_forall fun h => ?_)
  simp only [map_mul, ← integral_conj]
  simp [mul_comm]

end Gen

theorem rapid_bound {φ : UA σ W.J → ℂ} (hφ : IsRapid (Y := W) φ) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : UA σ W.J → ℝ) (A : ℝ), (∀ γ ∈ ratU σ W.J, ∀ h, T (γ * h) = T h) →
      (∀ h, T h ≤ A * (ht h : ℝ) ^ N) → ∀ h, ‖φ h‖ * T h ≤ max A 0 * K := by
  obtain ⟨C, hC⟩ := hφ.2.2 N
  refine ⟨2 ^ N * max C 0, by positivity, fun T A hi hb h => ?_⟩
  have q1 : 1 ≤ qht h := le_ciInf fun γ => one_le_heightGL F _
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (f := fun γ : ratU σ W.J => ht (γ.1 * h)) (a := 2 * qht h)
    (lt_two_mul_self (zero_lt_one.trans_le q1))
  have h2 : (ht (γ.1 * h) : ℝ) ≤ 2 * qht h := by exact_mod_cast hγ.le
  calc _ ≤ ‖φ h‖ * (max A 0 * (2 * qht h : ℝ) ^ N) := by
        refine mul_le_mul_of_nonneg_left (hi γ γ.2 h ▸ (hb _).trans ?_) (norm_nonneg _)
        gcongr
        exact le_max_left _ _
    _ = max A 0 * (2 ^ N * (‖φ h‖ * (qht h : ℝ) ^ N)) := by ring
    _ ≤ _ := by gcongr; exact (hC h).trans (le_max_left _ _)

theorem finW (hE : EpsOf) (hV : FinVolU) (hp : IsPair B M χX χW om r s r' s') {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)}
    (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ) : IsFiniteMeasure (μ.restrict D) :=
  isFiniteMeasure_restrict.2 (hV F E σ hp.base.cm d _ (hE F E σ B hp.base d W _ _ (Or.inr hp.skew)).1 μ D hμ hD).ne

theorem finX (hE : EpsOf) (hV : FinVolU) (hp : IsPair B M χX χW om r s r' s') : IsFiniteMeasure (M.μ.restrict M.dom) :=
  isFiniteMeasure_restrict.2 (hV F E σ hp.base.cm n _ (hE F E σ B hp.base n X _ _ (Or.inl hp.herm)).1 _ _ hp.good.haar hp.good.dom).ne

theorem theta_rat (hB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {Ψ} (hΨ : Ψ ∈ schA F _) (g) :
    ∀ γ ∈ ratU σ W.J, ∀ h, theta om Ψ g (γ * h) = theta om Ψ g h := fun γ hγ h => by
  simpa using ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Ψ hΨ).2.1 1 (one_mem _) γ hγ g h

theorem th_bd (hB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {f} (hf : IsRapid (Y := W) f) {Ψ} (hΨ : Ψ ∈ schA F _) (b : ℝ≥0) :
    ∃ K : ℝ, ∀ g, ht g ≤ b → ∀ h, ‖f h * star (theta om Ψ g h)‖ ≤ K := by
  obtain ⟨C, k, hC⟩ := ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Ψ hΨ).2.2
  obtain ⟨K, -, hK⟩ := rapid_bound hf k
  refine ⟨_, fun g hg h => (norm_mul _ _).trans_le ((norm_star (theta om Ψ g h)).symm ▸ hK (fun h => ‖theta om Ψ g h‖) (max C 0 * b ^ k)
    (fun γ hγ h => by simp only [theta_rat hB hp hΨ g γ hγ]) (fun h => (hC g h).trans ?_) h)⟩
  rw [mul_assoc, ← mul_pow]
  gcongr
  exact le_max_left _ _

theorem th_cont (hB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {f} (hf : IsRapid (Y := W) f) {Ψ} (hΨ : Ψ ∈ schA F _) :
    Continuous fun x : UA σ X.J × UA σ W.J => f x.2 * star (theta om Ψ x.1 x.2) :=
  (hf.1.comp continuous_snd).mul ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Ψ hΨ).1.star

theorem th_int (hB : ThetaBasic) (hE : EpsOf) (hV : FinVolU) (hp : IsPair B M χX χW om r s r' s') {μ : Measure (UA σ W.J)}
    {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ) {f} (hf : IsRapid (Y := W) f) {Ψ}
    (hΨ : Ψ ∈ schA F _) (g) : Integrable (fun h => f h * star (theta om Ψ g h)) (μ.restrict D) := by
  haveI := finW hE hV hp hμ hD
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  obtain ⟨K, hK⟩ := th_bd hB hp hf hΨ (ht g)
  exact .of_bound ((th_cont hB hp hf hΨ).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable K
    (.of_forall (hK g le_rfl))

theorem thAut_of (hB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hV : FinVolU) : ThAut := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp μ D hμ hD f hf Ψ hΨ
  haveI := finW hE hV hp hμ hD
  obtain ⟨lc, sc, -, -, -, -, -, hb⟩ := hG F E σ hp.base.cm n _ (hE F E σ B hp.base n X _ _ (Or.inl hp.herm)).1
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  refine ⟨gen_cont (th_cont hB hp hf hΨ) fun Ω hΩ => ?_, fun γ hγ g => integral_congr_ae (.of_forall fun h => ?_)⟩
  · obtain ⟨b, hb⟩ := hb Ω hΩ
    obtain ⟨K, hK⟩ := th_bd hB hp hf hΨ b
    exact ⟨K, fun g hg => hK g (hb g hg)⟩
  · have := ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Ψ hΨ).2.1 γ hγ 1 (one_mem _) g h
    rw [one_mul] at this
    simp only [this]

theorem thPerp_of (hB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hV : FinVolU) : ThPerp := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp f hf Ψ hΨ hc ⟨C, k, hC⟩ h0 μ D hμ hD
  haveI := finW hE hV hp hμ hD
  haveI := finX hE hV hp
  haveI := (hG F E σ hp.base.cm n _ (hE F E σ B hp.base n X _ _ (Or.inl hp.herm)).1).2.1
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  obtain ⟨K, -, hK⟩ := rapid_bound hf k
  exact gen_perp ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Ψ hΨ).1 hf.1 hc
    (hK (fun h => ∫ g in M.dom, ‖theta om Ψ g h‖ ∂M.μ) C (fun γ hγ h => by simp only [theta_rat hB hp hΨ _ γ hγ]) hC) (h0 μ D hμ hD)

end PositivityTheory.ThKEnd.Orth

end
