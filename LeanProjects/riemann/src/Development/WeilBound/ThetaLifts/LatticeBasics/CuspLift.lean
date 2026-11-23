import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
import Development.WeilBound.ThetaLifts.LatticeBasics.PolZero

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKEnd (unipU IsCusp)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem IsRapid.bound {φ : UA σ Y.J → ℂ} (hφ : IsRapid φ) (h1 : ∀ h : UA σ Y.J, 1 ≤ ht h) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (T : UA σ Y.J → ℂ) (A : ℝ), 0 ≤ A → (∀ γ ∈ ratU σ Y.J, ∀ h, T (γ * h) = T h) →
      (∀ h, ‖T h‖ ≤ A * (ht h : ℝ) ^ N) → ∀ h, ‖T h‖ * ‖φ h‖ ≤ A * M := by
  obtain ⟨C, hC⟩ := hφ.2.2 N
  refine ⟨2 ^ N * max C 0, by positivity, fun T A hA hi hb h => ?_⟩
  have q1 : 1 ≤ qht h := le_ciInf fun γ => h1 _
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (f := fun γ : ratU σ Y.J => ht (γ.1 * h)) (a := 2 * qht h)
    (lt_two_mul_self (zero_lt_one.trans_le q1))
  calc _ ≤ A * (2 * qht h : ℝ) ^ N * ‖φ h‖ := mul_le_mul_of_nonneg_right (hi γ γ.2 h ▸ (hb _).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) (by exact_mod_cast hγ.le) N) hA)) (norm_nonneg _)
    _ = A * (2 ^ N * (‖φ h‖ * (qht h : ℝ) ^ N)) := by ring
    _ ≤ _ := by gcongr; exact (hC h).trans (le_max_left _ _)

variable {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} {χ : Chr F E} {s₀ : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}

theorem eis_bound (he : ∀ h h', IsEmb h h' (e (h, h'))) {c : ℝ≥0} (h1 : ∀ h h' x, IsEmb (σ := σ) (Y := Y) h h' x → ht2 x ≤ c * (ht h * ht h'))
    (h2 : ∀ h : UA σ Y.J, 1 ≤ ht h) {φ : UA σ Y.J → ℂ} (hφ : IsRapid φ) (C : ℝ) (N : ℕ) (b : ℝ≥0) :
    ∃ M : ℝ, ∀ Ê : G2 σ Y → ℂ, (∀ c ∈ rat2 σ Y, ∀ x, Ê (c * x) = Ê x) → (∀ x, ‖Ê x‖ ≤ C * (ht2 x : ℝ) ^ N) →
      ∀ h, ht h ≤ b → ∀ h', ‖Ê (e (h, h'))‖ * ‖φ h'‖ ≤ M := by
  obtain ⟨M, -, hM⟩ := hφ.bound h2 N
  refine ⟨max C 0 * (c * b) ^ N * M, fun Ê hi hb h hh => hM (fun x => Ê (e (h, x))) _ (by positivity) (fun γ hγ x => ?_) fun x => ?_⟩
  · rw [← hi _ ((he 1 γ).rat (one_mem _) hγ) (e (h, x)), ← map_mul, Prod.mk_mul_mk, one_mul]
  · refine (hb _).trans ?_
    rw [mul_assoc, ← mul_pow]
    have : ht2 (e (h, x)) ≤ c * b * ht x := (h1 _ _ _ (he h x)).trans (by rw [mul_assoc]; gcongr)
    gcongr
    exacts [le_max_left _ _, by exact_mod_cast this]

theorem sfin {A : Type} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ] : SFinite μ := inferInstance

theorem sfin' {A : Type} [Group A] [TopologicalSpace A] [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A]
    (μ : Measure A) [μ.IsHaarMeasure] : SFinite μ := inferInstance

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem ct_zero (hO : OffOpen) (hU : PositivityTheory.ThKEnd.Grp.UnipUGood) (hE1 : EisContinues) (hH : HtEmb) {B : Base F E} {r s : ℕ}
    (hB : B.IsGood σ) (hn : 1 ≤ n) (hY : Y.IsSkew σ B r s) (d0 : Y.J.det ≠ 0) [LocallyCompactSpace (UA σ Y.J)]
    [SecondCountableTopology (UA σ Y.J)] [T2Space (UA σ Y.J)] (hb : ∀ Ω : Set (UA σ Y.J), IsCompact Ω → ∃ C : ℝ≥0, ∀ g ∈ Ω, ht g ≤ C)
    (hχ : IsHecke F E χ) (he : ∀ h h', IsEmb h h' (e (h, h'))) (ce : Continuous e) (hS : IsStab2 B K)
    (hK : IsCompact (K : Set (G2 σ Y))) (ha : IsHgt K a) (ca : Continuous a) (a0 : ∀ x, 0 < a x) (cf : Continuous f)
    (hf : Law χ (s₀ + n / 2) f) {U Ê} (hE : IsEisCont (flat a f s₀) U Ê) {μ : Measure (UA σ Y.J)} {D : Set (UA σ Y.J)}
    (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ Y.J) D μ) (fin : μ D < ⊤) {t₀ : ℝ}
    (hi : ∀ t, t₀ ≤ t → Integrable (fun g => a (e (1, g)) ^ t) μ) {φ : UA σ Y.J → ℂ} (hφ : IsRapid φ) (hc : IsCusp Y φ) :
    ∀ s ∈ U, IsCusp Y fun h => ∫ h' in D, Ê s (e (h, h')) * detInv χ h' * φ h' ∂μ := by
  intro s hs V v1 v2 κ 𝓜 k1 k2 h
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨g, -⟩ := hU F E σ hB.cm n Y (.inr hY.skew) d0 V
  haveI := g.sc
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 fin.ne
  haveI : IsFiniteMeasure (κ.restrict 𝓜) := isFiniteMeasure_restrict.2 (g.fin κ 𝓜 k1 k2).2.ne
  haveI : SFinite (μ.restrict D) := sfin _
  haveI : SFinite (κ.restrict 𝓜) := sfin _
  haveI : SFinite μ := sfin' μ
  obtain ⟨c, c1, -, c3⟩ := hH F E σ n Y
  obtain ⟨t₁, half⟩ := hE.half
  have cE : ∀ s ∈ U, Continuous (Ê s) := fun s hs =>
    hE.cont.comp_continuous (f := fun x => (s, x)) (by fun_prop) fun _ => ⟨hs, trivial⟩
  have iv : ∀ s ∈ U, ∀ γ ∈ rat2 σ Y, ∀ x, Ê s (γ * x) = Ê s x := fun s hs γ hγ x =>
    An.ident hE.isOpen hE.conn (hE.hol _) (hE.hol _) (fun s hs => ⟨(half s hs).1,
      (hf.flat ha a0 s).eis_rat hχ (half s hs).2 hγ _⟩) hs
  obtain ⟨Ω, hΩ, cov⟩ := g.cov
  obtain ⟨b, hb'⟩ := hb _ ((hΩ.image continuous_subtype_val).image (continuous_mul_const h))
  let k : ℂ → unipU σ Y V × UA σ Y.J → ℂ := fun s y => Ê s (e (y.1.1 * h, y.2)) * detInv χ y.2 * φ y.2
  have ck : ∀ s ∈ U, Continuous (k s) := fun s hs =>
    (((cE s hs).comp (ce.comp (by fun_prop))).mul ((continuous_detInv hχ).comp continuous_snd)).mul (hφ.1.comp continuous_snd)
  have bk : ∀ s ∈ U, ∃ ε > 0, ∃ M, ∀ s' ∈ U ∩ Metric.ball s ε, ∀ y, ‖k s' y‖ ≤ M := fun s hs => by
    obtain ⟨ε, C, N, h0, hg⟩ := hE.grow s hs
    obtain ⟨M, hM⟩ := eis_bound he c1 c3 hφ C N b
    refine ⟨ε, h0, M, fun s' hs' y => ?_⟩
    obtain ⟨γ, hγ, h1⟩ := cov y.1
    have := hM (Ê s') (iv s' hs'.1) (hg s' hs'.2) _ (hb' _ ⟨_, ⟨_, h1, rfl⟩, rfl⟩) y.2
    rw [show e ((γ * y.1).1 * h, y.2) = e (γ.1, 1) * e (y.1.1 * h, y.2) by simp [← map_mul, mul_assoc],
      iv s' hs'.1 _ ((he _ _).rat hγ (one_mem _))] at this
    simpa only [k, norm_mul, norm_detInv, mul_one] using this
  have ik : ∀ s ∈ U, Integrable (k s) ((κ.restrict 𝓜).prod (μ.restrict D)) := fun s hs => by
    obtain ⟨ε, h0, M, hM⟩ := bk s hs
    exact .of_bound (ck s hs).aestronglyMeasurable M (.of_forall (hM s ⟨hs, Metric.mem_ball_self h0⟩))
  have hol : DifferentiableOn ℂ (fun s => ∫ y, k s y ∂(κ.restrict 𝓜).prod (μ.restrict D)) U := fun s hs => by
    obtain ⟨ε, h0, M, hM⟩ := bk s hs
    have o := hE.isOpen.inter (Metric.isOpen_ball (x := s) (ε := ε))
    exact ((An.diffOn_integral o (fun s hs => (ck s hs.1).aestronglyMeasurable)
      (fun y => (((hE.hol _).mul_const _).mul_const _).mono Set.inter_subset_left) fun S hS _ =>
        ⟨M, fun s hs => hM s (hS hs)⟩).differentiableAt (o.mem_nhds ⟨hs, Metric.mem_ball_self h0⟩)).differentiableWithinAt
  have l1 : Law (1 : Chr F E) ((0 : ℂ) + n / 2) fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2) := fun p t x hp => by
    beta_reduce
    rw [ha.mul hp, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (absE_pos _).le (a0 x).le]; simp
  have h1 : IsHecke F E (1 : Chr F E) := ⟨continuous_const, fun _ => rfl⟩
  obtain ⟨U₁, Ê₁, hE₁, -⟩ := hE1 F E σ B n Y r _ hB hn (.inr hY) 1 h1 0 (fun x => by simp only [pow_zero, ite_self]; rfl) K a hS ha 0 (fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2))
    ⟨(Complex.continuous_ofReal.comp ca).cpow continuous_const fun x => Complex.ofReal_mem_slitPlane.2 (a0 x), l1, by
      refine FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2)).subset ?_)
      rintro _ ⟨k, rfl⟩
      refine funext fun x => ?_
      obtain ⟨p, t, hp, k', hk', rfl⟩ := ha.iwa x
      show (a _ : ℂ) ^ _ = (a _ : ℂ) ^ _
      simp only [mul_assoc, ha.val p t hp _ (mul_mem hk' k.2), ha.val p t hp _ hk']⟩
  obtain ⟨t₂, half₁⟩ := hE₁.half
  rw [← integral_prod (k s) (ik s hs)]
  refine An.ident hE.isOpen hE.conn hol (differentiableOn_const 0) (t := max (max t₁ t₂) (t₀ - n / 2)) (fun s hs => ?_) hs
  have s1 := (le_max_left _ _).trans_lt hs
  obtain ⟨u, sm⟩ := half s ((le_max_left _ _).trans_lt s1)
  have cs := continuous_flat (s₀ := s₀) cf ca a0 s
  obtain ⟨C, hC⟩ := (hf.flat (s₀ := s₀) ha a0 s).bound cs ha hK
  have ez : (s - s₀ + (s₀ + n / 2)).re = s.re + n / 2 := by simp; ring
  rw [ez] at hC
  have i1 : Integrable (fun g => flat a f s₀ s (e (1, g))) μ :=
    ((hi (s.re + n / 2) (by have := (le_max_right _ _).trans_lt hs; linarith)).const_mul C).mono'
      (cs.comp (ce.comp (Continuous.prodMk_right 1))).aestronglyMeasurable (.of_forall fun g => hC _)
  have i2 := i1.mul_bdd (continuous_detInv hχ).aestronglyMeasurable (.of_forall fun g => (norm_detInv χ g).le)
  obtain ⟨u₁, sm₁⟩ := half₁ (s.re : ℂ) (by simpa using (le_max_right _ _).trans_lt s1)
  obtain ⟨ε, C₁, N, h0, hg⟩ := hE₁.grow _ u₁
  have hfin : ∀ x, ∑' q : Cos σ Y, ∫⁻ y in D, ‖eisTerm (flat a f s₀ s) (e (x, y)) q * detInv χ y * φ y‖ₑ ∂μ ≠ ⊤ := fun x => by
    obtain ⟨M, hM⟩ := eis_bound he c1 c3 hφ C₁ N (ht x)
    have hM' := hM _ (fun c hc => (l1.flat ha a0 _).eis_rat h1 sm₁ hc) (hg _ (Metric.mem_ball_self h0)) x le_rfl
    haveI : Countable (Cos σ Y) := by
      exact Set.countable_univ_iff.1 ((sm₁ 1).summable.countable_support.mono fun q _ => mul_ne_zero
        (Complex.cpow_ne_zero_iff.2 (.inl (Complex.ofReal_ne_zero.2 (a0 _).ne')))
        (Complex.cpow_ne_zero_iff.2 (.inl (Complex.ofReal_ne_zero.2 (a0 _).ne'))))
    rw [← lintegral_tsum (f := fun q y => ‖eisTerm (flat a f s₀ s) (e (x, y)) q * detInv χ y * φ y‖ₑ) fun q => (((cs.comp (continuous_const.mul (ce.comp (Continuous.prodMk_right x)))).mul
      (continuous_detInv hχ)).mul hφ.1).measurable.enorm.aemeasurable]
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in D, ENNReal.ofReal (max C 0 * M) ∂μ)
      (by rw [setLIntegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top fin.ne) (lintegral_mono fun y => ?_)
    have t1 : ∀ q : Cos σ Y, eisTerm (flat a (fun x => (a x : ℂ) ^ ((0 : ℂ) + n / 2)) 0 (s.re : ℂ)) (e (x, y)) q =
        ((a (q.out.1 * e (x, y)) ^ (s.re + n / 2) : ℝ) : ℂ) := fun q => by
      rw [eisTerm, flat, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (a0 _).ne'), Complex.ofReal_cpow (a0 _).le]
      congr 1; push_cast; ring
    have t2 : HasSum (fun q : Cos σ Y => a (q.out.1 * e (x, y)) ^ (s.re + n / 2)) (Ê₁ s.re (e (x, y))).re := by
      simpa only [t1, Complex.ofReal_re] using Complex.hasSum_re (sm₁ (e (x, y)))
    have p0 : ∀ q : Cos σ Y, 0 ≤ max C 0 * (a (q.out.1 * e (x, y)) ^ (s.re + n / 2) * ‖φ y‖) := fun q => by
      have := Real.rpow_nonneg (a0 (q.out.1 * e (x, y))).le (s.re + n / 2); positivity
    have t3 := (t2.mul_right ‖φ y‖).mul_left (max C 0)
    refine (ENNReal.tsum_le_tsum fun q => ?_).trans ((ENNReal.ofReal_tsum_of_nonneg p0 t3.summable).symm.le.trans
      (ENNReal.ofReal_le_ofReal ?_))
    · rw [← ofReal_norm_eq_enorm, norm_mul, norm_mul, norm_detInv, mul_one, ← mul_assoc]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ((hC _).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (a0 _).le _))) (norm_nonneg _))
    · rw [t3.tsum_eq]
      exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (Complex.re_le_norm _) (norm_nonneg _)).trans (hM' y))
        (le_max_right _ _)
  refine ⟨u, ?_⟩
  rw [integral_prod (k s) (ik s u)]
  simp only [k, fun x => unfoldC hO hU hB hY d0 hχ he ce cs (hf.flat ha a0 s) sm hμ hD i1 hφ hc x (hfin x)]
  obtain ⟨b₀, hb₀⟩ := hφ.2.2 0
  rw [integral_integral_swap (f := fun (m : unipU σ Y V) g => flat a f s₀ s (e (1, g)) * detInv χ g * φ (m.1 * h * g))
    ((i2.comp_snd _).mul_bdd (c := b₀) (hφ.1.comp (by fun_prop)).aestronglyMeasurable
      (.of_forall fun y => by simpa using hb₀ (y.1.1 * h * y.2)))]
  simp only [integral_const_mul, mul_assoc _ h, hc V v1 v2 κ 𝓜 k1 k2, mul_zero, integral_zero]

end GlobalTheory.ThK.Dbl

end
