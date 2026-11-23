import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.TSpan

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.CentralizerFixed

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem pb_congr {q : ℕ} {g g' : Gp L N} (e : actL g = actL g') (ω : Form (HS L N) q) :
    pb g ω = pb g' ω := by
  unfold pb
  rw [e]

theorem pb_mul {q : ℕ} (g g' : Gp L N) (ω : Form (HS L N) q) (h : HS L N) :
    pb (g * g') ω h = (pb g ω (actL g' h)).compContinuousLinearMap (actL g') := by
  have e : actL (g * g') = (actL g).comp (actL g') := by
    ext1 x
    exact actL_mul g g' x
  unfold pb
  rw [e]
  ext m
  rfl

theorem pb_one {q : ℕ} (ω : Form (HS L N) q) (h : HS L N) : pb 1 ω h = ω h := by
  have e : actL (1 : Gp L N) = ContinuousLinearMap.id ℝ (HS L N) := by
    ext1 x
    exact actL_one x
  unfold pb
  rw [e]
  ext m
  rfl

theorem sc_zero (hadd : ∀ t t' : InfinitePlace L → ℝ, (sc (t + t') : Gp L N) = sc t * sc t') :
    (sc 0 : Gp L N) = 1 := by
  have := hadd 0 0
  rw [add_zero] at this
  exact mul_left_cancel (a := (sc 0 : Gp L N)) (this.symm.trans (mul_one _).symm)

theorem fix_zero {q : ℕ} {ω : Form (HS L N) q}
    (hadd : ∀ t t' : InfinitePlace L → ℝ, (sc (t + t') : Gp L N) = sc t * sc t') : (0 : InfinitePlace L → ℝ) ∈ Fix ω := by
  intro h _
  rw [sc_zero hadd]
  exact pb_one ω h

theorem fix_add {q : ℕ} {ω : Form (HS L N) q}
    (hadd : ∀ t t' : InfinitePlace L → ℝ, (sc (t + t') : Gp L N) = sc t * sc t') {t t' : InfinitePlace L → ℝ}
    (ht : t ∈ Fix ω) (ht' : t' ∈ Fix ω) : t + t' ∈ Fix ω := by
  intro h hh
  have e := ht (actL (sc t') h) (actL_pos _ hh)
  rw [hadd, pb_mul, e]
  exact ht' h hh

theorem av_congr {q : ℕ} (v : InfinitePlace L → ℝ) {ω ω' : Form (HS L N) q}
    (e : ∀ h ∈ Pos L N, ω h = ω' h) : ∀ h ∈ Pos L N, av v ω h = av v ω' h := by
  intro h hh
  show (∫ τ in (0:ℝ)..1, pb (sc (τ • v)) ω h) = ∫ τ in (0:ℝ)..1, pb (sc (τ • v)) ω' h
  congr 1
  funext τ
  show (ω (actL _ h)).compContinuousLinearMap _ = (ω' (actL _ h)).compContinuousLinearMap _
  rw [e _ (actL_pos _ hh)]

theorem inv_av (hA : TAv) {q : ℕ} (v : InfinitePlace L → ℝ) {ω : Form (HS L N) q}
    (hc : ContinuousOn ω (Pos L N)) {g : Gp L N} (hg : ∀ t, sc t * g = g * sc t) (hinv : FInv ω g) :
    FInv (av v ω) g := by
  intro h hh
  have := (hA L N q v ω hc).2.1 g hg h hh
  change pb g (av v ω) h = _
  rw [this]
  exact av_congr v (fun k hk => hinv k hk) h hh

theorem sc_cont (v : InfinitePlace L → ℝ) : Continuous fun τ : ℝ => (sc (τ • v) : Gp L N) := by
  refine continuous_pi fun w => ?_
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun τ : ℝ => Matrix.scalar (Fin N) ((Real.exp ((τ • v) w) : ℂ))
    simp only [Matrix.scalar_apply, Pi.smul_apply, smul_eq_mul]
    refine Continuous.matrix_diagonal (continuous_pi fun _ => ?_)
    fun_prop
  · show Continuous fun τ : ℝ => Matrix.scalar (Fin N) (((Real.exp ((τ • v) w) : ℂ))⁻¹)
    simp only [Matrix.scalar_apply, Pi.smul_apply, smul_eq_mul]
    refine Continuous.matrix_diagonal (continuous_pi fun _ => ?_)
    refine Continuous.inv₀ (by fun_prop) (fun τ => ?_)
    exact_mod_cast (Real.exp_pos _).ne'

def Carr {k : ℕ} (ω₀ : Form (HS L N) (k + 1)) (B : Gp L N → ℝ) (ω : Form (HS L N) (k + 1)) : Prop :=
  ContinuousOn ω (Pos L N) ∧ dC (intP ω) = 0 ∧ (∀ γ, FInv ω (emb L N γ)) ∧
    (∀ c : ℝ, (fun _ => c) ∈ Fix ω) ∧
    (∀ z : Chn (Gm L N) (k + 1), IsCyc z →
      ev (emb L N) (intP ω) (one L N) z = ev (emb L N) (intP ω₀) (one L N) z) ∧
    ∃ C, 0 ≤ C ∧ ∀ x, ‖fr ω x‖ ≤ C * B x

theorem step_dC (hA : TAv) {k : ℕ} {ω : Form (HS L N) (k + 1)} (hc : ContinuousOn ω (Pos L N))
    (hd : dC (intP ω) = 0) (v : InfinitePlace L → ℝ) : dC (intP (av v ω)) = 0 := by
  funext y
  obtain ⟨_, _, _, hcont, hint, _⟩ := hA L N (k+1) v ω hc
  have e : dC (intP (av v ω)) y = ∫ τ in (0:ℝ)..1, dC (intP ω) (fun j => (sc (τ • v) : Gp L N) • y j) := by
    simp only [dC, hint]
    rw [intervalIntegral.integral_finset_sum]
    · congr 1
      funext i
      rw [intervalIntegral.integral_const_mul]
    · intro i _
      exact ((hcont _).const_mul _).intervalIntegrable _ _
  rw [e, hd]
  simp

theorem step_ev (hEv : SEv) (hSc : TScal) (hSi : TSimp) (hA : TAv) {k : ℕ} {ω : Form (HS L N) (k + 1)}
    (hc : ContinuousOn ω (Pos L N)) (hd : dC (intP ω) = 0) (hΓ : ∀ γ, FInv ω (emb L N γ))
    (v : InfinitePlace L → ℝ) (z : Chn (Gm L N) (k + 1)) (hz : IsCyc z) :
    ev (emb L N) (intP (av v ω)) (one L N) z = ev (emb L N) (intP ω) (one L N) z := by
  obtain ⟨_, _, _, hcont, hint, _⟩ := hA L N (k+1) v ω hc
  have hcomm := (hSc L N).2.1
  have hinvF : Inv (emb L N) (intP ω) := fun γ y => (hSi L N (k+1)).2 ω _ (hΓ γ) y
  have hcst := (hEv (Gm L N) (Gp L N) (Pos L N) (emb L N) k (intP ω) hinvF hd).2
  have key : ∀ τ : ℝ, (z.sum fun g r => r * intP ω (fun j => (sc (τ • v) : Gp L N) • (emb L N (Fin.partialProd g j) • one L N)))
      = ev (emb L N) (intP ω) (one L N) z := by
    intro τ
    rw [← hcst ((sc (τ • v) : Gp L N) • one L N) (one L N) z hz]
    simp only [ev]
    refine Finsupp.sum_congr fun g _ => ?_
    congr 2
    funext j
    rw [smul_smul, smul_smul, hcomm]
  show (z.sum fun g r => r * intP (av v ω) (fun j => emb L N (Fin.partialProd g j) • one L N)) = _
  simp only [hint]
  have e : (z.sum fun g r => r * ∫ τ in (0:ℝ)..1, intP ω (fun j => (sc (τ • v) : Gp L N) • (emb L N (Fin.partialProd g j) • one L N)))
      = ∫ τ in (0:ℝ)..1, z.sum fun g r => r * intP ω (fun j => (sc (τ • v) : Gp L N) • (emb L N (Fin.partialProd g j) • one L N)) := by
    simp only [Finsupp.sum]
    rw [intervalIntegral.integral_finset_sum]
    · congr 1
      funext g
      rw [intervalIntegral.integral_const_mul]
    · intro g _
      exact ((hcont _).const_mul _).intervalIntegrable _ _
  rw [e]
  simp only [key]
  simp

theorem step_bd (hSc : TScal) (hA : TAv) {k : ℕ} {ω : Form (HS L N) (k + 1)} (hc : ContinuousOn ω (Pos L N))
    {B : Gp L N → ℝ} (hB : ∀ K : Set (Gp L N), IsCompact K → ∃ C, ∀ g ∈ K, ∀ x, B (x * g) ≤ C * B x)
    (hB0 : ∀ x, 0 ≤ B x) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖fr ω x‖ ≤ C * B x) (v : InfinitePlace L → ℝ) :
    ∃ C', 0 ≤ C' ∧ ∀ x, ‖fr (av v ω) x‖ ≤ C' * B x := by
  obtain ⟨-, hcomm, -, -, -⟩ := hSc L N
  obtain ⟨-, -, -, -, -, hAfr⟩ := hA L N (k + 1) v ω hc
  obtain ⟨CK, hCK⟩ := hB _ ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).image (sc_cont (N := N) v))
  refine ⟨C * max CK 0, mul_nonneg hC0 (le_max_right _ _), fun x => ?_⟩
  rw [hAfr x]
  have hb : ∀ τ ∈ Set.uIoc (0 : ℝ) 1, ‖fr ω (sc (τ • v) * x)‖ ≤ C * max CK 0 * B x := fun τ hτ => by
    rw [Set.uIoc_of_le zero_le_one] at hτ
    rw [hcomm]
    calc ‖fr ω (x * sc (τ • v))‖ ≤ C * B (x * sc (τ • v)) := hC _
      _ ≤ C * (max CK 0 * B x) := mul_le_mul_of_nonneg_left
          ((hCK _ ⟨τ, ⟨hτ.1.le, hτ.2⟩, rfl⟩ x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hB0 x))) hC0
      _ = C * max CK 0 * B x := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this

theorem step (hEv : SEv) (hSc : TScal) (hSi : TSimp) (hA : TAv) {k : ℕ} {ω₀ ω : Form (HS L N) (k + 1)}
    {B : Gp L N → ℝ} (hB : ∀ K : Set (Gp L N), IsCompact K → ∃ C, ∀ g ∈ K, ∀ x, B (x * g) ≤ C * B x)
    (hB0 : ∀ x, 0 ≤ B x) (hω : Carr ω₀ B ω) (v : InfinitePlace L → ℝ) (hv : v ∈ Fix ω) :
    Carr ω₀ B (av v ω) ∧ (∀ t ∈ Fix ω, t ∈ Fix (av v ω)) ∧ ∀ σ : ℝ, σ • v ∈ Fix (av v ω) := by
  obtain ⟨hc, hd, hΓ, hdiag, hev, C, hC0, hC⟩ := hω
  obtain ⟨-, hcomm, -, -, -⟩ := hSc L N
  have hfix : ∀ t ∈ Fix ω, t ∈ Fix (av v ω) := fun t ht =>
    inv_av hA v hc (fun t' => hcomm t' (sc t)) ht
  have hper := ((hA L N (k + 1) v ω hc).2.2.1 hv)
  have hAc := (hA L N (k + 1) v ω hc).1
  exact ⟨⟨hAc, step_dC hA hc hd v, fun γ => inv_av hA v hc (fun t => hcomm t _) (hΓ γ),
    fun c => hfix _ (hdiag c), fun z hz => (step_ev hEv hSc hSi hA hc hd hΓ v z hz).trans (hev z hz),
    step_bd hSc hA hc hB hB0 hC0 hC v⟩, hfix, hper⟩

theorem iter (hEv : SEv) (hSc : TScal) (hSi : TSimp) (hA : TAv) {k : ℕ} {ω₀ ω : Form (HS L N) (k + 1)}
    {B : Gp L N → ℝ} (hB : ∀ K : Set (Gp L N), IsCompact K → ∃ C, ∀ g ∈ K, ∀ x, B (x * g) ≤ C * B x)
    (hB0 : ∀ x, 0 ≤ B x) (hω : Carr ω₀ B ω) (l : List (𝓞 L)ˣ) :
    ∃ ω', Carr ω₀ B ω' ∧ ∀ u ∈ l, ∀ σ : ℝ, σ • lg u ∈ Fix ω' := by
  induction l with
  | nil => exact ⟨ω, hω, by simp⟩
  | cons u l ih =>
    obtain ⟨ω1, h1, hl1⟩ := ih
    obtain ⟨-, -, hemb, -, -⟩ := hSc L N
    have hu : lg u ∈ Fix ω1 := by
      intro h hh
      rw [pb_congr (hemb u).symm]
      exact h1.2.2.1 _ h hh
    obtain ⟨h2, hfix, hper⟩ := step hEv hSc hSi hA hB hB0 h1 (lg u) hu
    refine ⟨av (lg u) ω1, h2, fun u' hu' σ => ?_⟩
    rcases List.mem_cons.1 hu' with rfl | hu'
    · exact hper σ
    · exact hfix _ (hl1 u' hu' σ)

theorem join (hSp : TSpan) (hSc : TScal) (hSi : TSimp) (hA : TAv) (hEv : SEv) : SCen := by
  intro L _ _ N k ω hG hΓ hS B hB hfr
  have hB0 : ∀ x, 0 ≤ B x := fun x => (norm_nonneg _).trans (hfr x)
  obtain ⟨l, hl⟩ := hSp L
  have h0 : Carr ω B ω := ⟨hG.1, hG.2, hΓ,
    fun c => hS (fun _ => Units.mk0 ((Real.exp c : ℝ) : ℂ) (by exact_mod_cast (Real.exp_pos c).ne'))
      (fun _ _ => rfl),
    fun _ _ => rfl, 1, zero_le_one, fun x => by simpa using hfr x⟩
  obtain ⟨ω', ⟨hc, hd, hΓ', hdiag, hev, C, -, hC⟩, hlf⟩ := iter hEv hSc hSi hA hB hB0 h0 l
  obtain ⟨hadd, -, -, hscal, -⟩ := hSc L N
  have key : ∀ t ∈ Submodule.span ℝ (insert (fun _ => (1 : ℝ)) {x | ∃ u ∈ l, lg u = x}),
      ∀ σ : ℝ, σ • t ∈ Fix ω' := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      rcases hx with rfl | ⟨u, hu, rfl⟩
      · intro σ
        convert hdiag σ using 1
        funext w
        simp
      · exact hlf u hu
    | zero => intro σ; rw [smul_zero]; exact fix_zero hadd
    | add x y _ _ hx hy => intro σ; rw [smul_add]; exact fix_add hadd (hx σ) (hy σ)
    | smul a x _ hx => intro σ; rw [smul_smul]; exact hx _
  refine ⟨ω', ⟨hc, hd⟩, hΓ', fun s => ?_, hev, C, hC⟩
  intro h hh
  have := key _ (hl (fun w => Real.log ‖(s w : ℂ)‖)) 1 h hh
  rw [one_smul] at this
  change pb (scal L N s) ω' h = ω' h
  rw [pb_congr (hscal s)]
  exact this

end PositivityTheory.KB.CentralizerFixed

end
