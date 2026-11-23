import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyEqOfAgreeGLs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RdEqFderiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZOpSmooth

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.WaveZ

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Dt (U : ℝ → Mat n → V) : ℝ → Mat n → V := fun t x => deriv (fun s => U s x) t

theorem joint_contDiffAt {U : ℝ → Mat n → V}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)) (t : ℝ) {g : Mat n} (hg : g ∈ GLs n) :
    ContDiffAt ℝ ∞ (Function.uncurry U) (t, g) := by
  exact hU.contDiffAt ((GlobalTheory.CompanionTheory.WaveMult.ZJoint.isOpen_dom n).mem_nhds ⟨Set.mem_univ t, hg⟩)

theorem hasDerivAt_line (t : ℝ) (g : Mat n) :
    HasDerivAt (fun s : ℝ => (s, g)) ((1 : ℝ), (0 : Mat n)) t := by
  exact (hasDerivAt_id t).prodMk (hasDerivAt_const t g)

theorem dt_eq_fderiv {U : ℝ → Mat n → V}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)) {t : ℝ} {g : Mat n} (hg : g ∈ GLs n) :
    Dt U t g = fderiv ℝ (Function.uncurry U) (t, g) ((1 : ℝ), (0 : Mat n)) := by
  have hd : DifferentiableAt ℝ (Function.uncurry U) (t, g) :=
    (GlobalTheory.CompanionTheory.WaveMult.WaveZ.joint_contDiffAt hU t hg).differentiableAt (by first | simp | exact WithTop.coe_ne_zero.2 ENat.top_ne_zero | decide)
  exact (hd.hasFDerivAt.comp_hasDerivAt t (GlobalTheory.CompanionTheory.WaveMult.WaveZ.hasDerivAt_line t g)).deriv

theorem dt_joint {U : ℝ → Mat n → V}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)) :
    ContDiffOn ℝ ∞ (Function.uncurry (Dt U)) (Set.univ ×ˢ GLs n) := by
  have hopen := GlobalTheory.CompanionTheory.WaveMult.ZJoint.isOpen_dom n
  refine (((contDiffOn_infty_iff_fderiv_of_isOpen hopen).1 hU).2.clm_apply
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ × PositivityTheory.RgTw.Mat n =>
      ((1 : ℝ), (0 : PositivityTheory.RgTw.Mat n))) _)).congr ?_
  rintro ⟨t, g⟩ ⟨-, hg⟩
  exact GlobalTheory.CompanionTheory.WaveMult.WaveZ.dt_eq_fderiv hU hg

theorem time_differentiableAt {U : ℝ → Mat n → V}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)) (t : ℝ) {g : Mat n} (hg : g ∈ GLs n) :
    DifferentiableAt ℝ (fun s => U s g) t := by
  have hd : DifferentiableAt ℝ (Function.uncurry U) (t, g) :=
    (GlobalTheory.CompanionTheory.WaveMult.WaveZ.joint_contDiffAt hU t hg).differentiableAt (by first | simp | exact WithTop.coe_ne_zero.2 ENat.top_ne_zero | decide)
  exact (hd.hasFDerivAt.comp_hasDerivAt t (GlobalTheory.CompanionTheory.WaveMult.WaveZ.hasDerivAt_line t g)).differentiableAt

theorem symm_mixed {M W : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Φ : ℝ × M → W} {t : ℝ} {g : M} (hc : ContDiffAt ℝ ∞ Φ (t, g)) (y : M) :
    HasDerivAt (fun s => fderiv ℝ Φ (s, g) ((0 : ℝ), y))
      (fderiv ℝ (fun x => fderiv ℝ Φ (t, x) ((1 : ℝ), (0 : M))) g y) t := by
  have h2 : ContDiffAt ℝ 2 Φ (t, g) :=
    hc.of_le (by first | exact ENat.LEInfty.out | exact_mod_cast le_top | simp)
  have hD1 : ContDiffAt ℝ 1 (fderiv ℝ Φ) (t, g) :=
    h2.fderiv_right (by first | exact le_of_eq one_add_one_eq_two | norm_num)
  have hDd : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) (t, g)) (t, g) :=
    (hD1.differentiableAt one_ne_zero).hasFDerivAt
  have hsymm : IsSymmSndFDerivAt ℝ Φ (t, g) :=
    h2.isSymmSndFDerivAt (by first | exact minSmoothness_of_isRCLikeNormedField.le | simp)
  have hpath : HasDerivAt (fun s : ℝ => (s, g)) ((1 : ℝ), (0 : M)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t g)
  have hL : HasDerivAt (fun s => fderiv ℝ Φ (s, g) ((0 : ℝ), y))
      (fderiv ℝ (fderiv ℝ Φ) (t, g) ((1 : ℝ), (0 : M)) ((0 : ℝ), y)) t :=
    (ContinuousLinearMap.apply ℝ W ((0 : ℝ), y)).hasFDerivAt.comp_hasDerivAt t
      (hDd.comp_hasDerivAt t hpath)
  have hR : HasFDerivAt (fun x => fderiv ℝ Φ (t, x) ((1 : ℝ), (0 : M)))
      ((ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : M))).comp
        ((fderiv ℝ (fderiv ℝ Φ) (t, g)).comp (ContinuousLinearMap.inr ℝ ℝ M))) g :=
    (ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : M))).hasFDerivAt.comp g
      (hDd.comp g (hasFDerivAt_prodMk_right t g))
  rw [hR.fderiv]
  convert hL using 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.inr_apply]
  exact hsymm _ _

theorem dt_Rd (X : Mat n) {U : ℝ → Mat n → V}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)) (t : ℝ) {g : Mat n} (hg : g ∈ GLs n) :
    deriv (fun s => Rd X (U s) g) t = Rd X (Dt U t) g := by
  have hΦ := GlobalTheory.CompanionTheory.WaveMult.WaveZ.joint_contDiffAt hU t hg
  have hL : (fun s => PositivityTheory.RgBcC.Rd X (U s) g) =
      fun s => fderiv ℝ (Function.uncurry U) (s, g) ((0 : ℝ), g * X) :=
    funext fun s => GlobalTheory.CompanionTheory.WaveMult.ZJoint.rd_eq_fderiv U hU hg X
  have hev : GlobalTheory.CompanionTheory.WaveMult.WaveZ.Dt U t =ᶠ[nhds g]
      fun x => fderiv ℝ (Function.uncurry U) (t, x) ((1 : ℝ), (0 : PositivityTheory.RgTw.Mat n)) :=
    Filter.eventuallyEq_of_mem ((GlobalTheory.CompanionTheory.WaveMult.ZJoint.isOpen_GLs n).mem_nhds hg)
      fun x hx => GlobalTheory.CompanionTheory.WaveMult.WaveZ.dt_eq_fderiv hU hx
  rw [hL]
  exact ((GlobalTheory.CompanionTheory.WaveMult.WaveZ.symm_mixed hΦ (g * X)).deriv).trans
    (congrArg (fun L => L (g * X)) (hev.fderiv_eq (𝕜 := ℝ)).symm)

def Good (Φ : (Mat n → V) → (Mat n → V)) : Prop :=
  ZJoint.Pres Φ ∧ (∀ F F' : Mat n → V, (∀ g ∈ GLs n, F g = F' g) → ∀ x ∈ GLs n, Φ F x = Φ F' x) ∧
    ∀ U : ℝ → Mat n → V, ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n) →
      ∀ (t : ℝ), ∀ g ∈ GLs n, deriv (fun s => Φ (U s) g) t = Φ (Dt U t) g

theorem good_Rd (X : Mat n) : Good (V := V) (Rd X) := by
  exact ⟨GlobalTheory.CompanionTheory.WaveMult.ZJoint.pres_Rd X,
    fun F F' h x hx => GlobalTheory.CompanionTheory.WaveMult.Rd_agree_GLs X h x hx,
    fun U hU t g hg => GlobalTheory.CompanionTheory.WaveMult.WaveZ.dt_Rd X hU t hg⟩

theorem good_id : Good (V := V) (n := n) (fun f => f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U hU
    exact hU
  · intro F F' h x hx
    exact h x hx
  · intro U _ t g _
    rfl

theorem good_zero : Good (V := V) (n := n) (fun _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U _
    exact (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ × PositivityTheory.RgTw.Mat n => (0 : V)) _)
  · intro F F' _ x _
    rfl
  · intro U _ t g _
    simp

theorem Good.add {Φ Ψ : (Mat n → V) → (Mat n → V)} (h : Good Φ) (k : Good Ψ) :
    Good (fun f => Φ f + Ψ f) := by
  obtain ⟨s₁, c₁, d₁⟩ := h
  obtain ⟨s₂, c₂, d₂⟩ := k
  refine ⟨?_, ?_, ?_⟩
  · intro U hU
    exact (s₁ U hU).add (s₂ U hU)
  · intro F F' hF x hx
    show Φ F x + Ψ F x = Φ F' x + Ψ F' x
    rw [c₁ F F' hF x hx, c₂ F F' hF x hx]
  · intro U hU t g hg
    have e₁ := GlobalTheory.CompanionTheory.WaveMult.WaveZ.time_differentiableAt (s₁ U hU) t hg
    have e₂ := GlobalTheory.CompanionTheory.WaveMult.WaveZ.time_differentiableAt (s₂ U hU) t hg
    exact ((e₁.hasDerivAt.add e₂.hasDerivAt).deriv).trans
      (congrArg₂ (· + ·) (d₁ U hU t g hg) (d₂ U hU t g hg))

theorem Good.smul {Φ : (Mat n → V) → (Mat n → V)} (c : ℂ) (h : Good Φ) :
    Good (fun f => c • Φ f) := by
  obtain ⟨s₁, c₁, d₁⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro U hU
    exact (s₁ U hU).const_smul c
  · intro F F' hF x hx
    show c • Φ F x = c • Φ F' x
    rw [c₁ F F' hF x hx]
  · intro U hU t g hg
    have e₁ := GlobalTheory.CompanionTheory.WaveMult.WaveZ.time_differentiableAt (s₁ U hU) t hg
    exact ((e₁.hasDerivAt.const_smul c).deriv).trans (congrArg (c • ·) (d₁ U hU t g hg))

theorem Good.comp {Φ Ψ : (Mat n → V) → (Mat n → V)} (h : Good Φ) (k : Good Ψ) :
    Good (fun f => Φ (Ψ f)) := by
  obtain ⟨s₁, c₁, d₁⟩ := h
  obtain ⟨s₂, c₂, d₂⟩ := k
  refine ⟨?_, ?_, ?_⟩
  · intro U hU
    exact s₁ _ (s₂ U hU)
  · intro F F' hF x hx
    exact c₁ (Ψ F) (Ψ F') (fun y hy => c₂ F F' hF y hy) x hx
  · intro U hU t g hg
    exact (d₁ (fun s => Ψ (U s)) (s₂ U hU) t g hg).trans
      (c₁ (GlobalTheory.CompanionTheory.WaveMult.WaveZ.Dt (fun s => Ψ (U s)) t) (Ψ (GlobalTheory.CompanionTheory.WaveMult.WaveZ.Dt U t))
        (fun y hy => d₂ U hU t y hy) g hg)

theorem good_sum {ι : Type} (S : Finset ι) (Φ : ι → (Mat n → V) → (Mat n → V)) (h : ∀ i, Good (Φ i)) :
    Good (fun f => ∑ i ∈ S, Φ i f) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp only [Finset.sum_empty]
    exact GlobalTheory.CompanionTheory.WaveMult.WaveZ.good_zero
  · intro a S ha ih
    simp only [Finset.sum_insert ha]
    exact GlobalTheory.CompanionTheory.WaveMult.WaveZ.Good.add (h a) ih

theorem good_Eu (s : Bool) (a b : Fin n) : Good (V := V) (Eu s a b) := by
  show GlobalTheory.CompanionTheory.WaveMult.WaveZ.Good (fun f : PositivityTheory.RgTw.Mat n → V =>
    (1 / 2 : ℂ) • (PositivityTheory.RgBcC.Rd (Matrix.single a b 1) f +
      (if s = true then -Complex.I else Complex.I) • PositivityTheory.RgBcC.Rd (Matrix.single a b Complex.I) f))
  exact GlobalTheory.CompanionTheory.WaveMult.WaveZ.Good.smul _ (GlobalTheory.CompanionTheory.WaveMult.WaveZ.Good.add
    (GlobalTheory.CompanionTheory.WaveMult.WaveZ.good_Rd _)
    (GlobalTheory.CompanionTheory.WaveMult.WaveZ.Good.smul _ (GlobalTheory.CompanionTheory.WaveMult.WaveZ.good_Rd _)))

theorem good_Epow (s : Bool) (m : ℕ) : ∀ a b : Fin n, Good (V := V) (Epow s m a b) := by
  induction m with
  | zero =>
    intro a b
    show GlobalTheory.CompanionTheory.WaveMult.WaveZ.Good (fun f : PositivityTheory.RgTw.Mat n → V => if a = b then f else 0)
    by_cases hab : a = b
    · simp only [if_pos hab]
      exact GlobalTheory.CompanionTheory.WaveMult.WaveZ.good_id
    · simp only [if_neg hab]
      exact GlobalTheory.CompanionTheory.WaveMult.WaveZ.good_zero
  | succ m ih =>
    intro a b
    show GlobalTheory.CompanionTheory.WaveMult.WaveZ.Good (fun f : PositivityTheory.RgTw.Mat n → V =>
      ∑ c, PositivityTheory.RgBcC.Eu s a c (PositivityTheory.RgBcC.Epow s m c b f))
    exact GlobalTheory.CompanionTheory.WaveMult.WaveZ.good_sum _ _ fun c =>
      GlobalTheory.CompanionTheory.WaveMult.WaveZ.Good.comp (GlobalTheory.CompanionTheory.WaveMult.WaveZ.good_Eu s a c) (ih c b)

theorem good_gel (s : Bool) (m : ℕ) : Good (V := V) (gel (n := n) s m) := by
  show GlobalTheory.CompanionTheory.WaveMult.WaveZ.Good (fun f : PositivityTheory.RgTw.Mat n → V =>
    ∑ a, PositivityTheory.RgBcC.Epow s m a a f)
  exact GlobalTheory.CompanionTheory.WaveMult.WaveZ.good_sum _ _ fun a => GlobalTheory.CompanionTheory.WaveMult.WaveZ.good_Epow s m a a

theorem good_zOp (w : List (Bool × ℕ)) : Good (V := V) (zOp (n := n) w) := by
  induction w with
  | nil =>
    show GlobalTheory.CompanionTheory.WaveMult.WaveZ.Good (fun f : PositivityTheory.RgTw.Mat n → V => f)
    exact GlobalTheory.CompanionTheory.WaveMult.WaveZ.good_id
  | cons p w ih =>
    obtain ⟨s, m⟩ := p
    show GlobalTheory.CompanionTheory.WaveMult.WaveZ.Good (fun f : PositivityTheory.RgTw.Mat n → V =>
      PositivityTheory.RgBcC.gel s m (PositivityTheory.RgBcC.zOp w f))
    exact GlobalTheory.CompanionTheory.WaveMult.WaveZ.Good.comp (GlobalTheory.CompanionTheory.WaveMult.WaveZ.good_gel s m) ih

theorem zOp_add (hR : RCalc) (w : List (Bool × ℕ)) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) : Set.EqOn (zOp w (f + f')) (zOp w f + zOp w f') (GLs n) := by
  induction w with
  | nil =>
    intro x _
    rfl
  | cons p w ih =>
    obtain ⟨s, m⟩ := p
    intro x hx
    show PositivityTheory.RgBcC.gel s m (PositivityTheory.RgBcC.zOp w (f + f')) x =
      PositivityTheory.RgBcC.gel s m (PositivityTheory.RgBcC.zOp w f) x +
        PositivityTheory.RgBcC.gel s m (PositivityTheory.RgBcC.zOp w f') x
    rw [GlobalTheory.CompanionTheory.WaveMult.gel_agree_GLs s m ih x hx]
    exact GlobalTheory.CompanionTheory.WaveMult.Swap.gel_add hR (GlobalTheory.CompanionTheory.WaveMult.Swap.zOp_smooth hR w hf)
      (GlobalTheory.CompanionTheory.WaveMult.Swap.zOp_smooth hR w hf') s m hx

theorem zOp_csmul (hR : RCalc) (w : List (Bool × ℕ)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (c : ℂ) :
    Set.EqOn (zOp w (c • f)) (c • zOp w f) (GLs n) := by
  induction w with
  | nil =>
    intro x _
    rfl
  | cons p w ih =>
    obtain ⟨s, m⟩ := p
    intro x hx
    show PositivityTheory.RgBcC.gel s m (PositivityTheory.RgBcC.zOp w (c • f)) x =
      c • PositivityTheory.RgBcC.gel s m (PositivityTheory.RgBcC.zOp w f) x
    rw [GlobalTheory.CompanionTheory.WaveMult.gel_agree_GLs s m ih x hx]
    exact GlobalTheory.CompanionTheory.WaveMult.Swap.gel_csmul hR (GlobalTheory.CompanionTheory.WaveMult.Swap.zOp_smooth hR w hf) c s m hx

theorem zOp_zero (hR : RCalc) (w : List (Bool × ℕ)) : Set.EqOn (zOp w (0 : Mat n → V)) 0 (GLs n) := by
  induction w with
  | nil =>
    intro x _
    rfl
  | cons p w ih =>
    obtain ⟨s, m⟩ := p
    intro x hx
    show PositivityTheory.RgBcC.gel s m (PositivityTheory.RgBcC.zOp w (0 : PositivityTheory.RgTw.Mat n → V)) x = 0
    rw [GlobalTheory.CompanionTheory.WaveMult.gel_agree_GLs s m ih x hx]
    exact GlobalTheory.CompanionTheory.WaveMult.Swap.gel_zero hR s m hx

theorem zOp_Om (hR : RCalc) (w : List (Bool × ℕ)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (zOp w (Om f)) (Om (zOp w f)) (GLs n) := by
  intro x hx
  have hA : ContDiffOn ℝ ∞ (PositivityTheory.RgBcC.gel true 2 f) (PositivityTheory.RgBcC.GLs n) :=
    GlobalTheory.CompanionTheory.WaveMult.Swap.gel_smooth hR hf true 2
  have hB : ContDiffOn ℝ ∞ (PositivityTheory.RgBcC.gel false 2 f) (PositivityTheory.RgBcC.GLs n) :=
    GlobalTheory.CompanionTheory.WaveMult.Swap.gel_smooth hR hf false 2
  have hAB : ContDiffOn ℝ ∞ (PositivityTheory.RgBcC.gel true 2 f + PositivityTheory.RgBcC.gel false 2 f)
      (PositivityTheory.RgBcC.GLs n) := hA.add hB
  have e₁ := GlobalTheory.CompanionTheory.WaveMult.WaveZ.zOp_csmul hR w hAB (2 : ℂ) hx
  have e₂ := GlobalTheory.CompanionTheory.WaveMult.WaveZ.zOp_add hR w hA hB hx
  have e₃ := GlobalTheory.CompanionTheory.WaveMult.Swap.gel_zOp hR true 2 w hf hx
  have e₄ := GlobalTheory.CompanionTheory.WaveMult.Swap.gel_zOp hR false 2 w hf hx
  show PositivityTheory.RgBcC.zOp w
      ((2 : ℂ) • (PositivityTheory.RgBcC.gel true 2 f + PositivityTheory.RgBcC.gel false 2 f)) x =
    (2 : ℂ) • (PositivityTheory.RgBcC.gel true 2 (PositivityTheory.RgBcC.zOp w f) x +
      PositivityTheory.RgBcC.gel false 2 (PositivityTheory.RgBcC.zOp w f) x)
  rw [e₁, Pi.smul_apply, e₂, Pi.add_apply, e₃, e₄]

theorem zOp_mem_CE (hR : RCalc) {E : KMod n} (w : List (Bool × ℕ)) {f : Mat n → E.V} (hf : f ∈ CE E) :
    zOp w f ∈ CE E := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    obtain ⟨s, m⟩ := p
    exact (hR n).2.1 E _ ih s m

theorem isWave_zOp : RCalc → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (w : List (Bool × ℕ)),
    IsWave E u → IsWave E (fun t => zOp w (u t)) := by
  intro hR n E u w hu
  obtain ⟨h1, h2, h3, h4⟩ := hu
  have C := GlobalTheory.CompanionTheory.WaveMult.WaveZ.good_zOp (V := E.V) (n := n) w
  refine ⟨GlobalTheory.CompanionTheory.WaveMult.ZJoint.zOp_joint n u w h1,
    fun t => GlobalTheory.CompanionTheory.WaveMult.WaveZ.zOp_mem_CE hR w (h2 t), ?_, ?_⟩
  · intro t g hg
    have hderiv : deriv (fun s => PositivityTheory.RgBcC.zOp w (u s) g) =
        fun s => PositivityTheory.RgBcC.zOp w (GlobalTheory.CompanionTheory.WaveMult.WaveZ.Dt u s) g :=
      funext fun s => C.2.2 u h1 s g hg
    have hsec : ∀ y ∈ PositivityTheory.RgBcC.GLs n,
        GlobalTheory.CompanionTheory.WaveMult.WaveZ.Dt (GlobalTheory.CompanionTheory.WaveMult.WaveZ.Dt u) t y = PositivityTheory.RgBcC.Om (u t) y := by
      intro y hy
      rw [← h3 t y hy, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
      rfl
    show iteratedDeriv 2 (fun s => PositivityTheory.RgBcC.zOp w (u s) g) t =
      PositivityTheory.RgBcC.Om (PositivityTheory.RgBcC.zOp w (u t)) g
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero, hderiv,
      C.2.2 (GlobalTheory.CompanionTheory.WaveMult.WaveZ.Dt u) (GlobalTheory.CompanionTheory.WaveMult.WaveZ.dt_joint h1) t g hg,
      GlobalTheory.CompanionTheory.WaveMult.zOp_agree_GLs n w
        (GlobalTheory.CompanionTheory.WaveMult.WaveZ.Dt (GlobalTheory.CompanionTheory.WaveMult.WaveZ.Dt u) t) (PositivityTheory.RgBcC.Om (u t)) hsec g hg]
    exact GlobalTheory.CompanionTheory.WaveMult.WaveZ.zOp_Om hR w (h2 t).1 hg
  · intro g hg
    show deriv (fun s => PositivityTheory.RgBcC.zOp w (u s) g) 0 = 0
    rw [C.2.2 u h1 0 g hg, GlobalTheory.CompanionTheory.WaveMult.zOp_agree_GLs n w
      (GlobalTheory.CompanionTheory.WaveMult.WaveZ.Dt u 0) 0 (fun y hy => h4 y hy) g hg]
    exact GlobalTheory.CompanionTheory.WaveMult.WaveZ.zOp_zero hR w hg

end GlobalTheory.CompanionTheory.WaveMult.WaveZ
