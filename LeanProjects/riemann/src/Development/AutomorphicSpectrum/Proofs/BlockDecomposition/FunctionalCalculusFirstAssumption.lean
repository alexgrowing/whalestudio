import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveFc.Asm

variable {n : ℕ}

theorem val_mem (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem open_GLs : IsOpen (GLs n) := by
  have : GLs n = (fun g : Mat n => g.det) ⁻¹' {0}ᶜ := rfl
  rw [this]
  exact isOpen_compl_singleton.preimage (Continuous.matrix_det continuous_id)

theorem mul_mem_GLs {y : Mat n} (hy : y ∈ GLs n) (h : G n) : y * h.val ∈ GLs n := by
  have h1 : h.val.det ≠ 0 := val_mem h
  have h2 : y.det ≠ 0 := hy
  show (y * h.val).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero h2 h1

section Rw

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_congr (X : Mat n) {f f' : Mat n → V} (h : ∀ y ∈ GLs n, f y = f' y) :
    ∀ g ∈ GLs n, Rd X f g = Rd X f' g := by
  intro g hg
  have e : f =ᶠ[𝓝 g] f' := Filter.eventuallyEq_of_mem (open_GLs.mem_nhds hg) h
  simp only [Rd, e.fderiv_eq]

theorem Rw_congr (w : List (Bool × Fin n × Fin n)) {f f' : Mat n → V} (h : ∀ y ∈ GLs n, f y = f' y) :
    ∀ g ∈ GLs n, Rw w f g = Rw w f' g := by
  induction w with
  | nil => exact h
  | cons p w ih => exact Rd_congr _ ih

end Rw

section Calc

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable {μ} in
theorem sob_memLp {f : Mat n → V} (hf : Sob μ f) : MemLp (fun y : G n => f y.val) 2 μ := hf.2 []

variable {μ} in
theorem sob_cont {f : Mat n → V} (hf : Sob μ f) : ContinuousOn f (GLs n) := hf.1.continuousOn

theorem cls_mem {f : Mat n → V} (hf : Sob μ f) : cls μ f ∈ Msob μ V :=
  Submodule.subset_span ⟨f, hf, rfl⟩

variable {μ} in
theorem cls_eq_of_sob (hC : ClsFacts) (hU : Unimod) {f f' : Mat n → V} (hf : Sob μ f) (hf' : Sob μ f')
    (h : cls μ f = cls μ f') : ∀ g ∈ GLs n, f g = f' g :=
  (hC n μ V hU).1 f f' (sob_cont hf) (sob_cont hf') (sob_memLp hf) (sob_memLp hf') h

variable {μ} in
theorem cls_congr (hC : ClsFacts) (hU : Unimod) {f f' : Mat n → V} (h : ∀ g ∈ GLs n, f g = f' g) :
    cls μ f = cls μ f' :=
  (hC n μ V hU).2.2.1 f f' h

variable {μ}

theorem sob_trans (hO : SobOps) (hL : LgFacts) (hU : Unimod) (hR : RCalc) {f : Mat n → V} (hf : Sob μ f)
    (h : G n) : Sob μ (fun y => f (y * h.val)) :=
  ((hO n μ V hL hU hR f hf).2.2.2.2 h (ContinuousLinearMap.id ℂ V)).1

theorem rR_cls (hC : ClsFacts) (hO : SobOps) (hL : LgFacts) (hU : Unimod) (hR : RCalc) {f : Mat n → V}
    (hf : Sob μ f) (h : G n) : rR μ V h (cls μ f) = cls μ (fun y => f (y * h.val)) :=
  (hC n μ V hU).2.2.2.1 h f (sob_memLp hf)

variable {Ω : Msob μ V →ₗ[ℂ] Msob μ V} {T : Lp V 2 μ →L[ℂ] Lp V 2 μ} [CompleteSpace V]

theorem comm_of (hC : ClsFacts) (hO : SobOps) (hL : LgFacts) (hU : Unimod) (hR : RCalc)
    (F : FCalc (Lp V 2 μ) (Msob μ V) Ω T) (hrep : ∀ x ∈ Msob μ V, ∃ f, Sob μ f ∧ cls μ f = x)
    (hΩ : ∀ (f : Mat n → V) (hf : cls μ f ∈ Msob μ V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp V 2 μ) = cls μ (Om f))
    (S : Lp V 2 μ →L[ℂ] Lp V 2 μ) (A : V →L[ℂ] V) (h : G n)
    (hS : ∀ f : Mat n → V, Sob μ f → S (cls μ f) = cls μ (fun y => A (f (y * h.val)))) (g : C₀(ℝ, ℂ)) :
    S * F.Φ g = F.Φ g * S := by
  refine F.comm S (fun x => ?_) g
  obtain ⟨f, hf, hx⟩ := hrep x x.2
  obtain ⟨hOm, -, -, -, htr⟩ := hO n μ V hL hU hR f hf
  obtain ⟨hs1, hs2⟩ := htr h A
  have hxe : x = ⟨cls μ f, cls_mem μ hf⟩ := Subtype.ext hx.symm
  refine ⟨⟨_, cls_mem μ hs1⟩, ?_, ?_⟩
  · rw [← hx, hS f hf]
  · rw [hΩ _ _ hs1, hxe, hΩ _ _ hf, hS _ hOm]
    exact cls_congr hC hU hs2

theorem comm_rR (hC : ClsFacts) (hO : SobOps) (hL : LgFacts) (hU : Unimod) (hR : RCalc)
    (F : FCalc (Lp V 2 μ) (Msob μ V) Ω T) (hrep : ∀ x ∈ Msob μ V, ∃ f, Sob μ f ∧ cls μ f = x)
    (hΩ : ∀ (f : Mat n → V) (hf : cls μ f ∈ Msob μ V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp V 2 μ) = cls μ (Om f))
    (g : C₀(ℝ, ℂ)) (h : G n) : F.Φ g * rR μ V h = rR μ V h * F.Φ g :=
  (comm_of hC hO hL hU hR F hrep hΩ (rR μ V h) (ContinuousLinearMap.id ℂ V) h
    (fun _ hf => rR_cls hC hO hL hU hR hf h) g).symm

theorem pres (hC : ClsFacts) (hO : SobOps) (hL : LgFacts) (hU : Unimod) (hR : RCalc) (hSG : SobG) (hP : PresSob)
    (F : FCalc (Lp V 2 μ) (Msob μ V) Ω T) (hrep : ∀ x ∈ Msob μ V, ∃ f, Sob μ f ∧ cls μ f = x)
    (hΩ : ∀ (f : Mat n → V) (hf : cls μ f ∈ Msob μ V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp V 2 μ) = cls μ (Om f))
    (g : C₀(ℝ, ℂ)) {f : Mat n → V} (hf : Sob μ f) :
    ∃ f', Sob μ f' ∧ cls μ f' = F.Φ g (cls μ f) ∧ ∀ w, cls μ (Rw w f') = F.Φ g (cls μ (Rw w f)) :=
  hP n μ V (F.Φ g) hL hU hR hSG (comm_rR hC hO hL hU hR F hrep hΩ g) f hf

end Calc

end GlobalTheory.CompanionTheory.WaveFc.Asm

namespace GlobalTheory.CompanionTheory.WaveFc.Asm

variable {n : ℕ}

section Sec

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

def kk (k : Matrix.unitaryGroup (Fin n) ℂ) : G n := Unitary.toUnits k

theorem rho_inv_rho (E : KMod n) (k : Matrix.unitaryGroup (Fin n) ℂ) (v : E.V) : E.ρ k⁻¹ (E.ρ k v) = v := by
  have h : E.ρ k⁻¹ * E.ρ k = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  exact congrArg (fun L : E.V →L[ℂ] E.V => L v) h

theorem rho_rho_inv (E : KMod n) (k : Matrix.unitaryGroup (Fin n) ℂ) (v : E.V) : E.ρ k (E.ρ k⁻¹ v) = v := by
  have h : E.ρ k * E.ρ k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact congrArg (fun L : E.V →L[ℂ] E.V => L v) h

theorem sec_pres (E : KMod n) [CompleteSpace E.V] {Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V} {T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ}
    (hC : ClsFacts) (hO : SobOps) (hL : LgFacts) (hU : Unimod) (hR : RCalc)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (hrep : ∀ x ∈ Msob μ E.V, ∃ f, Sob μ f ∧ cls μ f = x)
    (hΩ : ∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f))
    (g : C₀(ℝ, ℂ)) {f f' : Mat n → E.V} (hf : Sob μ f) (hs : IsSec E f) (hf' : Sob μ f')
    (hcl : cls μ f' = F.Φ g (cls μ f)) : IsSec E f' := by
  intro y hy k
  let S : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ := ((E.ρ k).compLpL 2 μ).comp (rR μ E.V (kk k))
  have hS : ∀ f : Mat n → E.V, Sob μ f → S (cls μ f) = cls μ (fun y => E.ρ k (f (y * (kk k).val))) := by
    intro f hf
    show (E.ρ k).compLpL 2 μ (rR μ E.V (kk k) (cls μ f)) = _
    rw [rR_cls hC hO hL hU hR hf, (hC n μ E.V hU).2.2.2.2 _ _ (sob_memLp (sob_trans hO hL hU hR hf _))]
  have hsob : ∀ f : Mat n → E.V, Sob μ f → Sob μ (fun y => E.ρ k (f (y * (kk k).val))) := fun f hf =>
    ((hO n μ E.V hL hU hR f hf).2.2.2.2 (kk k) (E.ρ k)).1
  have hfix : S (cls μ f) = cls μ f := by
    refine (hS f hf).trans (cls_congr hC hU fun y hy => ?_)
    have : (kk k).val = k.1 := rfl
    rw [this, hs y hy k, rho_rho_inv]
  have hc := comm_of hC hO hL hU hR F hrep hΩ S (E.ρ k) (kk k) hS g
  have h2 : S (cls μ f') = cls μ f' := by
    rw [hcl]
    have := congrArg (fun L : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ => L (cls μ f)) hc
    simp only [ContinuousLinearMap.mul_apply] at this
    rw [this, hfix]
  have hu := cls_eq_of_sob hC hU (hsob f' hf') hf' ((hS f' hf').symm.trans h2) y hy
  have : (kk k).val = k.1 := rfl
  rw [this] at hu
  rw [← hu, rho_inv_rho]

end Sec

section Bop

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Bop (f : Mat n → V) : Mat n → V := f + Om (Om f)

def Bn (f : Mat n → V) (N : ℕ) : Mat n → V := Nat.rec f (fun _ g => Bop g) N

theorem cpt_add {f f' : Mat n → V} (h : Cpt f) (h' : Cpt f') : Cpt (f + f') := by
  obtain ⟨R, hR⟩ := h
  obtain ⟨R', hR'⟩ := h'
  refine ⟨max R R', fun y hy hl => ?_⟩
  rw [Pi.add_apply, hR y hy (lt_of_le_of_lt (le_max_left _ _) hl), hR' y hy (lt_of_le_of_lt (le_max_right _ _) hl),
    add_zero]

end Bop

theorem CE_add (E : KMod n) {f f' : Mat n → E.V} (h : f ∈ CE E) (h' : f' ∈ CE E) : f + f' ∈ CE E :=
  ⟨h.1.add h'.1, fun g hg k => by rw [Pi.add_apply, Pi.add_apply, h.2 g hg k, h'.2 g hg k, map_add]⟩

theorem CE_smul (E : KMod n) (a : ℂ) {f : Mat n → E.V} (h : f ∈ CE E) : a • f ∈ CE E :=
  ⟨h.1.const_smul a, fun g hg k => by rw [Pi.smul_apply, Pi.smul_apply, h.2 g hg k, map_smul]⟩

theorem CE_Om (hR : RCalc) (E : KMod n) {f : Mat n → E.V} (h : f ∈ CE E) : Om f ∈ CE E :=
  CE_smul E 2 (CE_add E ((hR n).2.1 E f h true 2) ((hR n).2.1 E f h false 2))

theorem Bn_props [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (hL : LgFacts) (hR : RCalc) (hCp : CptSob) (E : KMod n) {f : Mat n → E.V} (hf : f ∈ CE E) (hc : Cpt f) (N : ℕ) :
    Bn f N ∈ CE E ∧ Cpt (Bn f N) := by
  induction N with
  | zero => exact ⟨hf, hc⟩
  | succ N ih =>
    have h1 := CE_Om hR E ih.1
    have c1 := (hCp n μ E.V hL hR _ ih.1.1 ih.2).2
    have c2 := (hCp n μ E.V hL hR _ h1.1 c1).2
    exact ⟨CE_add E ih.1 (CE_Om hR E h1), cpt_add ih.2 c2⟩

section Fn

theorem coe_toC0 {f : ℝ → ℂ} (h : Continuous f ∧ Tendsto f (cocompact ℝ) (𝓝 0)) : ⇑(toC0 f) = f := by
  unfold toC0
  rw [dif_pos h]
  rfl

def rf (y : ℝ) : ℂ := (((1 + y ^ 2)⁻¹ : ℝ) : ℂ)

theorem resolvent_function_vanishes_at_infinity : Continuous rf ∧ Tendsto rf (cocompact ℝ) (𝓝 0) := by
  have hpos : ∀ y : ℝ, 1 + y ^ 2 ≠ 0 := fun y => by positivity
  refine ⟨?_, ?_⟩
  · unfold rf
    exact Complex.continuous_ofReal.comp (Continuous.inv₀ (by fun_prop) hpos)
  · have h1 : Tendsto (fun y : ℝ => ‖y‖) (cocompact ℝ) atTop := tendsto_norm_cocompact_atTop
    have h2 : Tendsto (fun y : ℝ => 1 + y ^ 2) (cocompact ℝ) atTop := by
      have h3 : Tendsto (fun y : ℝ => ‖y‖ ^ 2) (cocompact ℝ) atTop :=
        (tendsto_pow_atTop (by norm_num)).comp h1
      refine tendsto_atTop_mono (fun y => ?_) h3
      rw [Real.norm_eq_abs, sq_abs]
      linarith
    have h4 := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero.comp h2)
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from Complex.ofReal_zero.symm]
    exact h4

end Fn

section Steps

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {Ω : Msob μ V →ₗ[ℂ] Msob μ V} {T : Lp V 2 μ →L[ℂ] Lp V 2 μ}

theorem T_B (hC : ClsFacts) (hO : SobOps) (hL : LgFacts) (hU : Unimod) (hR : RCalc)
    (hΩ : ∀ (f : Mat n → V) (hf : cls μ f ∈ Msob μ V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp V 2 μ) = cls μ (Om f))
    (hT : ∀ x : Msob μ V, T ((x : Lp V 2 μ) + (Ω (Ω x) : Lp V 2 μ)) = x) {g : Mat n → V} (hg : Sob μ g) :
    T (cls μ (Bop g)) = cls μ g := by
  have hOm := (hO n μ V hL hU hR g hg).1
  have hOOm := (hO n μ V hL hU hR _ hOm).1
  have e1 : Ω ⟨cls μ g, cls_mem μ hg⟩ = ⟨cls μ (Om g), cls_mem μ hOm⟩ := Subtype.ext (hΩ _ _ hg)
  have e2 : (Ω (Ω ⟨cls μ g, cls_mem μ hg⟩) : Lp V 2 μ) = cls μ (Om (Om g)) := by
    rw [e1]
    exact hΩ _ _ hOm
  have e3 : cls μ (Bop g) = cls μ g + cls μ (Om (Om g)) := by
    have := (hC n μ V hU).2.1 1 g (Om (Om g)) (sob_memLp hg) (sob_memLp hOOm)
    simpa [Bop] using this
  rw [e3, ← e2]
  exact hT ⟨_, _⟩

theorem wv_step (hW : WvAlg) (F : FCalc (Lp V 2 μ) (Msob μ V) Ω T) {c : ℝ} {N j : ℕ} {t : ℝ}
    (h1 : Continuous (wv c N j t) ∧ Tendsto (wv c N j t) (cocompact ℝ) (𝓝 0))
    (h2 : Continuous (wv c (N + 1) j t) ∧ Tendsto (wv c (N + 1) j t) (cocompact ℝ) (𝓝 0)) :
    F.Φ (toC0 (wv c (N + 1) j t)) = F.Φ (toC0 (wv c N j t)) * T := by
  have e : toC0 (wv c (N + 1) j t) = toC0 (wv c N j t) * toC0 rf := by
    ext y
    rw [ZeroAtInftyContinuousMap.coe_mul, Pi.mul_apply, coe_toC0 h1, coe_toC0 h2, coe_toC0 resolvent_function_vanishes_at_infinity,
      (hW c N t y).2.2.2 j, rf, mul_comm]
  rw [e, F.map_mul, F.res (toC0 rf) (fun y => by rw [coe_toC0 resolvent_function_vanishes_at_infinity]; rfl)]

theorem curve_deriv (hFc : Fcurve) (F : FCalc (Lp V 2 μ) (Msob μ V) Ω T) (c : ℝ) {N j : ℕ} (hj : j + 2 ≤ 4 * N) (t : ℝ)
    (x : Lp V 2 μ) :
    HasDerivAt (fun s => F.Φ (toC0 (wv c N j s)) x) (F.Φ (toC0 (wv c N (j + 1) t)) x) t := by
  have h := (hFc c N j hj t).2
  let L : C₀(ℝ, ℂ) →L[ℂ] Lp V 2 μ := (ContinuousLinearMap.apply ℂ (Lp V 2 μ) x).comp F.Φ
  exact (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h

end Steps

end GlobalTheory.CompanionTheory.WaveFc.Asm

namespace GlobalTheory.CompanionTheory.WaveFc.Asm

variable {n : ℕ}

section Main

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

theorem cls_zero {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] : cls μ (0 : Mat n → V) = 0 := by
  have h : MemLp (fun y : G n => (0 : Mat n → V) y.val) 2 μ := MemLp.zero
  unfold cls
  rw [dif_pos h]
  exact MemLp.toLp_zero h

theorem cut_eq_one {c y : ℝ} (h : y ≤ c) : cut c y = 1 := by
  unfold cut
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem core (E : KMod n) [CompleteSpace E.V] {Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V} {T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ}
    (hL : LgFacts) (hU : Unimod) (hR : RCalc) (hSG : SobG)
    (hAC : AbsCut) (hFc : Fcurve) (hW : WvAlg) (hC : ClsFacts) (hO : SobOps) (hCp : CptSob) (hP : PresSob)
    (hCJ : CurveJoint)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (hrep : ∀ x ∈ Msob μ E.V, ∃ f, Sob μ f ∧ cls μ f = x)
    (hΩ : ∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f))
    (hT : ∀ x : Msob μ E.V, T ((x : Lp E.V 2 μ) + (Ω (Ω x) : Lp E.V 2 μ)) = x) (c : ℝ)
    (hc : ∀ f : Mat n → E.V, Sob μ f → IsSec E f → (⟪cls μ (Om f), cls μ f⟫_ℂ).re ≤ c * ‖cls μ f‖ ^ 2)
    {f : Mat n → E.V} (hf : f ∈ CE E) (hcf : Cpt f) :
    ∃ u, IsWave E u ∧ ∀ g ∈ GLs n, u 0 g = f g := by
  have hbp := fun N => Bn_props μ hL hR hCp E hf hcf N
  have hbS : ∀ N, Sob μ (Bn f N) := fun N => (hCp n μ E.V hL hR _ (hbp N).1.1 (hbp N).2).1
  have hbE : ∀ N, IsSec E (Bn f N) := fun N => (hbp N).1.2
  have hC0 : ∀ N j t, j + 2 ≤ 4 * N → (Continuous (wv c N j t) ∧ Tendsto (wv c N j t) (cocompact ℝ) (𝓝 0)) :=
    fun N j t hj => (hFc c N j hj t).1
  have hstep : ∀ N j t, j + 2 ≤ 4 * N →
      F.Φ (toC0 (wv c (N + 1) j t)) (cls μ (Bn f (N + 1))) = F.Φ (toC0 (wv c N j t)) (cls μ (Bn f N)) := by
    intro N j t hj
    rw [wv_step hW F (hC0 N j t hj) (hC0 (N + 1) j t (by omega)), ContinuousLinearMap.mul_apply]
    exact congrArg _ (T_B hC hO hL hU hR hΩ hT (hbS N))
  have hpres := fun g (N : ℕ) => pres hC hO hL hU hR hSG hP F hrep hΩ g (hbS N)
  have hex : ∀ (j : ℕ) (t : ℝ), ∃ u, Sob μ u ∧ IsSec E u ∧
      cls μ u = F.Φ (toC0 (wv c (j + 2) j t)) (cls μ (Bn f (j + 2))) ∧
      ∀ w, cls μ (Rw w u) = F.Φ (toC0 (wv c (j + 2) j t)) (cls μ (Rw w (Bn f (j + 2)))) := by
    intro j t
    obtain ⟨u, h1, h2, h3⟩ := hpres (toC0 (wv c (j + 2) j t)) (j + 2)
    exact ⟨u, h1, sec_pres E hC hO hL hU hR F hrep hΩ _ (hbS _) (hbE _) h1 h2, h2, h3⟩
  choose U hUS hUE hUc hUw using hex
  have hd : ∀ j w t, HasDerivAt (fun s => cls μ (Rw w (U j s))) (cls μ (Rw w (U (j + 1) t))) t := by
    intro j w t
    have e : (fun s => cls μ (Rw w (U j s))) =
        fun s => F.Φ (toC0 (wv c (j + 2) j s)) (cls μ (Rw w (Bn f (j + 2)))) := funext fun s => hUw j s w
    rw [e]
    have hd := curve_deriv hFc F c (N := j + 2) (j := j) (by omega) t (cls μ (Rw w (Bn f (j + 2))))
    obtain ⟨f'', hf'', hc'', hw''⟩ := hpres (toC0 (wv c (j + 2) (j + 1) t)) (j + 2)
    have e2 : cls μ (Rw w (U (j + 1) t)) = F.Φ (toC0 (wv c (j + 2) (j + 1) t)) (cls μ (Rw w (Bn f (j + 2)))) := by
      rw [← hw'' w]
      refine cls_congr hC hU (Rw_congr w (cls_eq_of_sob hC hU (hUS (j + 1) t) hf'' ?_))
      rw [hUc, hc'']
      exact hstep (j + 2) (j + 1) t (by omega)
    rw [e2]
    exact hd
  obtain ⟨hjoint, hder⟩ := hCJ n μ E.V U hL hR hSG hUS hd
  refine ⟨U 0, ⟨hjoint, fun t => ⟨(hUS 0 t).1, hUE 0 t⟩, ?_, ?_⟩, ?_⟩
  · intro t g hg
    have d1 : deriv (fun s => U 0 s g) = fun s => U 1 s g := funext fun s => (hder 0 s g hg).deriv
    have d2 : iteratedDeriv 2 (fun s => U 0 s g) t = U 2 t g := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, d1]
      exact (hder 1 t g hg).deriv
    rw [d2]
    have hOmS := (hO n μ E.V hL hU hR _ (hUS 0 t)).1
    have h0 : cls μ (U 0 t) = F.Φ (toC0 (wv c 4 0 t)) (cls μ (Bn f 4)) := by
      rw [hUc, hstep 3 0 t (by omega), hstep 2 0 t (by omega)]
    have hom := F.omega (toC0 (wv c 4 0 t)) (toC0 (wv c 4 2 t))
      (fun y => by
        rw [coe_toC0 (hC0 4 0 t (by omega)), coe_toC0 (hC0 4 2 t (by omega))]
        exact (hW c 4 t y).1)
      (cls μ (Bn f 4)) ⟨cls μ (U 0 t), cls_mem μ (hUS 0 t)⟩ h0
    rw [hΩ _ _ (hUS 0 t)] at hom
    exact cls_eq_of_sob hC hU (hUS 2 t) hOmS ((hUc 2 t).trans hom.symm) g hg
  · intro g hg
    rw [(hder 0 0 g hg).deriv]
    have hz : toC0 (wv c 3 1 0) = 0 := by
      ext y
      rw [coe_toC0 (hC0 3 1 0 (by omega))]
      exact (hW c 3 0 y).2.1
    have h1 : cls μ (U 1 0) = cls μ (0 : Mat n → E.V) := by
      rw [hUc, cls_zero]
      show F.Φ (toC0 (wv c 3 1 0)) _ = 0
      rw [hz, map_zero]
      rfl
    exact (hC n μ E.V hU).1 _ 0 (sob_cont (hUS 1 0)) continuousOn_const (sob_memLp (hUS 1 0)) MemLp.zero h1 g hg
  · have hcut : F.Φ (toC0 rf * toC0 rf - toC0 (wv c 2 0 0)) (cls μ (Bn f 2)) = 0 := by
      refine hAC (Lp E.V 2 μ) (Msob μ E.V) Ω T F c _ (fun g => ?_) _ (fun y hy => ?_)
      · obtain ⟨u, h1, h2, -⟩ := hpres g 2
        refine ⟨⟨cls μ u, cls_mem μ h1⟩, h2, ?_⟩
        rw [hΩ _ _ h1]
        exact hc u h1 (sec_pres E hC hO hL hU hR F hrep hΩ _ (hbS _) (hbE _) h1 h2)
      · have e1 := (hW c 2 0 y).2.2.1
        rw [cut_eq_one hy] at e1
        have e2 : (toC0 rf * toC0 rf - toC0 (wv c 2 0 0)) y = rf y * rf y - wv c 2 0 0 y := by
          rw [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.mul_apply, coe_toC0 resolvent_function_vanishes_at_infinity,
            coe_toC0 (hC0 2 0 0 (by omega))]
        rw [e2, e1, rf, ← Complex.ofReal_mul, sub_eq_zero]
        congr 1
        rw [one_mul, pow_two (1 + y ^ 2), mul_inv]
    have hr : F.Φ (toC0 rf * toC0 rf) (cls μ (Bn f 2)) = cls μ f := by
      rw [F.map_mul, F.res (toC0 rf) (fun y => by rw [coe_toC0 resolvent_function_vanishes_at_infinity]; rfl), ContinuousLinearMap.mul_apply]
      have a1 : T (cls μ (Bn f 2)) = cls μ (Bn f 1) := T_B hC hO hL hU hR hΩ hT (hbS 1)
      have a2 : T (cls μ (Bn f 1)) = cls μ (Bn f 0) := T_B hC hO hL hU hR hΩ hT (hbS 0)
      rw [a1, a2]
      rfl
    have hw : F.Φ (toC0 (wv c 2 0 0)) (cls μ (Bn f 2)) = cls μ f := by
      rw [map_sub, ContinuousLinearMap.sub_apply, hr, sub_eq_zero] at hcut
      exact hcut.symm
    exact cls_eq_of_sob hC hU (hUS 0 0) (hbS 0) ((hUc 0 0).trans hw)

end Main

theorem asm1 : Asm1 := by
  intro hFC hAC hFc hW hC hO hCp hSB hP hCT hCJ hFr hOF hIbp hD hL hU hR hSG n E f hf hcf
  letI : MeasurableSpace (G n) := borel _
  haveI : BorelSpace (G n) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (G n) := inferInstanceAs (LocallyCompactSpace (Mat n)ˣ)
  let μ : Measure (G n) := Measure.haar
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨c, hc⟩ := hSB n μ E hL hU hR
  obtain ⟨hrep, Ω, T, hden, hsym, hinv, hT, hΩ⟩ := hCT n μ E.V hL hU hR hSG hP hFr hC hO hCp hOF hIbp hD
  obtain ⟨F⟩ := hFC (Lp E.V 2 μ) (Msob μ E.V) Ω T hden hsym hinv hT
  exact core E hL hU hR hSG hAC hFc hW hC hO hCp hP hCJ F hrep hΩ hT c hc hf hcf

end GlobalTheory.CompanionTheory.WaveFc.Asm
