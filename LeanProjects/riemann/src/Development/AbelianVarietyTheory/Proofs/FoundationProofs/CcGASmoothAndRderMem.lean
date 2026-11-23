import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff

open Set Filter GlobalTheory.AdelicU NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology ComplexConjugate ContDiff Matrix

noncomputable section

namespace GlobalTheory.Orb

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def IsSmoothRealFam (u : P → GAd σ J) : Prop :=
  (∀ t, projFin σ J (u t) = 1) ∧
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) i j, ContDiff ℝ ∞ fun t => archMat σ J τ (projArch σ J w (u t)) i j

omit [NumberField E] in

theorem isSmoothRealFam_one : IsSmoothRealFam fun _ : P => (1 : GAd σ J) :=
  ⟨fun _ => map_one _, fun _ _ _ _ => contDiff_const⟩

omit [NumberField E] in

theorem IsSmoothRealFam.mul {u v : P → GAd σ J} (hu : IsSmoothRealFam u) (hv : IsSmoothRealFam v) :
    IsSmoothRealFam fun t => u t * v t := by
  refine ⟨fun t => by rw [map_mul, hu.1, hv.1, one_mul], fun w τ i j => ?_⟩
  simp only [map_mul, Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (hu.2 w τ i k).mul (hv.2 w τ k j)

omit [NumberField E] in

theorem IsSmoothRealFam.comp {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] {u : P → GAd σ J}
    (hu : IsSmoothRealFam u) {p : Q → P} (hp : ContDiff ℝ ∞ p) : IsSmoothRealFam fun t => u (p t) :=
  ⟨fun _ => hu.1 _, fun w τ i j => (hu.2 w τ i j).comp hp⟩

omit [NumberField E] in

theorem isSmoothRealFam_prod {k : ℕ} {u : Fin k → P → GAd σ J} (hu : ∀ i, IsSmoothRealFam (u i)) :
    IsSmoothRealFam fun t => (List.ofFn fun i => u i t).prod := by
  induction k with
  | zero => simpa using isSmoothRealFam_one
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (hu 0).mul (ih fun i => hu i.succ)

omit [NumberField E] in

theorem infCoord_mul (x : GInf σ J) (y : GAd σ J) : infCoord σ J (x * projInf σ J y) =
    fun w τ i j => ∑ k, infCoord σ J x w τ i k * archMat σ J τ (projArch σ J w y) k j := by
  funext w τ i j
  simp only [infCoord, archCoord, matCoord, map_mul, Matrix.mul_apply, projInfArch_projInf]

theorem IsSmoothRealFam.contDiff {u : P → GAd σ J} (hu : IsSmoothRealFam u) {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J)
    (g : GAd σ J) : ContDiff ℝ ∞ fun t => f (g * u t) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ⟨-, Φ, hΦ, e⟩, b, -, rfl⟩ := hf
    simp only [infFin, map_mul, hu.1, mul_one, e, infCoord_mul]
    refine (hΦ.comp (contDiff_pi.2 fun w => contDiff_pi.2 fun τ => contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
      ContDiff.sum fun k _ => contDiff_const.mul (hu.2 w τ k j))).mul contDiff_const
  | zero => exact contDiff_const
  | add f f' _ _ h h' => exact h.add h'
  | smul a f _ h => exact h.const_smul a

theorem IsSmoothRealFam.deriv_mem_ccInf {u : ℝ → GAd σ J} (hu : IsSmoothRealFam u) (hc : Continuous u)
    (h0 : u 0 = 1) {a : GInf σ J → ℂ} (ha : a ∈ CcInf σ J) :
    (fun x => deriv (fun t => a (x * projInf σ J (u t))) 0) ∈ CcInf σ J := by
  obtain ⟨hs, Φ, hΦ, e⟩ := ha
  refine ⟨.intro hs fun x hx => ?_, fun y => fderiv ℝ Φ y fun w τ i j =>
    ∑ k, y w τ i k * deriv (fun t => archMat σ J τ (projArch σ J w (u t)) k j) 0, ?_, fun x => ?_⟩
  · have h1 : Tendsto (fun t => x * projInf σ J (u t)) (𝓝 0) (𝓝 x) := by
      simpa [h0] using (continuous_const.mul ((continuous_projInf σ J).comp hc)).tendsto (f := fun t => x * projInf σ J (u t)) 0
    rw [EventuallyEq.deriv_eq (f := fun _ => (0 : ℂ)) (h1.eventually (notMem_tsupport_iff_eventuallyEq.1 hx)),
      deriv_const]
  · refine (hΦ.fderiv_right (m := ∞) le_rfl).clm_apply ?_
    exact contDiff_pi.2 fun w => contDiff_pi.2 fun τ => contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
      ContDiff.sum fun k _ => (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_id w) τ) i) k).mul
        contDiff_const
  · have h1 : HasDerivAt (fun t => infCoord σ J (x * projInf σ J (u t))) (fun w τ i j =>
        ∑ k, infCoord σ J x w τ i k * deriv (fun t => archMat σ J τ (projArch σ J w (u t)) k j) 0) 0 := by
      simp only [infCoord_mul]
      exact hasDerivAt_pi.2 fun w => hasDerivAt_pi.2 fun τ => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j =>
        HasDerivAt.fun_sum fun k _ => ((hu.2 w τ k j).differentiable (by simp) 0).hasDerivAt.const_mul _
    have h2 := (hΦ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0 h1
    simp only [h0, map_one, mul_one] at h2
    simp only [e]
    exact h2.deriv

theorem IsSmoothRealFam.deriv_mem_ccAd {u : ℝ → GAd σ J} (hu : IsSmoothRealFam u) (hc : Continuous u)
    (h0 : u 0 = 1) {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    (fun g => deriv (fun t => f (g * u t)) 0) ∈ CcAd σ J := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hf
    convert infFin_mem_ccAd (hu.deriv_mem_ccInf hc h0 ha) hb using 1
    funext g
    simp only [infFin, map_mul, hu.1, mul_one, deriv_mul_const_field]
  | zero =>
    simp only [Pi.zero_apply, deriv_const]
    exact (CcAd σ J).zero_mem
  | add f f' hf hf' h h' =>
    convert (CcAd σ J).add_mem h h' using 1
    funext g
    exact deriv_fun_add ((hu.contDiff hf g).differentiable (by simp) 0) ((hu.contDiff hf' g).differentiable (by simp) 0)
  | smul c f _ h =>
    convert (CcAd σ J).smul_mem c h using 1
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, deriv_const_mul_field]

theorem isSmoothRealFam_embArch (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {x : P → GArch σ J w}
    (hx : ∀ i j, ContDiff ℝ ∞ fun t => archMat σ J τ (x t) i j) :
    IsSmoothRealFam (fun t => embArch σ J w (x t)) ∧ Continuous fun t => embArch σ J w (x t) := by
  refine ⟨⟨fun t => projFin_embArch σ J w _, fun w' τ' i j => ?_⟩, (continuous_embArch σ J w).comp
    ((isEmbedding_archMat J h τ).continuous_iff.2 (continuous_pi fun i => continuous_pi fun j => (hx i j).continuous))⟩
  by_cases e : w' = w
  · subst e
    simp only [projArch_embArch_self]
    rcases infEmb_eq_or_conj h τ τ' with e | e
    · simpa only [archMat_apply, e] using hx i j
    · simp only [archMat_apply, e]
      exact Complex.conjCLE.contDiff.comp (hx i j)
  · simp only [projArch_embArch_ne σ J e]
    exact contDiff_const

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_exp_smul_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • X) : Matrix (Fin n) (Fin n) ℂ) i j := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
    contDiff_iff_contDiffAt.2 fun A => (NormedSpace.exp_analytic (𝕂 := ℝ) A).contDiffAt
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).contDiff.comp
    (h.comp (contDiff_id.smul contDiff_const))

end

end General

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem isSmoothRealFam_oneP (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) :
    IsSmoothRealFam (oneP θ V τ X) ∧ Continuous (oneP θ V τ X) ∧ oneP θ V τ X 0 = 1 := by
  choose x hx using fun t : ℝ => exists_archEquiv_eq V (embOverOf D τ) rfl
    (GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX t)
  have e : oneP θ V τ X = fun t => embArch _ _ _ (x t) := funext fun t => by
    rw [oneP, ← hx, atTau_archEquiv hθ V _ rfl]
  have h := isSmoothRealFam_embArch (isCMExt_host D) (embOverOf D τ) (x := x) fun i j => by
    simp only [archMat_eq_archEquiv _ (isCMExt_host D), hx]
    exact contDiff_exp_smul_entry X i j
  refine ⟨e ▸ h.1, e ▸ h.2, ?_⟩
  have h1 := atTau_archEquiv hθ V (embOverOf D τ) rfl 1
  rw [map_one, map_one] at h1
  rw [oneP, zero_smul, NormedSpace.exp_zero]
  exact h1

theorem ccGA_smooth_and_Rder_mem (D : D7) (V : HSp D)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (f : GA D V → ℂ)
    (hf : f ∈ CcGA V) :
    (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) ∧
    ∀ τ, ∀ X ∈ lieAt V τ, Rder θ V τ X f ∈ CcGA V :=
  ⟨fun _ _ _ hX g => (isSmoothRealFam_prod fun i => (isSmoothRealFam_oneP hθ (hX i)).1.comp
      (contDiff_apply ℝ ℝ i)).contDiff hf g,
    fun _ _ hX => have h := isSmoothRealFam_oneP hθ hX; h.1.deriv_mem_ccAd h.2.1 h.2.2 hf⟩

end Record

end GlobalTheory.Orb
