import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Adapted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbLEqEmbOptL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryStabiliserEmbeddingNormLaws
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DKerHasCompactSupport

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLip

theorem integral_translate_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (f D : G → ℂ) (γ : ℝ → G) (h0 : γ 0 = 1) (hD : Integrable D μ)
    (hc : Continuous fun p : ℝ × G => D (γ p.1 * p.2))
    (hd : ∀ h t, HasDerivAt (fun t => f (γ t * h)) (D (γ t * h)) t) (s : ℝ) :
    ∫ h, ‖f (γ s * h) - f h‖ ∂μ ≤ |s| * ∫ h, ‖D h‖ ∂μ := by
  have hmeas : Measurable fun p : G × ℝ => ‖D (γ p.2 * p.1)‖ₑ :=
    (hc.comp (continuous_snd.prodMk continuous_fst)).measurable.enorm
  have hpt : ∀ h, ‖f (γ s * h) - f h‖ₑ ≤ ∫⁻ t in Set.uIoc (0:ℝ) s, ‖D (γ t * h)‖ₑ := by
    intro h
    have hcont : Continuous fun t => D (γ t * h) := hc.comp (continuous_id.prodMk continuous_const)
    have hF : ∫ t in (0:ℝ)..s, D (γ t * h) = f (γ s * h) - f (γ 0 * h) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd h t) (hcont.intervalIntegrable 0 s)
    rw [h0, one_mul] at hF
    rw [← hF, ← ofReal_norm_eq_enorm, intervalIntegral.norm_integral_eq_norm_integral_uIoc, ofReal_norm_eq_enorm]
    exact enorm_integral_le_lintegral_enorm _
  have hswap : ∫⁻ h, (∫⁻ t in Set.uIoc (0:ℝ) s, ‖D (γ t * h)‖ₑ) ∂μ =
      ∫⁻ t in Set.uIoc (0:ℝ) s, ∫⁻ h, ‖D (γ t * h)‖ₑ ∂μ :=
    lintegral_lintegral_swap hmeas.aemeasurable
  have hvol : volume (Set.uIoc (0:ℝ) s) = ENNReal.ofReal |s| := by
    rw [Set.uIoc, Real.volume_Ioc]
    congr 1
    rcases le_total 0 s with hs | hs <;> simp [hs, abs_of_nonneg, abs_of_nonpos]
  have hinv : ∀ t, ∫⁻ h, ‖D (γ t * h)‖ₑ ∂μ = ∫⁻ h, ‖D h‖ₑ ∂μ := fun t =>
    lintegral_mul_left_eq_self (fun h => ‖D h‖ₑ) (γ t)
  have hDfin : ∫⁻ h, ‖D h‖ₑ ∂μ ≠ ⊤ := ne_of_lt hD.2
  by_cases hI : Integrable (fun h => ‖f (γ s * h) - f h‖) μ
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hI.aestronglyMeasurable, integral_norm_eq_lintegral_enorm hD.aestronglyMeasurable,
      ← ENNReal.toReal_ofReal (abs_nonneg s), ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDfin) ?_
    calc ∫⁻ h, ENNReal.ofReal ‖f (γ s * h) - f h‖ ∂μ = ∫⁻ h, ‖f (γ s * h) - f h‖ₑ ∂μ := by
          simp only [ofReal_norm_eq_enorm]
      _ ≤ ∫⁻ h, (∫⁻ t in Set.uIoc (0:ℝ) s, ‖D (γ t * h)‖ₑ) ∂μ := lintegral_mono hpt
      _ = ENNReal.ofReal |s| * ∫⁻ h, ‖D h‖ₑ ∂μ := by
          rw [hswap]
          simp only [hinv]
          rw [setLIntegral_const, hvol, mul_comm]
  · rw [integral_undef hI]
    exact mul_nonneg (abs_nonneg _) (integral_nonneg fun _ => norm_nonneg _)

private theorem jm_sq_lemma {k : ℕ} (δ : Fin k → Bool) : Formalism.REAL.Jm δ * Formalism.REAL.Jm δ = 1 := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem exp_preserves_Jm_of_skew {k : ℕ} (δ : Fin k → Bool) (A : Matrix (Fin k) (Fin k) ℂ)
    (hA : Aᴴ * Formalism.REAL.Jm δ + Formalism.REAL.Jm δ * A = 0) :
    (NormedSpace.exp A)ᴴ * Formalism.REAL.Jm δ * NormedSpace.exp A = Formalism.REAL.Jm δ := by
  set J := Formalism.REAL.Jm δ with hJdef
  have hJ : J * J = 1 := jm_sq_lemma δ
  have hJi : J⁻¹ = J := Matrix.inv_eq_left_inv hJ
  have hJu : IsUnit J := ⟨⟨J, J, hJ, hJ⟩, rfl⟩
  have hAc : Aᴴ = J * (-A) * J⁻¹ := by
    rw [hJi]
    calc Aᴴ = Aᴴ * (J * J) := by rw [hJ, mul_one]
      _ = (Aᴴ * J + J * A) * J - J * A * J := by noncomm_ring
      _ = J * (-A) * J := by rw [hA]; noncomm_ring
  have h2 : NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, hAc, Matrix.exp_conj _ _ hJu, hJi]
  calc J * NormedSpace.exp (-A) * J * J * NormedSpace.exp A
      = J * (NormedSpace.exp (-A) * (J * J) * NormedSpace.exp A) := by simp only [mul_assoc]
    _ = J := by rw [hJ, mul_one, h2, mul_one]

section Rep

open Formalism.MainNotions.S GlobalTheory.Ell

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exp_mem' {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ lieOf (Formalism.REAL.Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • Y) ∈ UJset ε := by
  have hY0 : Yᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y = 0 := hY
  show (NormedSpace.exp (t • Y))ᴴ * Formalism.REAL.Jm ε * NormedSpace.exp (t • Y) = Formalism.REAL.Jm ε
  apply exp_preserves_Jm_of_skew
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hY0, smul_zero]

theorem rep_mul' (hπ : IsURepOn (UJset ε) π) {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hg' : g' ∈ UJset ε)
    (w : H) : π (g * g') w = π g (π g' w) := by
  obtain ⟨⟨-, hm⟩, -, -⟩ := id hπ
  rw [hm g hg g' hg', ContinuousLinearMap.comp_apply]

theorem exp_add' (Y : Matrix (Fin n) (Fin n) ℂ) (a b : ℝ) :
    NormedSpace.exp ((a + b) • Y) = NormedSpace.exp (a • Y) * NormedSpace.exp (b • Y) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left a).smul_right b)

theorem inner_exp (hπ : IsURepOn (UJset ε) π) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ lieOf (Formalism.REAL.Jm ε)) (t : ℝ)
    (u w : H) : ⟪u, π (NormedSpace.exp (t • Y)) w⟫_ℂ = ⟪π (NormedSpace.exp ((-t) • Y)) u, w⟫_ℂ := by
  obtain ⟨⟨hone, -⟩, hiso, -⟩ := id hπ
  have hm1 : NormedSpace.exp ((-t) • Y) * NormedSpace.exp (t • Y) = 1 := by
    rw [← exp_add', neg_add_cancel, zero_smul, NormedSpace.exp_zero]
  have hw : π (NormedSpace.exp ((-t) • Y)) (π (NormedSpace.exp (t • Y)) w) = w := by
    rw [← rep_mul' hπ (exp_mem' hY (-t)) (exp_mem' hY t), hm1, hone]
    rfl
  let T : H →ₗᵢ[ℂ] H :=
    { toLinearMap := (π (NormedSpace.exp ((-t) • Y)) : H →ₗ[ℂ] H)
      norm_map' := hiso _ (exp_mem' hY (-t)) }
  have key := T.inner_map_map u (π (NormedSpace.exp (t • Y)) w)
  change ⟪π (NormedSpace.exp ((-t) • Y)) u, π (NormedSpace.exp ((-t) • Y)) (π (NormedSpace.exp (t • Y)) w)⟫_ℂ
    = _ at key
  rw [hw] at key
  exact key.symm

theorem hasDerivAt_coef (hπ : IsURepOn (UJset ε) π) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ lieOf (Formalism.REAL.Jm ε))
    {v : H} (hv : SmV (lieOf (Formalism.REAL.Jm ε)) π v) (w : H) (t : ℝ) :
    HasDerivAt (fun r : ℝ => ⟪v, π (NormedSpace.exp (r • Y)) w⟫_ℂ)
      (-⟪dR π Y v, π (NormedSpace.exp (t • Y)) w⟫_ℂ) t := by
  have hsm := hv 1 ![Y] (fun i => by rw [Fin.fin_one_eq_zero i]; exact hY)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => π (NormedSpace.exp (s • Y)) v) := by
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (fun _ : Fin 1 => s)) := contDiff_pi.2 fun _ => contDiff_id
    convert hsm.comp hc using 1
    funext s
    simp [List.ofFn_succ]
  have hdiff : Differentiable ℝ (fun s : ℝ => π (NormedSpace.exp (s • Y)) v) := hφ.differentiable (by simp)
  have hd0 : HasDerivAt (fun s : ℝ => π (NormedSpace.exp (s • Y)) v) (dR π Y v) 0 := (hdiff 0).hasDerivAt
  have hφs : ∀ s : ℝ, HasDerivAt (fun s : ℝ => π (NormedSpace.exp (s • Y)) v)
      (π (NormedSpace.exp (s • Y)) (dR π Y v)) s := by
    intro s
    have ha : HasDerivAt (fun r : ℝ => π (NormedSpace.exp (s • Y)) (π (NormedSpace.exp (r • Y)) v))
        (π (NormedSpace.exp (s • Y)) (dR π Y v)) (s - s) := by
      rw [sub_self]
      exact (((π (NormedSpace.exp (s • Y))).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt 0 hd0
    refine (ha.comp_sub_const s s).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    show π (NormedSpace.exp (x • Y)) v = π (NormedSpace.exp (s • Y)) (π (NormedSpace.exp ((x - s) • Y)) v)
    rw [← rep_mul' hπ (exp_mem' hY s) (exp_mem' hY (x - s)), ← exp_add', add_sub_cancel]
  have hneg : HasDerivAt (fun r : ℝ => π (NormedSpace.exp ((-r) • Y)) v)
      (-(π (NormedSpace.exp ((-t) • Y)) (dR π Y v))) t := by
    have := (hφs (-t)).scomp t (hasDerivAt_neg t)
    simpa [Function.comp_def] using this
  have hin := hneg.inner ℂ (hasDerivAt_const t w)
  have hfun : (fun r : ℝ => ⟪v, π (NormedSpace.exp (r • Y)) w⟫_ℂ) =
      fun r => ⟪π (NormedSpace.exp ((-r) • Y)) v, w⟫_ℂ := funext fun r => inner_exp hπ hY r v w
  rw [hfun]
  refine hin.congr_deriv ?_
  rw [inner_exp hπ hY t (dR π Y v) w]
  simp

end Rep

theorem hsn_smul {m : ℕ} (a : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) : GlobalTheory.SepReal.hsn (a • X) = |a| * GlobalTheory.SepReal.hsn X := by
  unfold GlobalTheory.SepReal.hsn
  have hent : ∀ i j, ‖(a • X) i j‖ ^ 2 = a ^ 2 * ‖X i j‖ ^ 2 := fun i j => by
    rw [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp_rw [hent, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem eq_zero_of_hsn {m : ℕ} {X : Matrix (Fin m) (Fin m) ℂ} (h : GlobalTheory.SepReal.hsn X = 0) : X = 0 := by
  unfold GlobalTheory.SepReal.hsn at h
  have hs : ∑ a, ∑ b, ‖X a b‖ ^ 2 = 0 := by
    rwa [Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 hs i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h1 j (Finset.mem_univ _)
  simpa using h2

private theorem real_smul_mem_lieOf {m : ℕ} {G X : Matrix (Fin m) (Fin m) ℂ} (hX : X ∈ GlobalTheory.Ell.lieOf G) (r : ℝ) :
    r • X ∈ GlobalTheory.Ell.lieOf G := by
  have hX0 : Xᴴ * G + G * X = 0 := hX
  show (r • X)ᴴ * G + G * (r • X) = 0
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX0, smul_zero]

private theorem embOpt_mul' {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (h k : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.PackLoc.embOpt e (h * k) = GlobalTheory.PackLoc.embOpt e h * GlobalTheory.PackLoc.embOpt e k := by
  ext a b
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_option]
  cases x <;> cases y <;> simp [GlobalTheory.PackLoc.embOpt, Matrix.mul_apply]

private theorem embOpt_conjTranspose {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (h : Matrix (Fin m) (Fin m) ℂ) :
    (GlobalTheory.PackLoc.embOpt e h)ᴴ = GlobalTheory.PackLoc.embOpt e hᴴ := by
  ext a b
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  cases x <;> cases y <;> simp [GlobalTheory.PackLoc.embOpt, Matrix.conjTranspose_apply]

private theorem Jm_eq_embOpt_Jm {m N : ℕ} (e : Option (Fin m) ≃ Fin N) {ε : Fin N → Bool} {ε' : Fin m → Bool}
    (h0 : ε (e none) = true) (h1 : ∀ i, ε (e (some i)) = ε' i) :
    Formalism.REAL.Jm ε = GlobalTheory.PackLoc.embOpt e (Formalism.REAL.Jm ε') := by
  ext a b
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  cases x <;> cases y <;> simp [GlobalTheory.PackLoc.embOpt, Formalism.REAL.Jm, Matrix.diagonal_apply, h0, h1]

private theorem embOpt_mem_UJset {m N : ℕ} (e : Option (Fin m) ≃ Fin N) {ε : Fin N → Bool} {ε' : Fin m → Bool}
    (h0 : ε (e none) = true) (h1 : ∀ i, ε (e (some i)) = ε' i) {g : Matrix (Fin m) (Fin m) ℂ}
    (hg : g ∈ Formalism.MainNotions.S.UJset ε') : GlobalTheory.PackLoc.embOpt e g ∈ Formalism.MainNotions.S.UJset ε := by
  have hg' : gᴴ * Formalism.REAL.Jm ε' * g = Formalism.REAL.Jm ε' := hg
  show (GlobalTheory.PackLoc.embOpt e g)ᴴ * Formalism.REAL.Jm ε * GlobalTheory.PackLoc.embOpt e g = Formalism.REAL.Jm ε
  rw [Jm_eq_embOpt_Jm e h0 h1, embOpt_conjTranspose, ← embOpt_mul', ← embOpt_mul', hg']

private theorem embOptL_mem_lieOf_Jm {m N : ℕ} (e : Option (Fin m) ≃ Fin N) {ε : Fin N → Bool} {ε' : Fin m → Bool}
    (h0 : ε (e none) = true) (h1 : ∀ i, ε (e (some i)) = ε' i) {X : Matrix (Fin m) (Fin m) ℂ}
    (hX : X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε')) : GlobalTheory.PackLoc.embOptL e X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε) := by
  have hX' : Xᴴ * Formalism.REAL.Jm ε' + Formalism.REAL.Jm ε' * X = 0 := hX
  show (GlobalTheory.PackLoc.embOptL e X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * GlobalTheory.PackLoc.embOptL e X = 0
  ext a b
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  rcases x with _ | i <;> rcases y with _ | j
  · simp [GlobalTheory.PackLoc.embOptL, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  · simp [GlobalTheory.PackLoc.embOptL, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  · simp [GlobalTheory.PackLoc.embOptL, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  · have hij := congrFun (congrFun hX' i) j
    simp [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] at hij
    simpa [GlobalTheory.PackLoc.embOptL, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.conjTranspose_apply, h1] using hij

private theorem embOpt_exp_smul {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (t : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (t • X)) = NormedSpace.exp (t • GlobalTheory.PackLoc.embOptL e X) := by
  obtain rfl : N = m + 1 := by simpa using (Fintype.card_congr e).symm
  have hL := (GlobalTheory.SepReal.embLaws m e (fun _ => true) (fun _ => true) ⟨rfl, fun _ => rfl⟩).2.2.2.2.2.2.2.1 t X
  rw [← GlobalTheory.PackLoc.embH_eq_embOpt, ← GlobalTheory.PackLoc.embL_eq_embOptL, hL]

private theorem continuous_embOpt {m N : ℕ} (e : Option (Fin m) ≃ Fin N) : Continuous (GlobalTheory.PackLoc.embOpt e) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  cases x <;> cases y <;> simp [GlobalTheory.PackLoc.embOpt] <;>
    first | fun_prop | exact (continuous_apply _).comp (continuous_apply _)

private theorem continuous_exp_real_smul' {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • X) := by
  have hc : Continuous (NormedSpace.exp : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ) := by
    exact @NormedSpace.exp_continuous (Matrix (Fin m) (Fin m) ℂ) Matrix.linftyOpNormedRing
      Matrix.linftyOpNormedAlgebra (by exact (inferInstance : CompleteSpace (Matrix (Fin m) (Fin m) ℂ)))
  exact hc.comp (continuous_id.smul continuous_const)

theorem lip_core : ∀ (m N : ℕ) (e : Option (Fin m) ≃ Fin N) (ε : Fin N → Bool) (ε' : Fin m → Bool)
  (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (v : H) (K : ℝ),
  Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) π → ε (e none) = true → (∀ i, ε (e (some i)) = ε' i) →
  GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) π v →
  (∀ g ∈ Formalism.MainNotions.S.UJset ε,
    Integrable (fun h => ⟪v, π (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ) (Formalism.REAL.muG ε')) →
  (∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε'), GlobalTheory.SepReal.hsn X ≤ 1 →
    Integrable (fun h => ⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL e X) v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ)
      (Formalism.REAL.muG ε') ∧
    ∫ h, ‖⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL e X) v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ε') ≤ K) →
  ∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε'), ∀ s : ℝ,
    Integrable (fun h => ‖⟪v, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖) (Formalism.REAL.muG ε') ∧
    ∫ h, ‖⟪v, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ε') ≤ K * |s| * GlobalTheory.SepReal.hsn X := by
  intro m N e ε ε' H _ _ π v K hπ h0 h1 hv hI hK X hX s
  obtain ⟨-, -, hπcont⟩ := id hπ
  have hmem : ∀ g ∈ Formalism.MainNotions.S.UJset ε', GlobalTheory.PackLoc.embOpt e g ∈ Formalism.MainNotions.S.UJset ε :=
    fun g hg => embOpt_mem_UJset e h0 h1 hg
  have hone : (1 : Matrix (Fin N) (Fin N) ℂ) ∈ Formalism.MainNotions.S.UJset ε := by
    show (1 : Matrix (Fin N) (Fin N) ℂ)ᴴ * Formalism.REAL.Jm ε * 1 = Formalism.REAL.Jm ε
    simp
  have hint : Integrable (fun h : Formalism.REAL.UJ ε' =>
      ‖⟪v, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
        ⟪v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖) (Formalism.REAL.muG ε') := by
    have hA := hI _ (hmem _ (exp_mem' hX s))
    have hB := hI 1 hone
    refine (hA.sub hB).norm.congr (Filter.Eventually.of_forall fun h => ?_)
    simp only [Pi.sub_apply, embOpt_mul', one_mul]
  refine ⟨hint, ?_⟩
  by_cases hX0 : X = 0
  · subst hX0
    simp [GlobalTheory.SepReal.hsn]
  have hpos : 0 < GlobalTheory.SepReal.hsn X :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) (fun h => hX0 (eq_zero_of_hsn h.symm))
  set c := GlobalTheory.SepReal.hsn X with hc
  have hX'lie : c⁻¹ • X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε') := real_smul_mem_lieOf hX c⁻¹
  have hX'n : GlobalTheory.SepReal.hsn (c⁻¹ • X) = 1 := by
    rw [hsn_smul, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
  obtain ⟨hDi, hDb⟩ := hK _ hX'lie hX'n.le
  have hZ : GlobalTheory.PackLoc.embOptL e (c⁻¹ • X) ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε) := embOptL_mem_lieOf_Jm e h0 h1 hX'lie
  let u : ℝ → (Matrix (Fin m) (Fin m) ℂ)ˣ := fun t =>
    ⟨NormedSpace.exp (t • c⁻¹ • X), NormedSpace.exp ((-t) • c⁻¹ • X),
      by rw [← exp_add', add_neg_cancel, zero_smul, NormedSpace.exp_zero],
      by rw [← exp_add', neg_add_cancel, zero_smul, NormedSpace.exp_zero]⟩
  let γ : ℝ → Formalism.REAL.UJ ε' := fun t => ⟨u t, exp_mem' hX'lie t⟩
  let f : Formalism.REAL.UJ ε' → ℂ := fun h => ⟪v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ
  let D : Formalism.REAL.UJ ε' → ℂ := fun h =>
    -⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL e (c⁻¹ • X)) v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ
  have hkey : ∀ (t : ℝ) (h : Formalism.REAL.UJ ε'),
      π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (t • c⁻¹ • X) * Formalism.MainNotions.S.umat h)) v =
        π (NormedSpace.exp (t • GlobalTheory.PackLoc.embOptL e (c⁻¹ • X))) (π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v) := by
    intro t h
    rw [embOpt_mul', embOpt_exp_smul,
      rep_mul' hπ (exp_mem' hZ t) (hmem _ h.2)]
  have hγ0 : γ 0 = 1 := by
    apply Subtype.ext
    apply Units.ext
    show NormedSpace.exp ((0:ℝ) • c⁻¹ • X) = 1
    rw [zero_smul, NormedSpace.exp_zero]
  have hd : ∀ (h : Formalism.REAL.UJ ε') (t : ℝ), HasDerivAt (fun t => f (γ t * h)) (D (γ t * h)) t := by
    intro h t
    have H1 := hasDerivAt_coef hπ hZ hv (π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v) t
    have e1 : (fun t => f (γ t * h)) = fun r : ℝ =>
        ⟪v, π (NormedSpace.exp (r • GlobalTheory.PackLoc.embOptL e (c⁻¹ • X)))
          (π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v)⟫_ℂ := by
      funext r
      show ⟪v, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (r • c⁻¹ • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ = _
      rw [hkey]
    have e2 : D (γ t * h) = -⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL e (c⁻¹ • X)) v,
        π (NormedSpace.exp (t • GlobalTheory.PackLoc.embOptL e (c⁻¹ • X)))
          (π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v)⟫_ℂ := by
      show -⟪_, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (t • c⁻¹ • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ = _
      rw [hkey]
    rw [e1, e2]
    exact H1
  have hcD : Continuous fun p : ℝ × Formalism.REAL.UJ ε' => D (γ p.1 * p.2) := by
    have hum : Continuous fun h : Formalism.REAL.UJ ε' => Formalism.MainNotions.S.umat h :=
      Units.continuous_val.comp continuous_subtype_val
    have hg : Continuous fun p : ℝ × Formalism.REAL.UJ ε' =>
        GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (p.1 • c⁻¹ • X) * Formalism.MainNotions.S.umat p.2) :=
      (continuous_embOpt e).comp (((continuous_exp_real_smul' (c⁻¹ • X)).comp continuous_fst).mul (hum.comp continuous_snd))
    have hπc : Continuous fun p : ℝ × Formalism.REAL.UJ ε' =>
        π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (p.1 • c⁻¹ • X) * Formalism.MainNotions.S.umat p.2)) v :=
      (hπcont v).comp_continuous hg fun p => hmem _ (γ p.1 * p.2).2
    exact (continuous_const.inner hπc).neg
  have hmain := integral_translate_le (Formalism.REAL.muG ε') f D γ hγ0 hDi.neg hcD hd (s * c)
  have hsX : (s * c) • c⁻¹ • X = s • X := by
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one]
  have hDn : ∫ h, ‖D h‖ ∂(Formalism.REAL.muG ε') ≤ K := by simpa only [D, norm_neg] using hDb
  calc _ = ∫ h, ‖f (γ (s * c) * h) - f h‖ ∂(Formalism.REAL.muG ε') := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
        show _ = ‖⟪v, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp ((s * c) • c⁻¹ • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
          ⟪v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖
        rw [hsX]
    _ ≤ |s * c| * ∫ h, ‖D h‖ ∂(Formalism.REAL.muG ε') := hmain
    _ ≤ |s * c| * K := mul_le_mul_of_nonneg_left hDn (abs_nonneg _)
    _ = K * |s| * c := by rw [abs_mul, abs_of_pos hpos]; ring

end GlobalTheory.PackLip

end
