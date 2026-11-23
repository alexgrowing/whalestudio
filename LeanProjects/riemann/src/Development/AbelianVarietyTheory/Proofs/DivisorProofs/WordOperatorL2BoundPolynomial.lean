import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.WordL2Estimates

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

abbrev Dir (F : Type) [Field F] [NumberField F] (κ : Type) : Type :=
  (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)

theorem real_smul_fun {X : Type} (r : ℝ) (f : X → ℂ) : r • f = (r : ℂ) • f := by
  funext x
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]

theorem dD_add_fun (v : κ → mixedEmbedding.mixedSpace F) {Φ Ψ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ)
    (hΨ : Ψ ∈ schA F κ) : dD F v (Φ + Ψ) = dD F v Φ + dD F v Ψ := by
  funext x
  simp only [dD, Pi.add_apply]
  exact deriv_add ((SchAStab.archimedeanDirectionalDerivative_mem_adelicSchwartz F v hΦ).1 x) ((SchAStab.archimedeanDirectionalDerivative_mem_adelicSchwartz F v hΨ).1 x)

theorem dD_pureA_apply (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (v : κ → mixedEmbedding.mixedSpace F) (x : κ → AF F) :
    dD F v (pureA F f g) x = fderiv ℝ f (arch F x) v * g (fun i => (x i).2) := by
  rw [dD, (SchAStab.hasDerivAt_line F f g x v).deriv]

theorem dD_dir {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (∀ v w : κ → mixedEmbedding.mixedSpace F, dD F (v + w) Φ = dD F v Φ + dD F w Φ) ∧
      ∀ (r : ℝ) (v : κ → mixedEmbedding.mixedSpace F), dD F (r • v) Φ = (r : ℂ) • dD F v Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨fun v w => funext fun x => ?_, fun r v => funext fun x => ?_⟩
    · simp only [Pi.add_apply, dD_pureA_apply, map_add, add_mul]
    · simp only [Pi.smul_apply, dD_pureA_apply, map_smul, smul_eq_mul, Complex.real_smul]
      ring
  | zero =>
    have h0 : ∀ u : κ → mixedEmbedding.mixedSpace F, dD F u (0 : (κ → AF F) → ℂ) = 0 := fun u => by
      funext x; simp [dD]
    exact ⟨fun v w => by rw [h0, h0, h0, add_zero], fun r v => by rw [h0, h0, smul_zero]⟩
  | add Φ Ψ hΦ hΨ h1 h2 =>
    refine ⟨fun v w => ?_, fun r v => ?_⟩
    · rw [dD_add_fun _ hΦ hΨ, dD_add_fun _ hΦ hΨ, dD_add_fun _ hΦ hΨ, h1.1, h2.1]
      abel
    · rw [dD_add_fun _ hΦ hΨ, dD_add_fun _ hΦ hΨ, h1.2, h2.2, smul_add]
  | smul a Φ hΦ h =>
    refine ⟨fun v w => ?_, fun r v => ?_⟩
    · rw [dD_smul, dD_smul, dD_smul, h.1, smul_add]
    · rw [dD_smul, dD_smul, h.2, smul_comm]

theorem mM_add_l (l l' : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : (κ → AF F) → ℂ) :
    mM F (l + l') f = mM F l f + mM F l' f := by
  funext x
  simp only [mM, ContinuousLinearMap.add_apply, Complex.ofReal_add, Pi.add_apply, add_mul]

theorem mM_smul_l (r : ℝ) (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : (κ → AF F) → ℂ) :
    mM F (r • l) f = (r : ℂ) • mM F l f := by
  funext x
  simp only [mM, ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul, Pi.smul_apply, mul_assoc]

theorem mM_add_f (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f g : (κ → AF F) → ℂ) :
    mM F l (f + g) = mM F l f + mM F l g := by
  funext x
  simp only [mM, Pi.add_apply, mul_add]

variable (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ)

theorem dR_add_dir {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (ζ ζ' : Dir F κ) :
    dR F T c (ζ + ζ') Φ = dR F T c ζ Φ + dR F T c ζ' Φ := by
  unfold dR
  rw [Prod.fst_add, Prod.snd_add, (dD_dir hΦ).1, map_add T, mM_add_l, smul_add]
  abel

theorem dR_smul_dir {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (r : ℝ) (ζ : Dir F κ) :
    dR F T c (r • ζ) Φ = r • dR F T c ζ Φ := by
  unfold dR
  rw [Prod.smul_fst, Prod.smul_snd, (dD_dir hΦ).2, map_smul T, mM_smul_l, smul_comm c, ← smul_add, real_smul_fun]

theorem dR_add_fun (ζ : Dir F κ) {Φ Ψ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (hΨ : Ψ ∈ schA F κ) :
    dR F T c ζ (Φ + Ψ) = dR F T c ζ Φ + dR F T c ζ Ψ := by
  unfold dR
  rw [dD_add_fun _ hΦ hΨ, mM_add_f, smul_add]
  abel

theorem dR_smul_fun (ζ : Dir F κ) (a : ℂ) (f : (κ → AF F) → ℂ) : dR F T c ζ (a • f) = a • dR F T c ζ f := by
  unfold dR
  rw [dD_smul, mM_smul, smul_comm c a, ← smul_add]

theorem dR_mem (ζ : Dir F κ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : dR F T c ζ Φ ∈ schA F κ :=
  Submodule.add_mem _ (SchAStab.archimedeanDirectionalDerivative_mem_adelicSchwartz F ζ.1 hΦ).2 (Submodule.smul_mem _ c (SchAStab.mem_schA_mM F _ hΦ))

theorem wordR_mem (zs : List (Dir F κ)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : wordR F T c zs Φ ∈ schA F κ := by
  induction zs with
  | nil => exact hΦ
  | cons ζ zs ih => exact dR_mem T c ζ ih

theorem wordR_add (zs : List (Dir F κ)) {Φ Ψ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (hΨ : Ψ ∈ schA F κ) :
    wordR F T c zs (Φ + Ψ) = wordR F T c zs Φ + wordR F T c zs Ψ := by
  induction zs with
  | nil => rfl
  | cons ζ zs ih =>
    show dR F T c ζ (wordR F T c zs (Φ + Ψ)) = dR F T c ζ (wordR F T c zs Φ) + dR F T c ζ (wordR F T c zs Ψ)
    rw [ih, dR_add_fun T c ζ (wordR_mem T c zs hΦ) (wordR_mem T c zs hΨ)]

theorem wordR_smul (zs : List (Dir F κ)) (a : ℂ) (f : (κ → AF F) → ℂ) :
    wordR F T c zs (a • f) = a • wordR F T c zs f := by
  induction zs with
  | nil => rfl
  | cons ζ zs ih =>
    show dR F T c ζ (wordR F T c zs (a • f)) = a • dR F T c ζ (wordR F T c zs f)
    rw [ih, dR_smul_fun]

theorem wordR_concat (zs : List (Dir F κ)) (ζ : Dir F κ) (Φ : (κ → AF F) → ℂ) :
    wordR F T c (zs ++ [ζ]) Φ = wordR F T c zs (dR F T c ζ Φ) := by
  unfold wordR
  rw [List.foldr_append]
  rfl

def wordRL (zs : List (Dir F κ)) : schA F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun Φ := wordR F T c zs Φ
  map_add' Φ Ψ := wordR_add T c zs Φ.2 Ψ.2
  map_smul' a Φ := wordR_smul T c zs a Φ

theorem wordR_sum {ι : Type} [Fintype ι] (zs : List (Dir F κ)) (a : ι → ℂ) (Φ : ι → (κ → AF F) → ℂ)
    (h : ∀ i, Φ i ∈ schA F κ) : wordR F T c zs (∑ i, a i • Φ i) = ∑ i, a i • wordR F T c zs (Φ i) := by
  have e : (∑ i, a i • Φ i) = ((∑ i, a i • (⟨Φ i, h i⟩ : schA F κ) : schA F κ) : (κ → AF F) → ℂ) := by
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [e]
  exact (map_sum (wordRL T c zs) _ _).trans (Finset.sum_congr rfl fun i _ => map_smul (wordRL T c zs) _ _)

def dRL {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Dir F κ →ₗ[ℝ] ((κ → AF F) → ℂ) where
  toFun ζ := dR F T c ζ Φ
  map_add' := dR_add_dir T c hΦ
  map_smul' := dR_smul_dir T c hΦ

theorem dR_expand {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (Dir F κ)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ)
    (ζ : Dir F κ) : dR F T c ζ Φ = ∑ i, ((b.repr ζ i : ℝ) : ℂ) • dR F T c (b i) Φ := by
  calc dR F T c ζ Φ = dRL T c hΦ ζ := rfl
    _ = dRL T c hΦ (∑ i, b.repr ζ i • b i) := by rw [b.sum_repr]
    _ = ∑ i, b.repr ζ i • dRL T c hΦ (b i) := by rw [map_sum]; simp only [map_smul]
    _ = _ := Finset.sum_congr rfl fun i _ => real_smul_fun _ _

theorem lintegral_enorm_sq {X : Type} {m : MeasurableSpace X} (μ : Measure X) (f : X → ℂ) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = eLpNorm f 2 μ ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [ENNReal.toReal_ofNat, Nat.cast_ofNat, one_div]
  rw [inv_mul_cancel₀ two_ne_zero, ENNReal.rpow_one]
  simp only [ENNReal.rpow_two]

end GlobalTheory.ArchDecay.WordL2Estimates

namespace GlobalTheory.ArchDecay.WordL2Estimates

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
variable (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ)

theorem eLpNorm_wordR_le (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (P : ℕ) : ∀ Φ ∈ schA F κ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 1 ≤ ρ → ∀ zs : List (Dir F κ), zs.length ≤ P →
      (∀ ζ ∈ zs, ‖ζ‖ ≤ ρ) → eLpNorm (wordR F T c zs Φ) 2 μ ≤ ENNReal.ofReal (C * ρ ^ P) := by
  letI : MeasurableSpace (κ → AF F) := borel _
  have hL2 : ∀ Φ ∈ schA F κ, MemLp Φ 2 μ := fun Φ hΦ => GlobalTheory.WeilM.schA_memLp_two F κ μ hμ Φ hΦ
  induction P with
  | zero =>
    intro Φ hΦ
    refine ⟨(eLpNorm Φ 2 μ).toReal, ENNReal.toReal_nonneg, fun ρ _ zs hl _ => ?_⟩
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl), pow_zero, mul_one,
      ENNReal.ofReal_toReal (hL2 Φ hΦ).eLpNorm_lt_top.ne]
    rfl
  | succ P ih =>
    intro Φ hΦ
    let b := Module.finBasis ℝ (Dir F κ)
    obtain ⟨C₀, h₀, hC₀⟩ := ih Φ hΦ
    choose C h1 hC using fun i => ih (dR F T c (b i) Φ) (dR_mem T c (b i) hΦ)
    let κ₀ := ‖b.equivFunL.toContinuousLinearMap‖
    have hκ₀ : 0 ≤ κ₀ := norm_nonneg _
    have hs : 0 ≤ ∑ i, κ₀ * C i := Finset.sum_nonneg fun i _ => mul_nonneg hκ₀ (h1 i)
    refine ⟨C₀ + ∑ i, κ₀ * C i, add_nonneg h₀ hs, fun ρ hρ zs hl hu => ?_⟩
    have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
    have hρp : 0 ≤ ρ ^ P := pow_nonneg hρ0 P
    rcases List.eq_nil_or_concat' zs with rfl | ⟨zs', ζ, rfl⟩
    · refine (hC₀ ρ hρ [] (Nat.zero_le _) (by simp)).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul (le_add_of_nonneg_right hs) (pow_le_pow_right₀ hρ P.le_succ) hρp (add_nonneg h₀ hs)
    · have hl' : zs'.length ≤ P := by simpa using hl
      have hu' : ∀ z ∈ zs', ‖z‖ ≤ ρ := fun z hz => hu z (List.mem_append_left _ hz)
      have hζ : ‖ζ‖ ≤ ρ := hu ζ (List.mem_append_right _ (List.mem_singleton_self _))
      have a2 : ∀ i, ‖b.repr ζ i‖ ≤ κ₀ * ρ := fun i =>
        (norm_le_pi_norm (b.equivFunL.toContinuousLinearMap ζ) i).trans
          ((b.equivFunL.toContinuousLinearMap.le_opNorm ζ).trans (mul_le_mul_of_nonneg_left hζ hκ₀))
      rw [wordR_concat, dR_expand T c b hΦ ζ, wordR_sum T c zs' _ _ fun i => dR_mem T c (b i) hΦ]
      calc eLpNorm (∑ i, ((b.repr ζ i : ℝ) : ℂ) • wordR F T c zs' (dR F T c (b i) Φ)) 2 μ
          ≤ ∑ i, eLpNorm (((b.repr ζ i : ℝ) : ℂ) • wordR F T c zs' (dR F T c (b i) Φ)) 2 μ :=
            eLpNorm_sum_le (fun i _ => ((hL2 _ (wordR_mem T c zs' (dR_mem T c (b i) hΦ))).const_smul _).1)
              one_le_two
        _ ≤ ∑ i, ENNReal.ofReal (κ₀ * ρ * (C i * ρ ^ P)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [eLpNorm_const_smul, ← ofReal_norm_eq_enorm, Complex.norm_real,
              ENNReal.ofReal_mul (mul_nonneg hκ₀ hρ0)]
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal (a2 i)) (hC i ρ hρ zs' hl' hu')
        _ = ENNReal.ofReal (∑ i, κ₀ * ρ * (C i * ρ ^ P)) :=
            (ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (mul_nonneg hκ₀ hρ0) (mul_nonneg (h1 i) hρp)).symm
        _ ≤ ENNReal.ofReal ((C₀ + ∑ i, κ₀ * C i) * ρ ^ (P + 1)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have e : ∑ i, κ₀ * ρ * (C i * ρ ^ P) = (∑ i, κ₀ * C i) * ρ ^ (P + 1) := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun i _ => by ring
            rw [e]
            exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left h₀) (pow_nonneg hρ0 _)

end GlobalTheory.ArchDecay.WordL2Estimates

namespace GlobalTheory.ArchDecay

theorem wordR_L2_le : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ), ∀ Φ ∈ schA F κ, ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ P : ℕ, ∃ C : ℝ, ∀ ρ : ℝ, 1 ≤ ρ → ∀ zs : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), zs.length ≤ P → (∀ ζ ∈ zs, ‖ζ‖ ≤ ρ) → ∫⁻ x, ‖wordR F T c zs Φ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * ρ ^ (2 * P)) := by
  intro F _ _ κ _ T c Φ hΦ μ hμ P
  obtain ⟨C, hC0, hC⟩ := WordL2Estimates.eLpNorm_wordR_le T c μ hμ P Φ hΦ
  refine ⟨C ^ 2, fun ρ hρ zs hl hu => ?_⟩
  have h := hC ρ hρ zs hl hu
  rw [WordL2Estimates.lintegral_enorm_sq]
  calc eLpNorm (wordR F T c zs Φ) 2 μ ^ 2 ≤ ENNReal.ofReal (C * ρ ^ P) ^ 2 := pow_le_pow_left' h 2
    _ = ENNReal.ofReal (C ^ 2 * ρ ^ (2 * P)) := by
      rw [← ENNReal.ofReal_pow (mul_nonneg hC0 (pow_nonneg (zero_le_one.trans hρ) _))]
      congr 1
      ring

end GlobalTheory.ArchDecay
