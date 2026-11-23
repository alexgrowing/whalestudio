import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableMajorantAdelicSchwartzLocallyUnifo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictTranslatedDiagonalMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierSecondVariableRapidDecayStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

noncomputable section
namespace GlobalTheory.PartialFourierSum

open GroundTheory.Global NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem adelicFourierPi_mul (f : (κ → mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (y : κ → AdeleRing (𝓞 F) F) :
    adelicFourierPi F (fun x => f (infPartPi x) * g (finPartPi x)) y =
      mixedFourierPi F f (infPartPi y) * finiteFourierPi F g (finPartPi y) := by
  have h := integral_prod_mul (μ := mixedMeasurePi F) (ν := finiteMeasurePi F)
    (fun u ↦ 𝐞 (-mixedPairingPi F u (infPartPi y)) • f u)
    (fun v ↦ g v * (finiteAdelicChar F (∑ i, v i * finPartPi y i) : ℂ))
  have e := measurePreserving_splitEquivPi.integral_comp' (μ := adeleMeasurePi F)
    (f := splitEquivPi F κ) (fun p : (κ → mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) ↦
      (𝐞 (-mixedPairingPi F p.1 (infPartPi y)) • f p.1) *
        (g p.2 * (finiteAdelicChar F (∑ i, p.2 i * finPartPi y i) : ℂ)))
  rw [mixedFourierPi, finiteFourierPi, ← h, ← e, adelicFourierPi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [splitEquivPi_apply, adelicChar_sum_mul_eq_pi, Circle.smul_def, smul_eq_mul]
  ring

theorem exists_summable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : (κ → mixedSpace F) ≃L[ℝ] E)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → Summable fun ξ : κ → F => ((1 + ‖L (embPi F ξ)‖) ^ k)⁻¹ *
      ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ := by
  obtain ⟨k₀, M, hM, hb⟩ := GlobalTheory.SchwartzMajorant.exists_majorant_pureA F (g := g) hg 0
  refine ⟨k₀, fun k hk => ?_⟩
  set c : ℝ := ‖(L.symm : E →L[ℝ] (κ → mixedSpace F))‖ with hc
  have hn : ∀ v, ‖((((1 + ‖L v‖) ^ k)⁻¹ : ℝ) : ℂ)‖ = ((1 + ‖L v‖) ^ k)⁻¹ := fun v => by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hb' := hb 1 (c ^ k₀) (fun v => ((((1 + ‖L v‖) ^ k)⁻¹ : ℝ) : ℂ))
    (fun v => by
      rw [hn]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg (L v)])))
    (fun v => by
      rw [hn, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      have h1 : ‖v‖ ≤ c * ‖L v‖ := by
        simpa using (L.symm : E →L[ℝ] (κ → mixedSpace F)).le_opNorm (L v)
      have hc0 : 0 ≤ c := norm_nonneg _
      calc ‖v‖ ^ k₀ ≤ (c * (1 + ‖L v‖)) ^ k₀ :=
            pow_le_pow_left₀ (norm_nonneg _) (h1.trans (by nlinarith [norm_nonneg (L v)])) _
        _ = c ^ k₀ * (1 + ‖L v‖) ^ k₀ := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by linarith [norm_nonneg (L v)]) hk) (by positivity))
  refine Summable.of_nonneg_of_le (fun ξ => by positivity) (fun ξ => ?_) (hM.mul_left (1 + c ^ k₀))
  have h := hb' ξ
  rw [GlobalTheory.SchwartzMajorant.pureA_add_algebraMap, norm_mul, hn] at h
  have e1 : ((fun j => mixedEmbedding F (ξ j)) + fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((0 : κ → AdeleRing (𝓞 F) F) j).1) = embPi F ξ := by
    funext j
    simp only [Pi.add_apply, Pi.zero_apply, embPi]
    rw [show (0 : AdeleRing (𝓞 F) F).1 = 0 from rfl, map_zero, add_zero]
  have e2 : ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + fun j =>
      ((0 : κ → AdeleRing (𝓞 F) F) j).2) = fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j) := by
    funext j
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [show (0 : AdeleRing (𝓞 F) F).2 = 0 from rfl, add_zero]
  rw [e1, e2] at h
  exact h

def shear : ((κ → mixedSpace F) × EuclidPi F κ) ≃L[ℝ] (κ ⊕ κ → mixedSpace F) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => Sum.elim ((toEuclidPi F).symm p.2 + p.1) ((toEuclidPi F).symm p.2)
      map_add' := fun p q => by
        funext i
        rcases i with i | i
        · simp only [Prod.fst_add, Prod.snd_add, map_add, Sum.elim_inl, Pi.add_apply]; abel
        · simp only [Prod.snd_add, map_add, Sum.elim_inr, Pi.add_apply]
      map_smul' := fun a p => by
        funext i
        rcases i with i | i
        · simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Sum.elim_inl, Pi.add_apply, Pi.smul_apply,
            RingHom.id_apply, smul_add]
        · simp only [Prod.smul_snd, map_smul, Sum.elim_inr, Pi.smul_apply, RingHom.id_apply]
      invFun := fun x => (fun i => x (Sum.inl i) - x (Sum.inr i), toEuclidPi F fun i => x (Sum.inr i))
      left_inv := fun p => by
        refine Prod.ext (funext fun i => ?_) ?_
        · simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply]; abel
        · simp only [Sum.elim_inr]
          exact (toEuclidPi F).apply_symm_apply p.2
      right_inv := fun x => by
        funext i
        rcases i with i | i
        · simp only [ContinuousLinearEquiv.symm_apply_apply, Sum.elim_inl, Pi.add_apply]; abel
        · simp only [ContinuousLinearEquiv.symm_apply_apply, Sum.elim_inr] }

theorem arch_bound (f : SchwartzMap (κ ⊕ κ → mixedSpace F) ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ u v : κ → mixedSpace F, ‖mixedFourierPi F (fun t => f (Sum.elim (t + u) t)) v‖ ≤
      C * (((1 + ‖u‖) ^ k)⁻¹ * ((1 + ‖toEuclidPiConj F v‖) ^ k)⁻¹) := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.schwartz_fourier_secondVariable_rapid_decay (κ → mixedSpace F) (EuclidPi F κ)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (shear (F := F) (κ := κ)) f) k
  refine ⟨C, fun u v => ?_⟩
  have h := hC u (toEuclidPiConj F v)
  rw [mixedFourierPi_eq, ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact h

theorem finiteTensor_shift (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (b : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F)
    (u t : κ → FiniteAdeleRing (𝓞 F) F) :
    finiteTensor (fun i => cosetIndicator J (b i)) (Sum.elim (t + u) t) =
      finiteTensor (fun i => cosetIndicator J (b (Sum.inl i) - b (Sum.inr i))) u *
        finiteTensor (fun i => cosetIndicator J (b (Sum.inr i))) t := by
  simp only [finiteTensor, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [cosetIndicator_apply]
  by_cases h : t i - b (Sum.inr i) ∈ idealFiniteAdeles J
  · have : t i + u i - b (Sum.inl i) ∈ idealFiniteAdeles J ↔
        u i - (b (Sum.inl i) - b (Sum.inr i)) ∈ idealFiniteAdeles J := by
      rw [show t i + u i - b (Sum.inl i) = (t i - b (Sum.inr i)) + (u i - (b (Sum.inl i) - b (Sum.inr i))) by ring]
      exact AddSubgroup.add_mem_cancel_left _ h
    simp only [this]
  · simp only [if_neg h, mul_zero]

theorem summable_gen (f : SchwartzMap (κ ⊕ κ → mixedSpace F) ℂ) (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (b : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :
    Summable fun uv : (κ → F) × (κ → F) => ‖adelicFourierPi F (fun t : κ → AF F =>
      schwartzBruhatTensorPi f (finiteTensor fun i => cosetIndicator J (b i))
        (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) (fun i => algebraMap F (AF F) (uv.2 i))‖ := by
  set g₁ := finiteTensor (fun i => cosetIndicator J (b (Sum.inl i) - b (Sum.inr i))) with hg₁
  set g₂ := finiteTensor (fun i => cosetIndicator J (b (Sum.inr i))) with hg₂
  have m₁ : g₁ ∈ finiteSchwartzBruhatPi F :=
    finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J _
  have m₂ : finiteFourierPi F g₂ ∈ finiteSchwartzBruhatPi F :=
    finiteFourierPi_mem (finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J _)
  obtain ⟨k₁, h₁⟩ := exists_summable (ContinuousLinearEquiv.refl ℝ (κ → mixedSpace F)) m₁
  obtain ⟨k₂, h₂⟩ := exists_summable (toEuclidPiConj F) m₂
  obtain ⟨C, hC⟩ := arch_bound f (max k₁ k₂)
  have hs := ((h₁ _ (le_max_left k₁ k₂)).mul_of_nonneg (h₂ _ (le_max_right k₁ k₂))
    (fun _ => by positivity) (fun _ => by positivity)).mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun uv => ?_) hs
  have key : (fun t : κ → AF F => schwartzBruhatTensorPi f (finiteTensor fun i => cosetIndicator J (b i))
        (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) =
      fun t => (fun s => f (Sum.elim (s + embPi F uv.1) s)) (infPartPi t) *
        (g₁ (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (uv.1 i)) • g₂) (finPartPi t) := by
    funext t
    have e1 : infPartPi (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t) =
        Sum.elim (infPartPi t + embPi F uv.1) (infPartPi t) := by
      rw [← infPartPi_algebraMap]
      funext i
      rcases i with i | i
      · simp only [infPartPi, Sum.elim_inl, Pi.add_apply, homeomorphMixedSpace_apply]
        exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _
      · rfl
    have e2 : finPartPi (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t) =
        Sum.elim (finPartPi t + fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (uv.1 i)) (finPartPi t) := by
      rw [← finPartPi_algebraMap]
      funext i
      rcases i with i | i <;> rfl
    rw [schwartzBruhatTensorPi, e1, e2, finiteTensor_shift]
    rfl
  rw [key, adelicFourierPi_mul (fun s => f (Sum.elim (s + embPi F uv.1) s)), finiteFourierPi_smul, infPartPi_algebraMap, finPartPi_algebraMap, norm_mul,
    Pi.smul_apply, smul_eq_mul, norm_mul]
  refine (mul_le_mul_of_nonneg_right (hC _ _) (by positivity)).trans (le_of_eq ?_)
  simp only [ContinuousLinearEquiv.refl_apply]
  ring

theorem summable_partial_fourier : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : (κ ⊕ κ → AF F) → ℂ), φ ∈ schA F (κ ⊕ κ) → Summable fun uv : (κ → F) × (κ → F) => ‖adelicFourierPi F (fun t : κ → AF F => φ (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) (fun i => algebraMap F (AF F) (uv.2 i))‖ := by
  intro F _ _ κ _ φ hφ
  have hS : schA F (κ ⊕ κ) = cosetSpanPi F (κ ⊕ κ) := by
    rw [← schwartzBruhatPi_eq_cosetSpanPi]
    refine congrArg (Submodule.span ℂ) (Set.ext fun Φ => ?_)
    exact ⟨fun ⟨f, g, hg, h⟩ => ⟨f, g, hg, h⟩, fun ⟨f, g, hg, h⟩ => ⟨f, g, hg, h⟩⟩
  have hI : ∀ ψ ∈ cosetSpanPi F (κ ⊕ κ), ∀ u : κ → AF F,
      Integrable (fun t : κ → AF F => ψ (Sum.elim (t + u) t)) (adeleMeasurePi F) := fun ψ hψ u =>
    integrable_of_mem_schwartzBruhatPi (GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi F κ ψ (hS ▸ hψ) u)
  rw [hS] at hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, J, b, rfl⟩ := hG
    exact summable_gen f J b
  | zero =>
    simp only [Pi.zero_apply, adelicFourierPi, zero_mul, integral_zero, norm_zero]
    exact summable_zero
  | add G H hG hH ihG ihH =>
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun uv => ?_) (ihG.add ihH)
    have h := congrFun (adelicFourierPi_add (hI G hG fun i => algebraMap F (AF F) (uv.1 i))
      (hI H hH fun i => algebraMap F (AF F) (uv.1 i))) (fun i => algebraMap F (AF F) (uv.2 i))
    exact (congrArg norm h).le.trans (norm_add_le _ _)
  | smul c G _ ih =>
    refine (ih.mul_left ‖c‖).congr fun uv => ?_
    have h := congrFun (adelicFourierPi_smul c (fun t : κ → AF F =>
      G (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t))) (fun i => algebraMap F (AF F) (uv.2 i))
    rw [← _root_.norm_smul]
    exact (congrArg norm h).symm

end GlobalTheory.PartialFourierSum
