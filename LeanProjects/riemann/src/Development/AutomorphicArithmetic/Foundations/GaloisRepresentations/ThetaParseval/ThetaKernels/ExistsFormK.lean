import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ExistsForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsThetaFunOFHeisOFK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CommFEventuallyK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ProfHeisLiftK

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.SplitLagrF
theorem exists_form_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ e, IsSplitIdemF σ e →
      ∀ f₀, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f₀ →
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT) f₀ ≠ 0 →
      ∃ ℓ : (WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
        (∀ u : WOF F E nS (nT + nT), (∀ i j, cAF σ e * u i j = u i j) →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            ℓ (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
        (∃ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f ∧ ℓ f ≠ 0) ∧
        ∀ M : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), IsUnit M.det → ∃ R : ℝ, 0 < R ∧
          ∀ (f f' : WOF F E nS (nT + nT) → ℂ) (k : ℂ),
            IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f' →
            (∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
              prof σ JS JT ξ₀ B.ψ ν 𝓕 f' y = k * prof σ JS JT ξ₀ B.ψ ν 𝓕 f (M * y)) →
            ℓ f' = (R : ℂ) * k * ℓ f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ ν 𝓕 hν h𝓕 e he f₀ hf₀ hne
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  letI : MeasurableSpace (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) := borel _
  haveI : BorelSpace (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) :=
    (isClosed_conjHalf e).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : Measure (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) := Measure.addHaar
  haveI : μ.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar (G := GlobalTheory.SplitInvFormF.conjHalf σ e nS nT)).IsAddHaarMeasure
  have hth := _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS (nT + nT) JS
    (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀
  let L : GlobalTheory.WeilPartsF.thetaSubF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ y : GlobalTheory.SplitInvFormF.conjHalf σ e nS nT, prof σ JS JT ξ₀ B.ψ ν 𝓕 f.1 y.1 ∂μ
      map_add' := fun f g => by
        rw [← integral_add (_root_.GlobalTheory.SplitLagrF.prof_integrable_k hB hS hT hξ hσξ hν h𝓕 he μ f.2)
          (_root_.GlobalTheory.SplitLagrF.prof_integrable_k hB hS hT hξ hσξ hν h𝓕 he μ g.2)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => _root_.GlobalTheory.SplitLagrF.prof_add_k hB hν h𝓕 f.2 g.2 y.1)
      map_smul' := fun c f => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => prof_smul ν 𝓕 c f.1 y.1) }
  obtain ⟨ℓ, hℓ0⟩ := LinearMap.exists_extend L
  have hℓ : ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
      ℓ f = ∫ y : GlobalTheory.SplitInvFormF.conjHalf σ e nS nT, prof σ JS JT ξ₀ B.ψ ν 𝓕 f y.1 ∂μ :=
    fun f hf => LinearMap.congr_fun hℓ0 ⟨f, hf⟩
  refine ⟨ℓ, fun u hu f hf => ?_, ?_, fun M hM => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := exists_decomp (σ := σ) (e := e) hu
    rw [hℓ _ (hth _ _ hf), hℓ f hf,
      GlobalTheory.SplitVacF.heisOF_add_half he (mul_mem_conjHalf _ ha) (mul_mem_conjHalf _ hb),
      ← integral_add_right_eq_self (μ := μ)
        (fun y : GlobalTheory.SplitInvFormF.conjHalf σ e nS nT => prof σ JS JT ξ₀ B.ψ ν 𝓕 f y.1) ⟨b, hb⟩]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show _ = prof σ JS JT ξ₀ B.ψ ν 𝓕 f (y.1 + b)
    simp only
    rw [_root_.GlobalTheory.SplitLagrF.prof_heis_dC_k hB hS hT hξ hσξ hν h𝓕 (hth _ _ hf), GlobalTheory.SplitVacF.commF_half he y.2 (add_mem ha ha), one_mul,
      prof_heis_aC ν 𝓕 he f y.2 hb]
  · by_contra hall
    push Not at hall
    exact hne (_root_.GlobalTheory.SplitLagrF.lagrInt_eq_zero_k hB hS hT hξ hσξ hν h𝓕 he μ hf₀ fun u => by
      rw [← hℓ _ (hth u _ hf₀)]; exact hall _ (hth u _ hf₀))
  · obtain ⟨r, hr, hm⟩ := integral_mul_left e μ M hM
    refine ⟨r, hr, fun f f' k hf hf' hk => ?_⟩
    rw [hℓ f hf, hℓ f' hf', mul_comm (r : ℂ) k, mul_assoc, ← hm, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hk x.1 x.2)
end GlobalTheory.SplitLagrF
end
end
