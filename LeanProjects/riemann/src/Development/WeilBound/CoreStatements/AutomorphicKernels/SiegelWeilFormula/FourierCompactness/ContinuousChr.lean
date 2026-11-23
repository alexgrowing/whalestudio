import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kfour

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem continuous_chr {ψ : AddChar (AF F) ℂ} (hψ : Continuous ψ) {b : GL (Fin n ⊕ Fin n) E}
    (T : Matrix (Fin n) (Fin n) (AE F E)) :
    Continuous fun β : nA σ Y b => ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T * β.1)))) := by
  have htr : Continuous (Algebra.trace (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (Algebra.trace (AF F) (AE F E))
  exact hψ.comp ((htr.comp (continuous_const.matrix_mul continuous_subtype_val).matrix_trace).neg)

private theorem trace_inclR_eq_algebraMap_trace (e : E) :
    Algebra.trace (AF F) (AE F E) (inclR (AF F) e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  have h : Algebra.lmul (AF F) (AE F E) (inclR (AF F) e) =
      (Algebra.lmul F E e).baseChange (AF F) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    show (1 ⊗ₜ[F] e) * (a ⊗ₜ[F] x) = _
    rw [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]

theorem lamBd : LamBd := by
  intro F E _ _ _ _ _ σ d L hL
  obtain ⟨nb, lam, 𝓖, T, x, ⟨hnb, -, -, h1⟩, -, rfl⟩ := hL
  have good := d.ok.good
  have hσ := sigma_sigma_of_good good
  have hfr := d.ok.frame
  obtain ⟨hLC, hSC, hT2, hBo⟩ := nA_top hσ hfr
  have hnbc : Continuous nb := nb_continuous hσ hfr hnb
  obtain ⟨K, hK, hKcov⟩ := nF_cocompact hσ hfr
  have hψ1 : ∀ c : F, d.B.ψ (algebraMap F (AF F) c) = 1 := good.std.2.1
  let χ : nA σ d.Y d.b → ℂ := fun β =>
    d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (((T : nA σ d.Y d.b) :
      Matrix (Fin d.n) (Fin d.n) (AE F E)) * β.1))))
  have hχadd : ∀ β γ, χ (β + γ) = χ β * χ γ := by
    intro β γ
    simp only [χ, AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add, neg_add]
    exact AddChar.map_add_eq_mul _ _ _
  have hχns : ∀ (k : ℕ) β, χ (k • β) = χ β ^ k := by
    intro k β
    simp only [χ, AddSubgroup.coe_nsmul, Matrix.mul_smul, Matrix.trace_smul, map_nsmul, ← smul_neg]
    exact AddChar.map_nsmul_eq_pow _ _ _
  have htr : ∀ X : Matrix (Fin d.n) (Fin d.n) E,
      Matrix.trace (incM F X) = inclR (AF F) (Matrix.trace X) := by
    intro X
    simp [incM, Matrix.trace, map_sum]
  have hχF : ∀ γ ∈ nF σ d.Y d.b, χ γ = 1 := by
    intro γ hγ
    obtain ⟨G0, hG0⟩ := (mem_nF_iff γ).1 hγ
    obtain ⟨T0, hT0⟩ := (mem_nF_iff (T : nA σ d.Y d.b)).1 T.2
    simp only [χ]
    rw [hT0, hG0, ← incM_mul', htr, trace_inclR_eq_algebraMap_trace, ← map_neg]
    exact hψ1 _
  have hχc : Continuous χ := continuous_chr good.std.1 _
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hχc.continuousOn
  have hχR : ∀ β, ‖χ β‖ ≤ R := by
    intro β
    obtain ⟨γ, hγ, hmem⟩ := hKcov β
    have := hR _ hmem
    rwa [hχadd, hχF γ hγ, one_mul] at this
  have hχ1 : ∀ β, ‖χ β‖ ≤ 1 := by
    intro β
    by_contra hlt
    push_neg at hlt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R hlt
    have := hχR (k • β)
    rw [hχns, norm_pow] at this
    linarith
  have hper : ∀ f : G2 σ d.Y → ℂ, (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      ∀ β, ∃ β' ∈ K, f (nb β * x) = f (nb β' * x) := by
    intro f hf β
    obtain ⟨γ, hγ, hmem⟩ := hKcov β
    refine ⟨γ + β, hmem, ?_⟩
    rw [nb_add hnb, mul_assoc, hf _ (nb_rat hnb γ hγ)]
  have hfin : lam 𝓖 < ⊤ := by
    rw [h1]
    exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hint : ∀ f : G2 σ d.Y → ℂ, Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      Integrable (fun β => f (nb β * x) * χ β) (lam.restrict 𝓖) := by
    intro f hf hfi
    have hc : Continuous fun β => f (nb β * x) := hf.comp (hnbc.mul continuous_const)
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
    refine Integrable.of_bound (hc.mul hχc).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun β => ?_)
    obtain ⟨β', hβ', he⟩ := hper f hfi β
    rw [norm_mul, he]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hχ1 β)).trans (hM β' hβ')
  refine ⟨?_, ?_⟩
  · intro a f f' hf hf' hfi hfi'
    show ∫ β in 𝓖, (a • f + f') (nb β * x) * χ β ∂lam =
      a * ∫ β in 𝓖, f (nb β * x) * χ β ∂lam + ∫ β in 𝓖, f' (nb β * x) * χ β ∂lam
    have e : (fun β => (a • f + f') (nb β * x) * χ β) =
        fun β => a * (f (nb β * x) * χ β) + f' (nb β * x) * χ β := by
      funext β
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, integral_add ((hint f hf hfi).const_mul a) (hint f' hf' hfi'), integral_const_mul]
  · refine ⟨(fun β => nb β * x) '' K, hK.image (hnbc.mul continuous_const), ?_⟩
    intro f M hf hfi hM
    show ‖∫ β in 𝓖, f (nb β * x) * χ β ∂lam‖ ≤ M
    have hb : ∀ β ∈ 𝓖, ‖f (nb β * x) * χ β‖ ≤ M := by
      intro β _
      obtain ⟨β', hβ', he⟩ := hper f hfi β
      rw [norm_mul, he]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hχ1 β)).trans (hM _ ⟨β', hβ', rfl⟩)
    calc ‖∫ β in 𝓖, f (nb β * x) * χ β ∂lam‖ ≤ M * lam.real 𝓖 :=
          norm_setIntegral_le_of_norm_le_const hfin hb
      _ = M := by simp [Measure.real, h1]

end PositivityTheory.SiegelWeilFormula.kfour

end
