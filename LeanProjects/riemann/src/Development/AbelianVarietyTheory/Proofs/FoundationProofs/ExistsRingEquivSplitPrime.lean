import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousExtension

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.SplitCompletion

theorem continuous_of_valued_eq {A B Γ : Type*} [Ring A] [Ring B] [LinearOrderedCommGroupWithZero Γ]
    [Valued A Γ] [Valued B Γ] (hs : Function.Surjective (Valued.v : A → Γ)) (f : A →+* B)
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A _).tendsto_iff (Valued.hasBasis_nhds_zero B _)]
  intro γ _
  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    simp [ha]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [hf, ← ha]
  exact hx

open scoped WithZeroTopology in

theorem exists_extension {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (w : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) (f : K →+* u.adicCompletion L)
    (hf : ∀ x, Valued.v (f x) = w.valuation K x) :
    ∃ φ : w.adicCompletion K →+* u.adicCompletion L, Continuous φ ∧
      (∀ x : K, φ (algebraMap K _ x) = f x) ∧ ∀ y, Valued.v (φ y) = Valued.v y := by
  first
  | exact @_root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension
  | exact _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension
  | (apply _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension ..)

theorem exists_ringEquiv_splitPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v),
    ∃ φ : (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E ≃+* Fv F v, (∀ x : E, φ (algebraMap E _ x) = τ x) ∧
      (∀ y, Valued.v (φ y) = Valued.v y) ∧ Continuous φ ∧ Continuous φ.symm := by
  intro F E _ _ _ _ _ v τ
  obtain ⟨φ, hφc, hφ, hφv⟩ := exists_extension (GlobalTheory.AdelicU.splitPrime τ) v (τ : E →+* Fv F v)
    (GlobalTheory.AdelicU.valued_apply_eq_valuation τ)
  obtain ⟨ψ, hψc, hψ, -⟩ := exists_extension v (GlobalTheory.AdelicU.splitPrime τ)
    ((algebraMap E _).comp (algebraMap F E)) fun a =>
      (ReciprocityTheory.Aut.adic_valued_algebraMap _ _).trans ((GlobalTheory.AdelicU.valued_apply_eq_valuation τ _).symm.trans
        (GlobalTheory.AdelicU.valued_apply_algebraMap τ a))
  have hid : φ ∘ ψ = id := (HeightOneSpectrum.denseRange_algebraMap F v).equalizer (hφc.comp hψc) continuous_id
    (funext fun a => ((congrArg φ (hψ a)).trans (hφ _)).trans (τ.commutes a))
  let e := RingEquiv.ofBijective φ ⟨φ.injective, fun y => ⟨ψ y, congrFun hid y⟩⟩
  refine ⟨e, hφ, hφv, hφc, continuous_of_valued_eq (v.valuedAdicCompletion_surjective F) e.symm.toRingHom fun y => ?_⟩
  exact (hφv _).symm.trans (congrArg _ (e.apply_symm_apply y))

end GlobalTheory.SplitCompletion
