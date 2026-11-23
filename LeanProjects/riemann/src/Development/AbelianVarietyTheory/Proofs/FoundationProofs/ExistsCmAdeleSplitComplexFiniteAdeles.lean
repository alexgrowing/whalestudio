import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValHalfInf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousSymmFinite
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

namespace GlobalTheory.Eis.Conv.AdeleCMSplit

open scoped TensorProduct NNReal Matrix in
open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.Eis.Conv.AdeleCMSplit.exists_adele_split : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    ∃ e : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E) ≃+* (InfinitePlace E → ℂ) × FiniteAdeleRing (𝓞 E) E,
      Continuous e.symm ∧
      (∀ x : E, e (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x) =
        (fun w : InfinitePlace E => w.embedding x, algebraMap E (FiniteAdeleRing (𝓞 E) E) x)) ∧
      e (_root_.GlobalTheory.Eis.Conv.halfE F E).1 = (fun _ => 2⁻¹, 1) := by
  intro F E _ _ _ _ _ σ hσ
  obtain ⟨e₁, he₁, -, he₁s⟩ := _root_.GlobalTheory.AdSplit.exists_adele_equiv F E
  choose θ hθ using fun τ => (_root_.GlobalTheory.Mem.VolEmb.existsUnique_infEmb F E σ hσ τ).exists
  have hcm : _root_.GlobalTheory.Mem.Vol.IsCMFam (fun w : InfinitePlace E => w.embedding) := by
    unfold _root_.GlobalTheory.Mem.Vol.IsCMFam
    simp only [InfinitePlace.mk_embedding]
    exact Function.bijective_id
  obtain ⟨e₂, he₂, -, he₂s, -⟩ := _root_.GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ
    (InfinitePlace E) (fun w => w.embedding) (fun w => θ w.embedding) hσ hcm (fun w => hθ _)
  obtain ⟨ι, hι1, hι2, -⟩ := _root_.GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E
  have hιs := _root_.GlobalTheory.AdeleBaseChange.continuous_symm_finite F E ι hι2
  refine ⟨e₁.trans (RingEquiv.prodCongr e₂ ι), ?_, ?_, ?_⟩
  · exact he₁s.comp ((he₂s.comp continuous_fst).prodMk (hιs.comp continuous_snd))
  · intro x
    have h1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x = (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ⊗ₜ[F] x := rfl
    have h2 : e₁ ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ⊗ₜ[F] x) =
        ((1 : InfiniteAdeleRing F) ⊗ₜ[F] x, (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) := by
      refine Prod.ext ?_ ?_
      · rw [(he₁ _).1]; exact Algebra.TensorProduct.map_tmul _ _ _ _
      · rw [(he₁ _).2]; exact Algebra.TensorProduct.map_tmul _ _ _ _
    rw [h1, RingEquiv.trans_apply, h2]
    refine Prod.ext ?_ ?_
    · funext w
      exact (he₂ _ w).trans ((hθ _).1 x)
    · exact hι1 x
  · have h0 : ((_root_.GlobalTheory.Eis.Conv.halfE F E).1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E) =
        ((algebraMap F (InfiniteAdeleRing F) 2⁻¹, (1 : FiniteAdeleRing (𝓞 F) F)) : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)
          ⊗ₜ[F] (1 : E) := rfl
    have h2 : e₁ (((algebraMap F (InfiniteAdeleRing F) 2⁻¹, (1 : FiniteAdeleRing (𝓞 F) F)) :
        _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ⊗ₜ[F] (1 : E)) = ((1 : InfiniteAdeleRing F) ⊗ₜ[F] algebraMap F E 2⁻¹, 1) := by
      refine Prod.ext ?_ ?_
      · rw [(he₁ _).1]
        refine (Algebra.TensorProduct.map_tmul _ _ _ _).trans ?_
        show algebraMap F (InfiniteAdeleRing F) 2⁻¹ ⊗ₜ[F] (1 : E) = _
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul]
      · rw [(he₁ _).2]; exact (Algebra.TensorProduct.map_tmul _ _ _ _).trans (by rfl)
    rw [h0]
    refine (congrArg (RingEquiv.prodCongr e₂ ι) h2).trans ?_
    refine Prod.ext ?_ ?_
    · funext w
      refine ((he₂ ((1 : InfiniteAdeleRing F) ⊗ₜ[F] algebraMap F E 2⁻¹) w).trans
        ((hθ _).1 _)).trans ?_
      simp only [map_inv₀, map_ofNat]
    · exact map_one ι

end GlobalTheory.Eis.Conv.AdeleCMSplit
