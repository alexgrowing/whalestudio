import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace GlobalTheory.TraceDualChar

theorem psi_trivial_on_scaledInt : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
    ∀ z ∈ GlobalTheory.EvAdm.scaledInt F κ a,
      ψ (((0 : InfiniteAdeleRing F), ∑ i, z i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) : AF F) = 1 := by
  intro F _ _ ψ hψ κ _ a _ b hb z hz

  have hrat : ∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
      ψ (((0 : InfiniteAdeleRing F), ∑ i, algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) : AF F) = 1 := by
    intro ξ hξ
    obtain ⟨k, hk⟩ := hb ξ hξ
    set q : F := ∑ i, ξ i * b i with hq
    have e1 : (∑ i, algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) q := by
      rw [hq, map_sum]; simp only [map_mul]
    rw [e1]
    set y : AF F := (((algebraMap F (InfiniteAdeleRing F) q), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F) with hy
    have e2 : (show AF F from ((0 : InfiniteAdeleRing F), algebraMap F (FiniteAdeleRing (𝓞 F) F) q)) + y =
        algebraMap F (AF F) q := by
      rw [hy]
      show (show AF F from ((0 : InfiniteAdeleRing F) + algebraMap F (InfiniteAdeleRing F) q,
        algebraMap F (FiniteAdeleRing (𝓞 F) F) q + 0)) = algebraMap F (AF F) q
      rw [zero_add, add_zero]
      rfl
    have hAt : At (evI F) y := by
      intro u hu
      have hu1 : u.1 = 0 := by
        have : InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
        exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 this
      show (u.1 * algebraMap F (InfiniteAdeleRing F) q, u.2 * 0) = ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))
      rw [hu1, zero_mul, mul_zero]
    have hev : evI F y = mixedEmbedding F q := by
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
      rfl
    have hyv : ψ y = 1 := by
      rw [hψ.2.2 y hAt, hev, GlobalTheory.PsiNontriv.trace_mixedEmbedding, hk]
      rw [show ((((k : ℚ) : ℝ) : ℂ)) = (k : ℂ) by push_cast; ring]
      rw [show -(2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I (-k)
    have h3 := congrArg ψ e2
    rw [AddChar.map_add_eq_mul, hyv, mul_one, hψ.2.1] at h3
    exact h3

  by_contra hne
  set G : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun z =>
    ψ (((0 : InfiniteAdeleRing F), ∑ i, z i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) : AF F) with hG
  have hGc : Continuous G := by
    refine hψ.1.comp ?_
    refine Continuous.prodMk continuous_const ?_
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
  have hU : IsOpen ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∩ G ⁻¹' {1}ᶜ) :=
    (GlobalTheory.EvAdm.isOpen_scaledInt a).inter (isOpen_compl_singleton.preimage hGc)
  have hd : DenseRange (fun ξ : κ → F => fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) :=
    DenseRange.piMap fun _ => GlobalTheory.AdeleCharTwist.denseRange_fin
  obtain ⟨ξ, hξ1, hξ2⟩ := hd.exists_mem_open hU ⟨z, hz, hne⟩
  exact hξ2 (hrat ξ hξ1)

end GlobalTheory.TraceDualChar
