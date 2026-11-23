import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.CharZero

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
private theorem extensionEmbedding_infiniteAdele_algebraMap (F : Type) [Field F] [NumberField F]
    (x : F) (v : InfinitePlace F) :
    InfinitePlace.Completion.extensionEmbedding v ((algebraMap F (InfiniteAdeleRing F) x) v) =
      v.embedding x := by
  simp [InfinitePlace.Completion.extensionEmbedding_coe]

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
private theorem sum_infinitePlace_embedding_eq_trace (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (x : F) :
    ∑ v : InfinitePlace F, v.embedding x = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  let e : InfinitePlace F ≃ (F →+* ℂ) :=
    { toFun := fun v => v.embedding
      invFun := InfinitePlace.mk
      left_inv := fun v => InfinitePlace.mk_embedding v
      right_inv := fun φ => InfinitePlace.embedding_mk_eq_of_isReal
        (IsTotallyReal.complexEmbedding_isReal φ) }
  rw [Fintype.sum_equiv e (fun v => v.embedding x) (fun φ => φ x) (fun _ => rfl)]
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := x)
  rw [← eq_ratCast (algebraMap ℚ ℂ), h]
  convert Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => φ x)
    (fun φ : F →ₐ[ℚ] ℂ => φ x) (fun _ => rfl)

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in

theorem _root_.GlobalTheory.GaugeEx.CharZero.exists_isCharAF :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ ψ, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF F ψ := by
  intro F _ _ _
  let L : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F →+ ℂ := ∑ v : InfinitePlace F,
    (InfinitePlace.Completion.extensionEmbedding v).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun w : InfinitePlace F => w.Completion) v)
  have hLapply : (L : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F → ℂ) = fun a => ∑ v : InfinitePlace F,
      InfinitePlace.Completion.extensionEmbedding v (a v) := by
    ext a
    simp only [L, AddMonoidHom.finset_sum_apply]
    rfl
  have hL : Continuous L := by
    rw [hLapply]
    exact continuous_finset_sum _ fun v _ =>
      (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp
        (continuous_apply v)
  obtain ⟨ψ, hψ, -⟩ := _root_.GlobalTheory.StdAdelicChar.exists_char_of_trace F L hL (fun x => by
    rw [hLapply]
    change ∑ v : InfinitePlace F, InfinitePlace.Completion.extensionEmbedding v
      ((algebraMap F (InfiniteAdeleRing F) x) v) = _
    simp only [extensionEmbedding_infiniteAdele_algebraMap]
    exact sum_infinitePlace_embedding_eq_trace F x)
  exact ⟨ψ, hψ⟩

end GlobalTheory.GaugeEx.CharZero

end
