import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsResRing

noncomputable section

namespace GlobalTheory.Core.Rk.RapidInt

open scoped TensorProduct ENNReal NNReal ComplexConjugate Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Cont GlobalTheory.GaugeEx GlobalTheory.Core.Rk.NSing
open NumberField.mixedEmbedding
open scoped Classical

section Mixed

variable (F : Type) [Field F] [NumberField F]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem norm_toMixed_le (y : InfiniteAdeleRing F) :
    ‖InfiniteAdeleRing.ringEquiv_mixedSpace F y‖ ≤ ∑ v, ‖y v‖ := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Prod.norm_def]
  have hS : 0 ≤ ∑ v, ‖y v‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine max_le ((pi_norm_le_iff_of_nonneg hS).2 fun v => ?_) ((pi_norm_le_iff_of_nonneg hS).2 fun v => ?_)
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).norm_map_of_map_zero (map_zero _)]
    exact Finset.single_le_sum (f := fun w => ‖y w‖) (fun w _ => norm_nonneg _) (Finset.mem_univ v.1)
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v.1).norm_map_of_map_zero (map_zero _)]
    exact Finset.single_le_sum (f := fun w => ‖y w‖) (fun w _ => norm_nonneg _) (Finset.mem_univ v.1)

end Mixed

section Tup

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (M n : ℕ)

def crdTup : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₗ[Ainf F] (Fin n → Fin M → Fin d → Ainf F) :=
  LinearEquiv.piCongrRight fun _ => LinearEquiv.piCongrRight fun _ =>
    (Algebra.TensorProduct.basis (Ainf F) b).equivFun

def mixTup : (Fin n → Fin M → Fin d → Ainf F) ≃+ (Fin n → Fin M → Fin d → mixedSpace F) :=
  AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ =>
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv

theorem continuous_crdTup : Continuous (crdTup F E b M n) :=
  IsModuleTopology.continuous_of_linearMap (crdTup F E b M n).toLinearMap

theorem continuous_crdTup_symm : Continuous (crdTup F E b M n).symm :=
  IsModuleTopology.continuous_of_linearMap (crdTup F E b M n).symm.toLinearMap

theorem continuous_mixTup : Continuous (mixTup F M n (d := d)) :=
  continuous_pi fun a => continuous_pi fun i => continuous_pi fun k =>
    (continuous_toMixed F).comp ((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply a)))

theorem continuous_mixTup_symm : Continuous (mixTup F M n (d := d)).symm :=
  continuous_pi fun a => continuous_pi fun i => continuous_pi fun k =>
    (continuous_ofMixed F).comp ((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply a)))

def tupEquiv : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (Fin n → Fin M → Fin d → mixedSpace F) where
  toAddEquiv := (crdTup F E b M n).toAddEquiv.trans (mixTup F M n)
  continuous_toFun := (continuous_mixTup F M n).comp (continuous_crdTup F E b M n)
  continuous_invFun := (continuous_crdTup_symm F E b M n).comp (continuous_mixTup_symm F M n)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2000 in
theorem norm_tupEquiv_le (X : Fin n → Fin M → Ainf F ⊗[F] E) : ‖tupEquiv F E b M n X‖ ≤ sizeTup b X := by
  have h0 : ∀ a i k v, 0 ≤ ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v‖ := fun _ _ _ _ => norm_nonneg _
  have hS : 0 ≤ sizeTup b X := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun v _ => h0 a i k v
  refine (pi_norm_le_iff_of_nonneg hS).2 fun a => (pi_norm_le_iff_of_nonneg hS).2 fun i =>
    (pi_norm_le_iff_of_nonneg hS).2 fun k => ?_
  change ‖InfiniteAdeleRing.ringEquiv_mixedSpace F ((Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k)‖ ≤ _
  refine (norm_toMixed_le F _).trans ?_
  calc ∑ v, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v‖ ≤ sizeInf b (X a i) :=
        Finset.single_le_sum (f := fun k => ∑ v, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v‖)
          (fun k _ => Finset.sum_nonneg fun v _ => h0 a i k v) (Finset.mem_univ k)
    _ ≤ ∑ i, sizeInf b (X a i) :=
        Finset.single_le_sum (f := fun i => sizeInf b (X a i))
          (fun i _ => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun v _ => h0 a i k v) (Finset.mem_univ i)
    _ ≤ sizeTup b X :=
        Finset.single_le_sum (f := fun a => ∑ i, sizeInf b (X a i))
          (fun a _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun v _ => h0 a i k v)
          (Finset.mem_univ a)

end Tup

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2000 in

theorem integrable_of_rapidDecay : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (M n : ℕ) (μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)), μi.IsAddHaarMeasure →
    ∀ Φi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φi → RapidDecay b Φi → Integrable Φi μi := by
  intro F E _ _ _ _ _ d b M n μi hμ Φi hc hr
  set e := tupEquiv F E b M n with he
  have hmap : (μi.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μi e
  set N : ℕ := Module.finrank ℝ (Fin n → Fin M → Fin d → mixedSpace F) + 1 with hN
  have hint := integrable_one_add_norm (μ := μi.map e) (r := (N : ℝ)) (by rw [hN]; push_cast; linarith)
  obtain ⟨C, hC⟩ := hr N
  have hbd : ∀ X, ‖Φi X‖ ≤ C * (1 + ‖e X‖) ^ (-(N : ℝ)) := by
    intro X
    have h1 : ‖e X‖ ≤ sizeTup b X := norm_tupEquiv_le F E b M n X
    have h2 : 0 ≤ ‖e X‖ := norm_nonneg _
    have hs : 0 < 1 + sizeTup b X := by linarith
    have hw : 0 < 1 + ‖e X‖ := by linarith
    have hC0 : 0 ≤ C := le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg hs.le _)) (hC X)
    rw [Real.rpow_neg hw.le, Real.rpow_natCast, ← div_eq_mul_inv]
    have h3 : ‖Φi X‖ ≤ C / (1 + sizeTup b X) ^ N := by
      rw [le_div_iff₀ (pow_pos hs _)]; exact hC X
    exact h3.trans (div_le_div_of_nonneg_left hC0 (pow_pos hw _) (pow_le_pow_left₀ hw.le (by linarith) _))
  have hg : Integrable (Φi ∘ e.symm) (μi.map e) := by
    refine (hint.const_mul C).mono' (hc.comp e.symm.continuous).aestronglyMeasurable (ae_of_all _ fun w => ?_)
    have := hbd (e.symm w)
    simpa using this
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  rw [hemb.integrable_map_iff] at hg
  simpa [Function.comp_def] using hg

end GlobalTheory.Core.Rk.RapidInt
