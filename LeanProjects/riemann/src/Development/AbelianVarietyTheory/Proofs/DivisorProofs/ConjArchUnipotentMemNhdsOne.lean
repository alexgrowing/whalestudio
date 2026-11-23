import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology Filter
open scoped NumberField.AdeleRing

namespace GlobalTheory.InfConj

theorem continuous_mixedSpace_symm (E : Type) [Field E] [NumberField E] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm

def liftMat (E : Type) [Field E] [NumberField E] (a : ℕ)
    (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E a) : Matrix (Fin a) (Fin a) (Ad E) :=
  Matrix.of fun i j => (((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (Y i j), 0) : Ad E)

theorem continuous_liftMat (E : Type) [Field E] [NumberField E] (a : ℕ) : Continuous (liftMat E a) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Continuous.prodMk ((continuous_mixedSpace_symm E).comp ?_) continuous_const
  exact (continuous_apply j).comp (continuous_apply i)

theorem liftMat_zero (E : Type) [Field E] [NumberField E] (a : ℕ) : liftMat E a 0 = 0 := by
  ext i j : 2
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm 0 = 0
    exact map_zero _
  · rfl

theorem liftMat_archMat (E : Type) [Field E] [NumberField E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Ad E))
    (hZ : ∀ i j, (Z i j).2 = 0) : liftMat E a (GroundTheory.Automorphic.CuspidalSpectrum.archMat E a Z) = Z := by
  ext i j : 2
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (InfiniteAdeleRing.ringEquiv_mixedSpace E (Z i j).1) = (Z i j).1
    exact RingEquiv.symm_apply_apply _ _
  · exact (hZ i j).symm

end GlobalTheory.InfConj

namespace GlobalTheory.InfConj

theorem conj_blockEntry_snd (E : Type) [Field E] [NumberField E] (a r : ℕ) (x : GA E a)
    (P : BlockIx a r → Ad E) (hP : ∀ p, (P p).2 = 0) (i j : Fin a) :
    ((((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E))) i j).2 = 0 := by
  let f : Matrix (Fin a) (Fin a) (Ad E) →+* Matrix (Fin a) (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) :=
    (RingHom.snd (InfiniteAdeleRing E) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)).mapMatrix
  have hB : f (GroundTheory.Automorphic.AutomorphicForm.blockEntry P) = 0 := by
    refine Matrix.ext fun k l => ?_
    change (GroundTheory.Automorphic.AutomorphicForm.blockEntry P k l).2 = 0
    unfold GroundTheory.Automorphic.AutomorphicForm.blockEntry
    rw [Matrix.of_apply]
    split_ifs with h
    · exact hP _
    · rfl
  change f (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E))) i j = 0
  rw [map_mul, map_mul, hB, mul_zero, zero_mul]
  rfl

theorem conj_unip_mem_nhds : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (U : Set (GA E a)), U ∈ 𝓝 (1 : GA E a) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : GA E a) (P : BlockIx a r → Ad E), (∀ p, (P p).2 = 0) →
      ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E)))‖ ≤ δ →
      x⁻¹ * unip P * x ∈ U := by
  intro E _ _ a r U hU
  rw [(Units.isInducing_embedProduct (M := Matrix (Fin a) (Fin a) (Ad E))).nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨t, ht, htU⟩ := hU
  let φ : Matrix (Fin a) (Fin a) (Ad E) → Matrix (Fin a) (Fin a) (Ad E) × (Matrix (Fin a) (Fin a) (Ad E))ᵐᵒᵖ :=
    fun Z => (1 + Z, MulOpposite.op (1 - Z))
  have hφ : Continuous φ :=
    (continuous_const.add continuous_id).prodMk (MulOpposite.continuous_op.comp (continuous_const.sub continuous_id))
  have hφ0 : φ (liftMat E a 0) = Units.embedProduct _ (1 : GA E a) := by
    rw [liftMat_zero]
    simp only [φ, add_zero, sub_zero, Units.embedProduct_apply, inv_one, Units.val_one]
  have hnb : (φ ∘ liftMat E a) ⁻¹' t ∈ 𝓝 (0 : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E a) :=
    (hφ.comp (continuous_liftMat E a)).continuousAt.preimage_mem_nhds (by
      rw [Function.comp_apply, hφ0]; exact ht)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnb
  refine ⟨ε / 2, by positivity, fun x P hP hnorm => htU ?_⟩
  set Z := ((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
    GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E)) with hZdef
  have hmem : GroundTheory.Automorphic.CuspidalSpectrum.archMat E a Z ∈ Metric.ball 0 ε := by
    rw [mem_ball_zero_iff]; linarith
  have h1 := hball hmem
  rw [Set.mem_preimage, Function.comp_apply, liftMat_archMat E a Z (conj_blockEntry_snd E a r x P hP)] at h1
  rw [Set.mem_preimage]
  convert h1 using 1
  have hv : ((x⁻¹ * unip P * x : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) = 1 + Z := by
    rw [Units.val_mul, Units.val_mul]
    change ((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * (1 + nilM P) * (x : Matrix (Fin a) (Fin a) (Ad E)) = _
    rw [mul_add, add_mul, mul_one, Units.inv_mul, hZdef]
    rfl
  have hi : ((x⁻¹ * unip P * x : GA E a)⁻¹ : GA E a).val = 1 - Z := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, Units.val_mul, Units.val_mul]
    change ((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * (1 - nilM P) * (x : Matrix (Fin a) (Fin a) (Ad E)) = _
    rw [mul_sub, sub_mul, mul_one, Units.inv_mul, hZdef]
    rfl
  simp only [Units.embedProduct_apply, φ]
  rw [hv, hi]

end GlobalTheory.InfConj
