import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchHalfTurn

theorem leftMulMatrix_pi' {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    [∀ i, DecidableEq (κ i)] (b : ∀ i, Module.Basis (κ i) R (A i)) (x : ∀ i, A i) :
    Algebra.leftMulMatrix (Pi.basis b) x =
      Matrix.blockDiagonal' fun i => Algebra.leftMulMatrix (b i) (x i) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr, Matrix.blockDiagonal'_apply]
  by_cases h : i = j
  · subst h
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  · simp [h]

theorem trace_pi' {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)]
    [∀ i, Module.Finite R (A i)] (x : ∀ i, A i) :
    Algebra.trace R _ x = ∑ i, Algebra.trace R (A i) (x i) := by
  let b := fun i => Module.Free.chooseBasis R (A i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), leftMulMatrix_pi', Matrix.trace_blockDiagonal']
  exact Finset.sum_congr rfl fun i _ => (Algebra.trace_eq_matrix_trace (b i) (x i)).symm

def cst {F : Type} [Field F] (v : InfinitePlace F) : v.Completion :=
  if v.IsReal then (2 : v.Completion)⁻¹ else (4 : v.Completion)⁻¹

def sgl {F : Type} [Field F] (v : InfinitePlace F) (c : v.Completion) : InfiniteAdeleRing F :=
  Pi.single (M := fun w : InfinitePlace F => w.Completion) v c

theorem sgl_apply_self {F : Type} [Field F] (v : InfinitePlace F) (c : v.Completion) :
    sgl v c v = c := Pi.single_eq_same (M := fun w : InfinitePlace F => w.Completion) v c

theorem sgl_apply_ne {F : Type} [Field F] {v w : InfinitePlace F} (c : v.Completion) (h : w ≠ v) :
    sgl v c w = 0 := Pi.single_eq_of_ne (M := fun w : InfinitePlace F => w.Completion) h c

theorem fst_toMixed {F : Type} [Field F] (y : InfiniteAdeleRing F) (w : {w : InfinitePlace F // w.IsReal}) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F y).1 w =
      InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (y w.1) := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]

theorem snd_toMixed {F : Type} [Field F] (y : InfiniteAdeleRing F) (w : {w : InfinitePlace F // w.IsComplex}) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F y).2 w =
      InfinitePlace.Completion.extensionEmbedding w.1 (y w.1) := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]

theorem trace_sgl_cst (F : Type) [Field F] [NumberField F] (v : InfinitePlace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F (sgl v (cst v))) = 1 / 2 := by
  rw [Algebra.trace_prod_apply, trace_pi', trace_pi']
  simp only [fst_toMixed, snd_toMixed, Algebra.trace_self_apply, Algebra.trace_complex_apply]
  rcases v.isReal_or_isComplex with hv | hv
  · rw [Finset.sum_eq_single ⟨v, hv⟩, Finset.sum_eq_zero]
    · rw [sgl_apply_self, cst, if_pos hv, map_inv₀, map_ofNat]; norm_num
    · intro w _
      rw [sgl_apply_ne _ (fun h => ?_), map_zero, Complex.zero_re, mul_zero]
      exact (InfinitePlace.not_isComplex_iff_isReal.2 hv) (h ▸ w.2)
    · intro w _ hw
      rw [sgl_apply_ne _ (fun h => hw (Subtype.ext h)), map_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero, Finset.sum_eq_single ⟨v, hv⟩]
    · rw [sgl_apply_self, cst, if_neg (InfinitePlace.not_isReal_iff_isComplex.2 hv), map_inv₀, map_ofNat]
      norm_num [Complex.inv_re, Complex.normSq]
    · intro w _ hw
      rw [sgl_apply_ne _ (fun h => hw (Subtype.ext h)), map_zero, Complex.zero_re, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro w _
      rw [sgl_apply_ne _ (fun h => ?_), map_zero]
      exact (InfinitePlace.not_isReal_iff_isComplex.2 hv) (h ▸ w.2)

theorem mul_sgl {F : Type} [Field F] (y : InfiniteAdeleRing F) (v : InfinitePlace F) (c : v.Completion) :
    y * sgl v c = sgl v (y v * c) := by
  funext w
  show y w * sgl v c w = sgl v (y v * c) w
  by_cases h : w = v
  · subst h; rw [sgl_apply_self, sgl_apply_self]
  · rw [sgl_apply_ne _ h, sgl_apply_ne _ h, mul_zero]

theorem norm_toMixed_le' (F : Type) [Field F] [NumberField F] (y : InfiniteAdeleRing F) :
    ‖InfiniteAdeleRing.ringEquiv_mixedSpace F y‖ ≤ ∑ v, ‖y v‖ := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Prod.norm_def]
  have hS : 0 ≤ ∑ v, ‖y v‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine max_le ((pi_norm_le_iff_of_nonneg hS).2 fun v => ?_) ((pi_norm_le_iff_of_nonneg hS).2 fun v => ?_)
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).norm_map_of_map_zero (map_zero _)]
    exact Finset.single_le_sum (f := fun w => ‖y w‖) (fun w _ => norm_nonneg _) (Finset.mem_univ v.1)
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v.1).norm_map_of_map_zero (map_zero _)]
    exact Finset.single_le_sum (f := fun w => ‖y w‖) (fun w _ => norm_nonneg _) (Finset.mem_univ v.1)

theorem sum_norm_sgl {F : Type} [Field F] [NumberField F] (v : InfinitePlace F) (c : v.Completion) :
    ∑ w, ‖sgl v c w‖ = ‖c‖ := by
  rw [Finset.sum_eq_single v, sgl_apply_self]
  · intro w _ hw; rw [sgl_apply_ne _ hw, norm_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem halfturn : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (ι : Type) [Fintype ι], ∃ C : ℝ,
    ∀ x : ι → AF F, 0 < ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ →
      ∃ (i : ι) (a : Ainf F), ψ (x i * GlobalTheory.HeisSchA.mk a 0) = -1 ∧
      ‖InfiniteAdeleRing.ringEquiv_mixedSpace F a‖ * ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ ≤ C := by
  intro F _ _ ψ hψ ι _
  refine ⟨(∑ w : InfinitePlace F, ‖cst w‖) * ((Fintype.card ι : ℝ) * Fintype.card (InfinitePlace F)),
    fun x hS => ?_⟩
  set S := ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ with hSdef
  have hne : (Finset.univ : Finset (ι × InfinitePlace F)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    by_contra h
    rw [not_nonempty_iff] at h
    have h0 : S = 0 := by
      rw [hSdef, ← Fintype.sum_prod_type' (f := fun i v => ‖(x i).1 v‖), Finset.univ_eq_empty,
        Finset.sum_empty]
    linarith
  obtain ⟨⟨i, v⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (ι × InfinitePlace F))
    (fun p => ‖(x p.1).1 p.2‖) hne
  have hle : S ≤ ((Fintype.card ι : ℝ) * Fintype.card (InfinitePlace F)) * ‖(x i).1 v‖ := by
    calc S ≤ ∑ _j : ι, ∑ _w : InfinitePlace F, ‖(x i).1 v‖ :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun w _ => hmax ⟨j, w⟩ (Finset.mem_univ _)
      _ = _ := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
  have hm : 0 < ‖(x i).1 v‖ := by
    by_contra h
    push_neg at h
    have : S ≤ 0 := hle.trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) h)
    linarith
  have hx0 : (x i).1 v ≠ 0 := norm_pos_iff.1 hm
  refine ⟨i, sgl v (cst v * ((x i).1 v)⁻¹), ?_, ?_⟩
  · have hprod : x i * GlobalTheory.HeisSchA.mk (sgl v (cst v * ((x i).1 v)⁻¹)) 0 =
        GlobalTheory.HeisSchA.mk (sgl v (cst v)) 0 := by
      show ((x i).1 * sgl v _, (x i).2 * 0) = (sgl v (cst v), 0)
      rw [mul_sgl, mul_zero, mul_left_comm, mul_inv_cancel₀ hx0, mul_one]
    rw [hprod, hψ.2.2 _ (GlobalTheory.HeisSchA.at_mk _)]
    have hev : evI F (GlobalTheory.HeisSchA.mk (sgl v (cst v)) 0) =
        InfiniteAdeleRing.ringEquiv_mixedSpace F (sgl v (cst v)) := rfl
    rw [hev, trace_sgl_cst]
    have h2 : -(2 * (Real.pi : ℂ) * Complex.I) * (((1 / 2 : ℝ)) : ℂ) = -(Real.pi * Complex.I) := by
      push_cast; ring
    rw [h2, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  · have hnorm : ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (sgl v (cst v * ((x i).1 v)⁻¹))‖ ≤
        ‖cst v‖ / ‖(x i).1 v‖ := by
      refine (norm_toMixed_le' F _).trans (le_of_eq ?_)
      rw [sum_norm_sgl, norm_mul, norm_inv, div_eq_mul_inv]
    have hc : ‖cst v‖ ≤ ∑ w : InfinitePlace F, ‖cst w‖ :=
      Finset.single_le_sum (f := fun w => ‖cst w‖) (fun w _ => norm_nonneg _) (Finset.mem_univ v)
    calc ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (sgl v (cst v * ((x i).1 v)⁻¹))‖ * S
        ≤ (‖cst v‖ / ‖(x i).1 v‖) * (((Fintype.card ι : ℝ) * Fintype.card (InfinitePlace F)) *
            ‖(x i).1 v‖) := mul_le_mul hnorm hle hS.le (by positivity)
      _ = ‖cst v‖ * ((Fintype.card ι : ℝ) * Fintype.card (InfinitePlace F)) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

end GlobalTheory.ArchHalfTurn
