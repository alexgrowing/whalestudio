import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.RealEisensteinNonneg
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmEtaPeriodLatticeClassPf
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

namespace projectiveLineClassData

open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding UpperHalfPlane
open scoped nonZeroDivisors ComplexConjugate

variable {K : Type} [Field K] [NumberField K]

section Embeddings

omit [NumberField K] in

theorem conjugate_ne (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0) : conjugate σ ≠ σ := by
  obtain ⟨x, hx⟩ := hσ
  intro h
  apply hx
  have h1 := congrArg (fun φ : K →+* ℂ => φ x) h
  simp only [conjugate_coe_eq] at h1
  exact Complex.conj_eq_iff_im.mp h1

theorem eq_or_eq_conjugate (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) (φ : K →+* ℂ) : φ = σ ∨ φ = conjugate σ := by
  classical
  have hcard : Fintype.card (K →+* ℂ) = 2 := by rw [NumberField.Embeddings.card K ℂ, hK]
  have h2 : ({σ, conjugate σ} : Finset (K →+* ℂ)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair (conjugate_ne σ hσ).symm, hcard]
  have : φ ∈ ({σ, conjugate σ} : Finset (K →+* ℂ)) := h2 ▸ Finset.mem_univ φ
  simpa using this

theorem eq_mk (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (w : InfinitePlace K) : w = mk σ := by
  rcases eq_or_eq_conjugate hK σ hσ w.embedding with h | h
  · rw [← mk_embedding w, h]
  · rw [← mk_embedding w, h, mk_conjugate_eq]

theorem place_apply (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (w : InfinitePlace K) (x : K) : w x = ‖σ x‖ := by
  rw [eq_mk hK σ hσ w, apply]

omit [NumberField K] in

theorem isComplex_mk (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0) : IsComplex (mk σ) :=
  isComplex_mk_iff.mpr fun h => conjugate_ne σ hσ (ComplexEmbedding.isReal_iff.mp h)

theorem abs_norm_eq (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (x : K) : |((Algebra.norm ℚ x : ℚ) : ℝ)| = ‖σ x‖ ^ 2 := by
  classical
  have h := prod_eq_abs_norm x
  have hall : ∀ w : InfinitePlace K, w = mk σ := eq_mk hK σ hσ
  rw [Finset.prod_eq_single_of_mem (mk σ) (Finset.mem_univ _)
    (fun w _ hw => absurd (hall w) hw)] at h
  have hm : mult (mk σ) = 2 := by
    rw [mult, if_neg (not_isReal_iff_isComplex.mpr (isComplex_mk σ hσ))]
  rw [hm, apply] at h
  rw [h, Rat.cast_abs]

theorem mem_torsion_of (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (u : (𝓞 K)ˣ) : u ∈ Units.torsion K := by
  rw [Units.mem_torsion]
  intro w
  rw [place_apply hK σ hσ]
  have h := abs_norm_eq hK σ hσ (u : K)
  rw [← Rat.cast_abs, Units.norm K u, Rat.cast_one] at h
  have h0 : 0 ≤ ‖σ (u : K)‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖σ (u : K)‖ - 1), sq_nonneg (‖σ (u : K)‖ + 1)]

theorem natCard_units (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0) :
    Nat.card (𝓞 K)ˣ = Units.torsionOrder K := by
  have htop : Units.torsion K = ⊤ := eq_top_iff.mpr fun u _ => mem_torsion_of hK σ hσ u
  rw [Units.torsionOrder, htop, Subgroup.card_top]

end Embeddings

section Covolume

open EtaPeriodLatticeClass

def embPair (σ : K →+* ℂ) : Fin 2 → (K →ₐ[ℚ] ℂ) :=
  ![σ.toRatAlgHom, (conjugate σ).toRatAlgHom]

theorem embPair_bijective (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) : Function.Bijective (embPair σ) := by
  rw [Fintype.bijective_iff_injective_and_card, AlgHom.card, hK, Fintype.card_fin]
  have hne : σ.toRatAlgHom ≠ (conjugate σ).toRatAlgHom := fun h =>
    conjugate_ne σ hσ (RingHom.ext fun x => by
      have := DFunLike.congr_fun h x
      simpa [RingHom.toRatAlgHom_apply] using this.symm)
  refine ⟨fun i j hij => ?_, rfl⟩
  match i, j with
  | 0, 0 => rfl
  | 0, 1 => exact absurd hij hne
  | 1, 0 => exact absurd hij.symm hne
  | 1, 1 => rfl

def embEquiv (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0) :
    Fin 2 ≃ (K →ₐ[ℚ] ℂ) :=
  Equiv.ofBijective _ (embPair_bijective hK σ hσ)

theorem normSq_mul_det (c a b τ : ℂ) (ha : c * a = 1) (hb : c * b = τ) :
    ((‖c‖ ^ 2 : ℝ) : ℂ) * (a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b) =
      -(2 * τ.im * Complex.I) := by
  have hcb : (starRingEnd ℂ) c * (starRingEnd ℂ) b = (starRingEnd ℂ) τ := by
    rw [← map_mul, hb]
  have hca : (starRingEnd ℂ) c * (starRingEnd ℂ) a = 1 := by
    rw [← map_mul, ha, map_one]
  have hn : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * (starRingEnd ℂ) c := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsub : τ - (starRingEnd ℂ) τ = ((2 * τ.im : ℝ) : ℂ) * Complex.I := Complex.sub_conj τ
  rw [hn]
  push_cast at hsub
  linear_combination ((starRingEnd ℂ) c * (starRingEnd ℂ) b) * ha + hcb - (c * b) * hca - hb - hsub

end Covolume

section Covolume2

open EtaPeriodLatticeClass

theorem discr_neg_and_absNorm_mul (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) (I : FractionalIdeal (𝓞 K)⁰ K) (τ : ℍ) (c : ℂ) (hc : c ≠ 0)
    (himg : (fun z => c * z) '' (σ '' (I : Set K)) = latticeOf (τ : ℂ)) :
    (discr K : ℝ) < 0 ∧
      ((FractionalIdeal.absNorm I : ℚ) : ℝ) * ‖c‖ ^ 2 = 2 * τ.im / Real.sqrt |(discr K : ℝ)| := by
  classical
  have hmem : ∀ x : K, x ∈ I → c * σ x ∈ latticeOf (τ : ℂ) := fun x hx => by
    rw [← himg]; exact ⟨σ x, ⟨x, hx, rfl⟩, rfl⟩
  have hpre : ∀ z ∈ latticeOf (τ : ℂ), ∃ x ∈ I, c * σ x = z := by
    intro z hz
    rw [← himg] at hz
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
    exact ⟨x, hx, rfl⟩
  obtain ⟨α, hαI, hα⟩ := hpre 1 (mem_latticeOf.mpr ⟨1, 0, by simp⟩)
  obtain ⟨β, hβI, hβ⟩ := hpre τ (mem_latticeOf.mpr ⟨0, 1, by simp⟩)
  have hcoord : ∀ x ∈ I, ∃ m n : ℤ, x = m * α + n * β := by
    intro x hx
    obtain ⟨m, n, hmn⟩ := mem_latticeOf.mp (hmem x hx)
    refine ⟨m, n, σ.injective (mul_left_cancel₀ hc ?_)⟩
    rw [hmn, map_add, map_mul, map_mul, map_intCast, map_intCast]
    linear_combination (-(m : ℂ)) * hα - (n : ℂ) * hβ
  have hind : ∀ m n : ℤ, (m : K) * α + n * β = 0 → m = 0 ∧ n = 0 := by
    intro m n h
    have h2 := congrArg (fun x => c * σ x) h
    simp only [map_add, map_mul, map_intCast, map_zero, mul_zero] at h2
    have h3 : (m : ℂ) + n * (τ : ℂ) = ((0 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * (τ : ℂ) := by
      push_cast
      linear_combination h2 - (m : ℂ) * hα - (n : ℂ) * hβ
    exact coord_unique h3
  let v : Fin 2 → (I : Submodule (𝓞 K) K) := ![⟨α, hαI⟩, ⟨β, hβI⟩]
  have hli : LinearIndependent ℤ v := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    apply hind s t
    have := congrArg (fun y : (I : Submodule (𝓞 K) K) => (y : K)) hst
    simpa [zsmul_eq_mul] using this
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨m, n, hxmn⟩ := hcoord x hx
    have h0 : v 0 ∈ Submodule.span ℤ (Set.range v) := Submodule.subset_span ⟨0, rfl⟩
    have h1 : v 1 ∈ Submodule.span ℤ (Set.range v) := Submodule.subset_span ⟨1, rfl⟩
    have := Submodule.add_mem _ (Submodule.smul_mem _ m h0) (Submodule.smul_mem _ n h1)
    convert this using 1
    ext
    simp [v, zsmul_eq_mul, hxmn]
  let bJ : Module.Basis (Fin 2) ℤ (I : Submodule (𝓞 K) K) := Module.Basis.mk hli hsp
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, hK]
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) :=
    (RingOfIntegers.basis K).reindex (Fintype.equivFinOfCardEq hcard)
  have habs := FractionalIdeal.abs_det_basis_change b I bJ
  set b₀ := b.localizationLocalization ℚ ℤ⁰ K
  set w : Fin 2 → K := (↑) ∘ bJ with hw
  have hw0 : w 0 = α := by simp [hw, bJ, v]
  have hw1 : w 1 = β := by simp [hw, bJ, v]
  have hdisc := Algebra.discr_of_matrix_vecMul (⇑b₀) (b₀.toMatrix w)
  rw [Module.Basis.toMatrix_map_vecMul, ← Module.Basis.det_apply, Algebra.discr_localizationLocalization ℤ ℤ⁰ K b,
    NumberField.discr_eq_discr K b] at hdisc
  have hemb := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ w (embEquiv hK σ hσ)
  rw [Matrix.det_fin_two] at hemb
  simp only [Algebra.embeddingsMatrixReindex, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm, Algebra.embeddingsMatrix_apply, embEquiv,
    Equiv.ofBijective_apply, embPair, Matrix.cons_val_zero, Matrix.cons_val_one,
    RingHom.toRatAlgHom_apply, hw0, hw1, conjugate_coe_eq] at hemb
  have hX := normSq_mul_det c (σ α) (σ β) τ hα hβ
  rw [UpperHalfPlane.coe_im] at hX
  have hq : Algebra.discr ℚ w = (FractionalIdeal.absNorm I) ^ 2 * (discr K : ℚ) := by
    rw [hdisc, ← sq_abs, habs]
    simp
  have hC : ((‖c‖ ^ 2 : ℝ) : ℂ) ^ 2 *
      ((((FractionalIdeal.absNorm I : ℚ) : ℝ) : ℂ) ^ 2 * (((discr K : ℤ) : ℝ) : ℂ)) =
        ((-(4 * τ.im ^ 2) : ℝ) : ℂ) := by
    have h1 : ((‖c‖ ^ 2 : ℝ) : ℂ) ^ 2 *
        (σ α * (starRingEnd ℂ) (σ β) - (starRingEnd ℂ) (σ α) * σ β) ^ 2 =
          ((-(4 * τ.im ^ 2) : ℝ) : ℂ) := by
      rw [← mul_pow, hX]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [← h1, ← hemb, hq]
    simp only [map_mul, map_pow, eq_ratCast, Rat.cast_intCast]
    push_cast
    ring
  have hR : (‖c‖ ^ 2) ^ 2 * (((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ 2 * (discr K : ℝ)) =
      -(4 * τ.im ^ 2) := by
    have := Complex.ofReal_injective (by push_cast at hC ⊢; exact hC :
      (((‖c‖ ^ 2) ^ 2 * (((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ 2 * (discr K : ℝ)) : ℝ) : ℂ) =
        ((-(4 * τ.im ^ 2) : ℝ) : ℂ))
    exact this
  have hy := τ.im_pos
  have hN : 0 ≤ ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg I
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hD : (discr K : ℝ) < 0 := by
    by_contra h
    replace h := not_lt.mp h
    have : 0 ≤ (‖c‖ ^ 2) ^ 2 * (((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ 2 * (discr K : ℝ)) := by
      positivity
    nlinarith
  refine ⟨hD, ?_⟩
  have hsq : Real.sqrt |(discr K : ℝ)| ^ 2 = -(discr K : ℝ) := by
    rw [Real.sq_sqrt (abs_nonneg _), abs_of_neg hD]
  have hspos : 0 < Real.sqrt |(discr K : ℝ)| := Real.sqrt_pos.mpr (abs_pos.mpr hD.ne)
  have key : Real.sqrt |(discr K : ℝ)| * (((FractionalIdeal.absNorm I : ℚ) : ℝ) * ‖c‖ ^ 2) =
      2 * τ.im := by
    have h1 : (Real.sqrt |(discr K : ℝ)| * (((FractionalIdeal.absNorm I : ℚ) : ℝ) * ‖c‖ ^ 2)) ^ 2 =
        (2 * τ.im) ^ 2 := by
      rw [mul_pow, hsq]
      linear_combination (-1 : ℝ) * hR
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h1
  rw [eq_div_iff hspos.ne']
  linarith [key]

end Covolume2

end projectiveLineClassData

end GroundTheory.Heights₂.Theta
