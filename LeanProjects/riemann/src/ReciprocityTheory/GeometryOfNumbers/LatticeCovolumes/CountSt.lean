import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountZSt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidSt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStC

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder
open MeasureTheory

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def HermFam.IsConjInv (h : HermFam K V) : Prop :=
  ∀ (σ : K →+* ℂ) (x y : V),
    h.form (ComplexEmbedding.conjugate σ) x y = starRingEnd ℂ (h.form σ x y)

def smallVec (h : HermFam K V) (E : Submodule (𝓞 K) V) (R : ℝ) : Set V :=
  {x | x ∈ E ∧ ∀ σ, h.nrm σ x ≤ R}

theorem nrm_conj (h : HermFam K V) (hinv : h.IsConjInv) (σ : K →+* ℂ) (x : V) :
    h.nrm (ComplexEmbedding.conjugate σ) x = h.nrm σ x := by
  unfold HermFam.nrm
  rw [hinv σ x x, Complex.conj_re]

theorem nrm_eq_nrm_embedding (h : HermFam K V) (hinv : h.IsConjInv) (σ : K →+* ℂ) (x : V) :
    h.nrm σ x = h.nrm (InfinitePlace.mk σ).embedding x := by
  rcases InfinitePlace.embedding_mk_eq σ with h1 | h1 <;> rw [h1]
  exact (nrm_conj h hinv σ x).symm

open scoped Classical in
theorem mem_image_of_mem_ellS (h : HermFam K V) (hinv : h.IsConjInv) {E : Submodule (𝓞 K) V}
    {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) {R : ℝ} (hR : 0 ≤ R) {y}
    (hy : y ∈ ellS h v R ∩ (latE hv.2.1 E : Set _)) :
    y ∈ crdEmb hv.2.1 '' smallVec h E R := by
  obtain ⟨⟨hyR, hyC⟩, hyL⟩ := hy
  have hyL' : y ∈ E.toAddSubgroup.map (crdEmb hv.2.1) := hyL
  obtain ⟨x, hxE, rfl⟩ := AddSubgroup.mem_map.1 hyL'
  have hxs : x ∈ Submodule.span K (Set.range v) := hv.2.2 hxE

  have hexp : ∀ (σ : K →+* ℂ) (c : Fin r → K), h.form σ (∑ i, c i • v i) (∑ j, c j • v j) =
      ∑ i, ∑ j, starRingEnd ℂ (σ (c i)) * h.form σ (v i) (v j) * σ (c j) := by
    intro σ c
    have hr : ∀ y, h.form σ y (∑ j, c j • v j) = ∑ j, σ (c j) * h.form σ y (v j) := by
      intro y
      have e := map_sum (AddMonoidHom.mk' (h.form σ y) (h.add_right σ y)) (fun j => c j • v j)
        Finset.univ
      simp only [AddMonoidHom.mk'_apply, h.smul_right] at e
      exact e
    have hl : ∀ y, h.form σ (∑ i, c i • v i) y =
        ∑ i, starRingEnd ℂ (σ (c i)) * h.form σ (v i) y := by
      intro y
      rw [← h.conj_symm σ y, hr y, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, h.conj_symm]
    rw [hl]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hr, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hreal : ∀ w : {w : InfinitePlace K // w.IsReal},
      qR (gramR h v w) (fun i => (crdEmb hv.2.1 x i).1 w) = (h.form w.1.embedding x x).re := by
    intro w
    have hy : ∀ a : K, (((mixedEmbedding K a).1 w : ℝ) : ℂ) = w.1.embedding a := fun a => by
      simp [mixedEmbedding]
    symm
    conv_lhs => rw [← sum_crd hv.2.1 hxs]
    rw [hexp, Complex.re_sum]
    unfold qR
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [crdEmb, AddMonoidHom.coe_mk, ZeroHom.coe_mk, gramR, HermFam.gram, Matrix.map_apply,
      Matrix.of_apply]
    rw [← hy, ← hy, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
    ring
  have hcplx : ∀ w : {w : InfinitePlace K // w.IsComplex},
      qC (h.gram w.1.embedding v) (fun i => (crdEmb hv.2.1 x i).2 w) =
        (h.form w.1.embedding x x).re := by
    intro w
    symm
    conv_lhs => rw [← sum_crd hv.2.1 hxs]
    rw [hexp]
    unfold qC
    congr 1
  refine ⟨x, ⟨hxE, fun σ => ?_⟩, rfl⟩
  rw [nrm_eq_nrm_embedding h hinv σ x]
  have hre : (h.form (InfinitePlace.mk σ).embedding x x).re ≤ R ^ 2 := by
    rcases (InfinitePlace.mk σ).isReal_or_isComplex with hw | hw
    · exact (hreal ⟨_, hw⟩).symm.trans_le (hyR ⟨_, hw⟩)
    · exact (hcplx ⟨_, hw⟩).symm.trans_le (hyC ⟨_, hw⟩)
  unfold HermFam.nrm
  calc Real.sqrt (h.form (InfinitePlace.mk σ).embedding x x).re ≤ Real.sqrt (R ^ 2) :=
        Real.sqrt_le_sqrt hre
    _ = R := Real.sqrt_sq hR

theorem det_gram_conj_re (h : HermFam K V) (hinv : h.IsConjInv) (σ : K →+* ℂ) {r : ℕ}
    (v : Fin r → V) :
    (h.gram (ComplexEmbedding.conjugate σ) v).det.re = (h.gram σ v).det.re := by
  have hg : h.gram (ComplexEmbedding.conjugate σ) v = (h.gram σ v).map (starRingEnd ℂ) := by
    ext i j
    simp only [HermFam.gram, Matrix.map_apply, Matrix.of_apply]
    exact hinv σ (v i) (v j)
  rw [hg, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.conj_re]

end ReciprocityTheory.GeometryOfNumbersTheory
