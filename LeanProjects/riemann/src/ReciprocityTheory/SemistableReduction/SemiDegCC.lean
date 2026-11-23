import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement
import ReciprocityTheory.SemistableReduction.SemiDegCB
import Lemmata.MiscLemmasR.Imports

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField Matrix
open scoped nonZeroDivisors

theorem hermForm_smul_smul {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a b : K) (u w : Fin r → K) : S.h (a • u) (b • w) = S.c a * b * S.h u w := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermForm_sum_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {ι : Type} (s : Finset ι) (u : ι → Fin r → K) (w : Fin r → K) :
    S.h (∑ i ∈ s, u i) w = ∑ i ∈ s, S.h (u i) w := by
  simp only [HermForm.h, Finset.sum_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

theorem hermForm_conj {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (u w : Fin r → K) : S.c (S.h u w) = S.h w u := by
  simp only [HermForm.h, map_sum, map_mul, S.c_invol, S.G_herm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def intInv {K : Type} [Field K] [NumberField K] (c : K →+* K) : 𝓞 K →+* 𝓞 K :=
  RingOfIntegers.mapRingHom c

theorem intInv_coe {K : Type} [Field K] [NumberField K] (c : K →+* K) (a : 𝓞 K) :
    algebraMap (𝓞 K) K (intInv c a) = c (algebraMap (𝓞 K) K a) := rfl

theorem mem_one_map {K : Type} [Field K] [NumberField K] (c : K →+* K) {x : K}
    (hx : x ∈ (1 : Submodule (𝓞 K) K)) : c x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.mp hx
  exact Submodule.mem_one.mpr ⟨intInv c y, intInv_coe c y⟩

def cImage {K : Type} [Field K] [NumberField K] (c : K →+* K) (C : Submodule (𝓞 K) K) :
    Submodule (𝓞 K) K := Bl.ThirdBlockLemmaC.goal1 c C

theorem mem_cImage {K : Type} [Field K] [NumberField K] (c : K →+* K) (C : Submodule (𝓞 K) K)
    {x : K} : x ∈ cImage c C ↔ c x ∈ C := Iff.rfl

theorem cImage_fg {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (C : Submodule (𝓞 K) K) (hC : C.FG) : (cImage c C).FG := by
  haveI : RingHomSurjective (intInv c) :=
    ⟨fun y => ⟨intInv c y, by
      apply RingOfIntegers.ext
      show algebraMap (𝓞 K) K (intInv c (intInv c y)) = algebraMap (𝓞 K) K y
      rw [intInv_coe, intInv_coe, hc]⟩⟩
  let f : K →ₛₗ[intInv c] K :=
    { toFun := c
      map_add' := map_add c
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, intInv_coe] }
  have h : cImage c C = C.map f := by
    ext x
    rw [mem_cImage, Submodule.mem_map]
    constructor
    · intro hx
      exact ⟨c x, hx, hc x⟩
    · rintro ⟨y, hy, rfl⟩
      show c (c y) ∈ C
      rw [hc]
      exact hy
  rw [h]
  exact hC.map f

theorem one_le_cImage {K : Type} [Field K] [NumberField K] (c : K →+* K)
    (C : Submodule (𝓞 K) K) (h1 : 1 ≤ C) : 1 ≤ cImage c C := by
  intro x hx
  rw [mem_cImage]
  exact h1 (mem_one_map c hx)

theorem relIndex_cImage {K : Type} [Field K] [NumberField K] (c : K →+* K)
    (hc : ∀ x, c (c x) = x) (C : Submodule (𝓞 K) K) :
    (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex (cImage c C).toAddSubgroup =
      (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup := by
  have h1 : (1 : Submodule (𝓞 K) K).toAddSubgroup
      = (1 : Submodule (𝓞 K) K).toAddSubgroup.comap c.toAddMonoidHom := by
    ext x
    constructor
    · intro hx
      exact mem_one_map c hx
    · intro hx
      have h' : c (c x) ∈ (1 : Submodule (𝓞 K) K) := mem_one_map c hx
      rwa [hc] at h'
  have h2 : (cImage c C).toAddSubgroup = C.toAddSubgroup.comap c.toAddMonoidHom := by
    ext x
    exact mem_cImage c C
  rw [h1, h2, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective]
  · rw [← h1]
  · exact fun y => ⟨c y, hc y⟩

theorem prod_mem_prod_sub {K : Type} [Field K] [NumberField K] {k : ℕ}
    (p : Fin k → Submodule (𝓞 K) K) (x : Fin k → K) (hx : ∀ i, x i ∈ p i) :
    ∏ i, x i ∈ ∏ i, p i := by
  classical
  suffices h : ∀ s : Finset (Fin k), ∏ i ∈ s, x i ∈ ∏ i ∈ s, p i by exact h Finset.univ
  intro s
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Submodule.mul_mem_mul (hx a) ih

theorem det_mem_prod_sub {K : Type} [Field K] [NumberField K] {k : ℕ}
    (p : Fin k → Submodule (𝓞 K) K) (T : Matrix (Fin k) (Fin k) K)
    (hT : ∀ i j, T i j ∈ p i) : T.det ∈ ∏ i, p i := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem_prod_sub p (fun i => Tᵀ (σ i) i) fun i => hT i (σ i)) _

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
