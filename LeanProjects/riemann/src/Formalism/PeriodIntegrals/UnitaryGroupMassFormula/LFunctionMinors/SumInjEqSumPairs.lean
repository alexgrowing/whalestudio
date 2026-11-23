import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.FintypeColChoice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.DetSubmatrixFun

open Matrix Finset Equiv

noncomputable section

namespace PI.WwMainW

theorem sum_inj_eq_sum_pairs {R : Type} [CommRing R] {p n : ℕ} (F : (Fin p → Fin n) → R) :
    ∑ x : (Fin p ↪o Fin n) × Perm (Fin p), F (x.1 ∘ x.2) =
      ∑ f ∈ univ.filter (fun f : Fin p → Fin n => Function.Injective f), F f := by
  classical
  refine Finset.sum_bij (fun x _ => (x.1 : Fin p → Fin n) ∘ x.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact x.1.injective.comp x.2.injective
  · rintro ⟨I, σ⟩ _ ⟨J, τ⟩ _ h
    simp only at h
    have hr : Set.range (I : Fin p → Fin n) = Set.range (J : Fin p → Fin n) := by
      calc Set.range (I : Fin p → Fin n) = Set.range (⇑I ∘ ⇑σ) := (σ.surjective.range_comp _).symm
        _ = Set.range (⇑J ∘ ⇑τ) := by rw [h]
        _ = Set.range (J : Fin p → Fin n) := τ.surjective.range_comp _
    have hs : (Finset.univ.image (J : Fin p → Fin n)).card = p := by
      rw [Finset.card_image_of_injective _ J.injective]; simp
    have hIJ : (I : Fin p → Fin n) = J := by
      have e1 : (I : Fin p → Fin n) = (Finset.univ.image (J : Fin p → Fin n)).orderEmbOfFin hs :=
        Finset.orderEmbOfFin_unique hs (fun x => by
          have hx : I x ∈ Set.range (I : Fin p → Fin n) := ⟨x, rfl⟩
          rw [hr] at hx
          obtain ⟨y, hy⟩ := hx
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨y, hy⟩) I.strictMono
      have e2 : (J : Fin p → Fin n) = (Finset.univ.image (J : Fin p → Fin n)).orderEmbOfFin hs :=
        Finset.orderEmbOfFin_unique hs (fun x => by simp) J.strictMono
      exact e1.trans e2.symm
    have hIJ' : I = J := DFunLike.coe_injective hIJ
    subst hIJ'
    have hστ : σ = τ := Equiv.ext fun j => I.injective (congrFun h j)
    rw [hστ]
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    have hs : (Finset.univ.image f).card = p := by
      rw [Finset.card_image_of_injective _ hf]; simp
    set I := (Finset.univ.image f).orderEmbOfFin hs with hI
    have hex : ∀ j, ∃ k, I k = f j := by
      intro j
      have hm : f j ∈ Set.range (I : Fin p → Fin n) := by
        rw [hI, Finset.range_orderEmbOfFin]; simp
      exact hm
    choose g hg using hex
    have ginj : Function.Injective g := by
      intro a b hab
      apply hf
      rw [← hg a, ← hg b, hab]
    refine ⟨(I, Equiv.ofBijective g (Finite.injective_iff_bijective.mp ginj)), Finset.mem_univ _, ?_⟩
    funext j
    first
      | simp only [Function.comp_apply, Equiv.ofBijective_apply]; exact hg j
      | simp [hg]

theorem cbSorted : CBSorted := by
  unfold CBSorted
  intro R _ p n A B
  classical
  have step1 : (A * B).det = ∑ f : Fin p → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
    simp only [Matrix.det_apply', Matrix.mul_apply, Matrix.submatrix_apply, id_eq,
      Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  have step2 : ∑ f : Fin p → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det =
      ∑ x : (Fin p ↪o Fin n) × Perm (Fin p),
        (∏ i, B ((⇑x.1 ∘ ⇑x.2) i) i) * (A.submatrix id (⇑x.1 ∘ ⇑x.2)).det := by
    rw [sum_inj_eq_sum_pairs (fun f : Fin p → Fin n => (∏ i, B (f i) i) * (A.submatrix id f).det),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs with hf
    · rfl
    · have hf' : ∃ i j, f i = f j ∧ i ≠ j := by
        by_contra hc
        apply hf
        intro i j hij
        by_contra hne
        exact hc ⟨i, j, hij, hne⟩
      obtain ⟨i, j, hij, hne⟩ := hf'
      rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [Matrix.submatrix_apply, hij]), mul_zero]
  rw [step1, step2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun J _ => ?_
  have hsub : ∀ τ : Perm (Fin p),
      (A.submatrix id (⇑J ∘ ⇑τ)).det = Perm.sign τ * (A.submatrix id J).det := by
    intro τ
    have hm : A.submatrix id (⇑J ∘ ⇑τ) = (A.submatrix id J).submatrix id τ := by
      rw [Matrix.submatrix_submatrix]; rfl
    rw [hm, Matrix.det_permute']
  simp only [hsub]
  rw [Matrix.det_apply' (B.submatrix J id), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Matrix.submatrix_apply, id_eq, Function.comp_apply]
  ring

end PI.WwMainW
