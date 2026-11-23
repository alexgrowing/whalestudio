import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.DetSubmatrixFun

open Matrix Finset

noncomputable section

namespace PI.IsoDerivBFintype

instance finiteOE (h n : ℕ) : Finite (Fin h ↪o Fin n) :=
  Finite.of_injective (fun f : Fin h ↪o Fin n => (f : Fin h → Fin n)) DFunLike.coe_injective

instance fintypeOE (h n : ℕ) : Fintype (Fin h ↪o Fin n) := Fintype.ofFinite _

theorem exists_oe_perm {h n : ℕ} (f : Fin h → Fin n) (hf : Function.Injective f) :
    ∃ (I : Fin h ↪o Fin n) (σ : Equiv.Perm (Fin h)), ∀ i, I (σ i) = f i := by
  classical
  set s : Finset (Fin n) := Finset.univ.image f with hs
  have hcard : s.card = h := by
    rw [hs, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have hmem : ∀ i, f i ∈ s := fun i => Finset.mem_image_of_mem f (Finset.mem_univ i)
  let g : Fin h → Fin h := fun i => (s.orderIsoOfFin hcard).symm ⟨f i, hmem i⟩
  have hg : ∀ i, s.orderEmbOfFin hcard (g i) = f i := by
    intro i
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp [g]
  have ginj : Function.Injective g := by
    intro i j e
    apply hf
    rw [← hg i, ← hg j, e]
  exact ⟨s.orderEmbOfFin hcard, Equiv.ofBijective g (Finite.injective_iff_bijective.mp ginj), hg⟩

theorem cauchyBinet {R : Type*} [CommRing R] {h n : ℕ}
    (A : Matrix (Fin h) (Fin n) R) (B : Matrix (Fin n) (Fin h) R) :
    (A * B).det = ∑ I : Fin h ↪o Fin n, (A.submatrix id I).det * (B.submatrix I id).det := by
  classical
  rw [GenFrameSpan.det_mul_rect]
  have hR : ∀ I : Fin h ↪o Fin n, (A.submatrix id I).det * (B.submatrix I id).det
      = ∑ σ : Equiv.Perm (Fin h), (∏ i, B (I (σ i)) i) * (A.submatrix id (fun i => I (σ i))).det := by
    intro I
    rw [det_apply (B.submatrix I id), Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have e : A.submatrix id (fun i => I (σ i)) = (A.submatrix id I).submatrix id σ := rfl
    rw [e, det_permute']
    simp only [submatrix_apply, id, Units.smul_def, zsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun I _ => hR I, ← Finset.sum_product']
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => fun i => p.1 (p.2 i)) (fun _ _ _ => Finset.mem_univ _)
    ?_ ?_ (fun _ _ _ => rfl)
  · rintro ⟨I, σ⟩ _ _ ⟨I', σ'⟩ _ _ e
    have e' : (fun i => I (σ i)) = fun i => I' (σ' i) := e
    have hr : Set.range I = Set.range I' := by
      have h1 : Set.range (fun i => I (σ i)) = Set.range I := σ.surjective.range_comp I
      have h2 : Set.range (fun i => I' (σ' i)) = Set.range I' := σ'.surjective.range_comp I'
      rw [← h1, ← h2, e']
    have hI : I = I' := OrderEmbedding.range_inj.mp hr
    subst hI
    have : σ = σ' := by
      ext i
      have := congrFun e' i
      exact congrArg Fin.val (I.injective this)
    rw [this]
  · intro f _ hne
    have hf : Function.Injective f := by
      intro i j e
      by_contra hij
      apply hne
      rw [Matrix.det_zero_of_column_eq hij (by intro r; simp [e]), mul_zero]
    obtain ⟨I, σ, hIσ⟩ := exists_oe_perm f hf
    exact ⟨(I, σ), Finset.mem_univ _, by simpa [hIσ] using hne, funext hIσ⟩

end PI.IsoDerivBFintype
