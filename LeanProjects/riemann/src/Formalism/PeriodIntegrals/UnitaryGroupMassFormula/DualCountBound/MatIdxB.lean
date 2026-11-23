import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SmithMat

noncomputable section

open scoped Classical

namespace PI.NGStepBBW

theorem card_quot_span_mul {R : Type} [CommRing R] [IsDomain R] {a : R} (ha : a ≠ 0) (b : R) :
    Nat.card (R ⧸ Ideal.span {a * b}) = Nat.card (R ⧸ Ideal.span {a}) * Nat.card (R ⧸ Ideal.span {b}) := by
  have hHK : (Ideal.span {a * b}).toAddSubgroup ≤ (Ideal.span {a}).toAddSubgroup := fun x hx => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    exact Ideal.mem_span_singleton'.mpr ⟨c * b, by ring⟩
  have h1 : Nat.card (R ⧸ Ideal.span {a * b}) = (Ideal.span {a * b}).toAddSubgroup.index := rfl
  have h2 : Nat.card (R ⧸ Ideal.span {a}) = (Ideal.span {a}).toAddSubgroup.index := rfl
  have h3 : Nat.card (R ⧸ Ideal.span {b}) = (Ideal.span {b}).toAddSubgroup.index := rfl
  rw [h1, h2, h3, ← AddSubgroup.relIndex_mul_index hHK, mul_comm]
  congr 1
  let f : R →+ (Ideal.span {a}).toAddSubgroup :=
    { toFun := fun x => ⟨a * x, Ideal.mem_span_singleton'.mpr ⟨x, mul_comm _ _⟩⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp [mul_add] }
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    exact ⟨c, by ext; simp [f, mul_comm]⟩
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hf]
  congr 1
  ext x
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
  show a * x ∈ Ideal.span {a * b} ↔ x ∈ Ideal.span {b}
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  exact mul_dvd_mul_iff_left ha

theorem card_quot_prod {R : Type} [CommRing R] [IsDomain R] {ι : Type} (s : Finset ι) (d : ι → R)
    (hd : ∀ i ∈ s, d i ≠ 0) :
    Nat.card (R ⧸ Ideal.span {∏ i ∈ s, d i}) = ∏ i ∈ s, Nat.card (R ⧸ Ideal.span {d i}) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Ideal.span_singleton_one]
    haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Nat.card_of_subsingleton (0 : R ⧸ ⊤)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      card_quot_span_mul (hd i (Finset.mem_insert_self i s)),
      ih (fun j hj => hd j (Finset.mem_insert_of_mem hj))]

theorem card_coker_matrix {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) R) (hA : A.det ≠ 0) :
    Nat.card ((Fin n → R) ⧸ LinearMap.range A.mulVecLin) = Nat.card (R ⧸ Ideal.span {A.det}) := by
  classical
  obtain ⟨U, V, d, hU, hV, hD⟩ := smith_diagonal_entries R n A
  have hUd : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
  have hVd : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hprod : ∏ i, d i = U.det * A.det * V.det := by
    rw [← Matrix.det_diagonal, ← hD, Matrix.det_mul, Matrix.det_mul]
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin n)), d i ≠ 0 := by
    have h0 : ∏ i, d i ≠ 0 := by
      rw [hprod]
      exact mul_ne_zero (mul_ne_zero hUd.ne_zero hA) hVd.ne_zero
    exact fun i _ => (Finset.prod_ne_zero_iff.mp h0) i (Finset.mem_univ i)
  letI := hU.invertible
  let Ue : (Fin n → R) ≃ₗ[R] (Fin n → R) := Matrix.toLinearEquiv' U inferInstance
  have hVs : LinearMap.range V.mulVecLin = ⊤ := by
    letI := hV.invertible
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨Matrix.mulVec (⅟V) y, by simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]⟩
  have hrange : (LinearMap.range A.mulVecLin).map (Ue : (Fin n → R) →ₗ[R] (Fin n → R)) =
      LinearMap.range (Matrix.diagonal d).mulVecLin := by
    rw [← hD, Matrix.mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ hVs, Matrix.mulVecLin_mul,
      LinearMap.range_comp]
    rfl
  have hA1 : Nat.card ((Fin n → R) ⧸ LinearMap.range A.mulVecLin) =
      Nat.card ((Fin n → R) ⧸ LinearMap.range (Matrix.diagonal d).mulVecLin) :=
    Nat.card_congr (Submodule.Quotient.equiv _ _ Ue hrange).toEquiv
  have hrd : LinearMap.range (Matrix.diagonal d).mulVecLin = Submodule.pi Set.univ (fun i => Ideal.span {d i}) := by
    ext v
    simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨w, rfl⟩ i
      exact ⟨w i, by simp [Matrix.mulVecLin_apply, Matrix.mulVec_diagonal, mul_comm]⟩
    · intro h
      choose w hw using h
      exact ⟨w, funext fun i => by simp only [Matrix.mulVecLin_apply, Matrix.mulVec_diagonal]; rw [mul_comm]; exact hw i⟩
  have hspan : Ideal.span {U.det * A.det * V.det} = Ideal.span {A.det} :=
    Ideal.span_singleton_eq_span_singleton.mpr
      (Associated.symm ⟨hUd.unit * hVd.unit, by simp only [Units.val_mul, IsUnit.unit_spec]; ring⟩)
  rw [hA1, hrd, Nat.card_congr (Submodule.quotientPi _).toEquiv, Nat.card_pi, ← card_quot_prod Finset.univ d hne,
    hprod, hspan]

theorem card_coker_endo {R N : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    (ψ : N →ₗ[R] N) (hψ : LinearMap.det ψ ≠ 0) :
    Nat.card (N ⧸ LinearMap.range ψ) = Nat.card (R ⧸ Ideal.span {LinearMap.det ψ}) := by
  let b := Module.finBasis R N
  have hdet : (LinearMap.toMatrix b b ψ).det = LinearMap.det ψ := LinearMap.det_toMatrix b ψ
  have hsq : (b.equivFun : N →ₗ[R] (Fin (Module.finrank R N) → R)) ∘ₗ ψ =
      (LinearMap.toMatrix b b ψ).mulVecLin ∘ₗ (b.equivFun : N →ₗ[R] (Fin (Module.finrank R N) → R)) := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_apply, Matrix.mulVecLin_apply]
    exact (LinearMap.toMatrix_mulVec_repr b b ψ x).symm
  have hmap : (LinearMap.range ψ).map (b.equivFun : N →ₗ[R] (Fin (Module.finrank R N) → R)) =
      LinearMap.range (LinearMap.toMatrix b b ψ).mulVecLin := by
    rw [← LinearMap.range_comp, hsq, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  rw [Nat.card_congr (Submodule.Quotient.equiv _ _ b.equivFun hmap).toEquiv,
    card_coker_matrix _ (LinearMap.toMatrix b b ψ) (by rw [hdet]; exact hψ), hdet]

end PI.NGStepBBW
