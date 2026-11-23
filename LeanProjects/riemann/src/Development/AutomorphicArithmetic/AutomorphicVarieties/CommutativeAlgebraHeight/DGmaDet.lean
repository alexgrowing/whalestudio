import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DExtPoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCorner
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DTrCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.BcChiTmul

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem chi_congr {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D D' : Det n A E) (y : E)
    (h : ∀ (B : Type) [CommRing B] [Algebra A B] (b : B), D.D B (1 + b ⊗ₜ y) = D'.D B (1 + b ⊗ₜ y)) :
    D.chi y = D'.chi y := by
  let L := Localization.Away (X : A[X])
  have hinj : Function.Injective (algebraMap A[X] L) :=
    IsLocalization.injective L (M := Submonoid.powers (X : A[X]))
      (by
        rintro _ ⟨k, rfl⟩
        exact pow_mem monic_X.mem_nonZeroDivisors k)
  apply hinj
  have key : ∀ D₀ : Det n A E, algebraMap A[X] L (D₀.chi y) =
      algebraMap A[X] L X ^ n * D₀.D L (1 + (-IsLocalization.Away.invSelf (S := L) (X : A[X])) ⊗ₜ y) := by
    intro D₀
    have h1 := D₀.nat A[X] L (IsScalarTower.toAlgHom A A[X] L) (X ⊗ₜ 1 - 1 ⊗ₜ y)
    rw [← D₀.homog]
    refine h1.symm.trans ?_
    congr 1
    rw [smul_add, smul_tmul', smul_eq_mul, mul_neg, IsLocalization.Away.mul_invSelf, neg_tmul,
      Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one, ← sub_eq_add_neg]
    simp
  rw [key, key, h]

private theorem chi_one {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) :
    D.chi 1 = (X - 1) ^ n := by
  have := D.homog A[X] (X - 1) 1
  rw [map_one, mul_one] at this
  rw [← this, Det.chi, ← sub_tmul, Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one]

private theorem chi_zero {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) :
    D.chi 0 = X ^ n := by
  have := D.homog A[X] X 1
  rw [map_one, mul_one] at this
  rw [← this, Det.chi, tmul_zero, sub_zero, Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one]

private theorem ev_one_add {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E)
    (h : D.D A[X] (1 + X ⊗ₜ e) = 1 + X) (B : Type) [CommRing B] [Algebra A B] (b : B) :
    D.D B (1 + b ⊗ₜ e) = 1 + b := by
  have := D.nat A[X] B (aeval b) (1 + X ⊗ₜ e)
  rw [h] at this
  simpa using this

private theorem det_one_add_single {n : ℕ} {B : Type} [CommRing B] (i : Fin n) (b : B) :
    (1 + Matrix.single i i b).det = 1 + b := by
  rw [← Matrix.diagonal_single, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.det_diagonal,
    Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private noncomputable def rS {n : ℕ} {A E S : Type} [CommRing A] [Ring E] [Algebra A E] [CommRing S] [Algebra A S]
    (r : E →ₐ[A] Matrix (Fin n) (Fin n) S) : S ⊗[A] E →ₐ[S] Matrix (Fin n) (Fin n) S :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) r fun s _ => Algebra.commute_algebraMap_left s _

private theorem rS_tmul {n : ℕ} {A E S : Type} [CommRing A] [Ring E] [Algebra A E] [CommRing S] [Algebra A S]
    (r : E →ₐ[A] Matrix (Fin n) (Fin n) S) (s : S) (x : E) : rS r (s ⊗ₜ x) = s • r x :=
  (Algebra.TensorProduct.lift_tmul _ _ _ s x).trans (Algebra.smul_def _ _).symm

private def adapted {n : ℕ} {E : Type} [Ring E] (e : Fin n → E) (he : ∀ i, IsIdempotentElem (e i)) : Submonoid E where
  carrier := {x | x = 1 ∨ ∃ i j, e i * x * e j = x}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro x y (rfl | ⟨i, j, hx⟩) hy
    · simpa using hy
    rcases hy with rfl | ⟨k, l, hy⟩
    · exact Or.inr ⟨i, j, by simpa using hx⟩
    have h1 : e i * x = x := by rw [← hx, ← mul_assoc, ← mul_assoc, (he i).eq]
    have h2 : y * e l = y := by rw [← hy, mul_assoc, (he l).eq]
    exact Or.inr ⟨i, l, by rw [← mul_assoc, h1, mul_assoc, h2]⟩

theorem UpperTheory.V.CA.d_gma_det :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : Fin n → E), D.IsCH → CompleteOrthogonalIdempotents e → (∀ i, D.D A[X] (1 + X ⊗ₜ e i) = 1 + X) → ∀ (S : Type) [CommRing S] [Algebra A S] (r : E →ₐ[A] Matrix (Fin n) (Fin n) S), (∀ i, r (e i) = Matrix.single i i 1) → ∀ (T : Type) [CommRing T] [Algebra A T] [Algebra S T] [IsScalarTower A S T] {ι : Type} [Fintype ι] (t : ι → T) (x : ι → E), D.D T (∑ a, t a ⊗ₜ x a) = (∑ a, t a • (r (x a)).map (algebraMap S T)).det := by
  intro n A E _ _ _ D e hCH he h1 S _ _ r hr T _ _ _ _ ι _ t x
  have hrep : ∀ (B : Type) [CommRing B] [Algebra S B] (y : B ⊗[S] (S ⊗[A] E)),
      (Det.ofRep (Fintype.card_fin n) (rS r)).D B y = (Det.repS (rS r) B y).det := fun _ _ _ _ => rfl
  have main : D.baseChange S = Det.ofRep (Fintype.card_fin n) (rS r) := by
    refine d_ext _ _ ((adapted e he.idem).map
      (Algebra.TensorProduct.includeRight : E →ₐ[A] S ⊗[A] E).toMonoidHom) ?_ ?_
    · rw [eq_top_iff]
      rintro y -
      induction y with
      | zero => exact zero_mem _
      | add a b ha hb => exact add_mem ha hb
      | tmul s z =>
        have hz : z = ∑ i, ∑ j, e i * z * e j := by
          simp only [← Finset.mul_sum, he.complete, mul_one, ← Finset.sum_mul, one_mul]
        have hs : s ⊗ₜ[A] z = s • ((1 : S) ⊗ₜ[A] z) := by rw [smul_tmul', smul_eq_mul, mul_one]
        rw [hs, hz]
        refine Submodule.smul_mem _ _ ?_
        simp only [tmul_sum]
        refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.subset_span ?_
        refine ⟨e i * z * e j, Or.inr ⟨i, j, ?_⟩, rfl⟩
        rw [← mul_assoc, ← mul_assoc, (he.idem i).eq, mul_assoc, (he.idem j).eq]
    · rintro _ ⟨z, hz, rfl⟩ k hk1 hkn
      change (D.baseChange S).lam k ((1 : S) ⊗ₜ[A] z) = Det.lam _ k ((1 : S) ⊗ₜ[A] z)
      rcases hz with rfl | ⟨i, j, hz⟩
      · rw [← Algebra.TensorProduct.one_def, Det.lam, Det.lam, chi_one, chi_one]
      by_cases hij : i = j
      · subst hij
        have hc := (d_corner D (e i) hCH (he.idem i) (h1 i) (hk1.trans hkn)).1 z
        rw [hz] at hc
        generalize D.tr (e i * z) = a at hc
        subst hc
        rw [Det.lam, Det.lam, chi_congr (D.baseChange S) (Det.ofRep (Fintype.card_fin n) (rS r))]
        intro B _ _ b
        letI : Algebra A B := ((algebraMap S B).comp (algebraMap A S)).toAlgebra
        haveI : IsScalarTower A S B := .of_algebraMap_eq fun _ => rfl
        rw [(d_bc D S).1 B, hrep, map_add, map_add (Det.repS _ _), map_one, map_one (Det.repS _ _),
          Det.cancel_tmul, Det.repS_tmul, rS_tmul, map_one, mul_one, ← smul_tmul, ev_one_add D _ (h1 i), map_smul, hr, one_smul,
          ← det_one_add_single i (a • b)]
        congr 2
        ext p q
        simp only [Matrix.single_apply, Matrix.smul_apply, Matrix.map_apply]
        split_ifs
        · rw [Algebra.smul_def, Algebra.smul_def a, mul_one, smul_eq_mul, mul_comm]; rfl
        · simp
      · have h0 : ∀ D₀ : Det n S (S ⊗[A] E), D₀.lam k ((1 : S) ⊗ₜ[A] z) = D₀.lam k 0 := by
          intro D₀
          have e1 : (1 : S) ⊗ₜ[A] z = ((1 : S) ⊗ₜ[A] (e i * z)) * ((1 : S) ⊗ₜ[A] e j) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hz]
          rw [e1, (d_tr D₀).2.1, Algebra.TensorProduct.tmul_mul_tmul, ← mul_assoc, he.ortho (Ne.symm hij),
            zero_mul, tmul_zero]
        rw [h0, h0, Det.lam, Det.lam, chi_zero, chi_zero]
  have h2 := (d_bc D S).1 T (∑ a, t a ⊗ₜ ((1 : S) ⊗ₜ[A] x a))
  rw [main, hrep] at h2
  simp only [map_sum, Det.cancel_tmul, Det.repS_tmul, rS_tmul, map_one, mul_one, one_smul] at h2
  exact h2.symm
