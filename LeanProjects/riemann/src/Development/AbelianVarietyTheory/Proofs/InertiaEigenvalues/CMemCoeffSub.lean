import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetOneAddSmulBlkMem

open scoped BigOperators

namespace GlobalTheory.BlockDetPoly

def coeffSub {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (m : ℕ) :
    Subalgebra (MvPolynomial (Fin m) O) (X → MvPolynomial (Fin m) O) where
  carrier := {f | ∀ d, (fun x => MvPolynomial.coeff d (f x)) ∈ T}
  mul_mem' := by
    intro f g hf hg d
    have : (fun x => MvPolynomial.coeff d ((f * g) x)) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal d,
        (fun x => MvPolynomial.coeff p.1 (f x)) * (fun x => MvPolynomial.coeff p.2 (g x)) := by
      funext x
      simp [MvPolynomial.coeff_mul, Finset.sum_apply]
    rw [this]
    exact T.sum_mem fun p _ => T.mul_mem (hf _) (hg _)
  add_mem' := by
    intro f g hf hg d
    have : (fun x => MvPolynomial.coeff d ((f + g) x)) =
        (fun x => MvPolynomial.coeff d (f x)) + (fun x => MvPolynomial.coeff d (g x)) := by
      funext x
      simp
    rw [this]
    exact T.add_mem (hf _) (hg _)
  algebraMap_mem' := fun p d => T.algebraMap_mem (MvPolynomial.coeff d p)

theorem C_mem_coeffSub {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (m : ℕ)
    (t : X → O) (ht : t ∈ T) : (fun x => MvPolynomial.C (t x)) ∈ coeffSub T m := by
  show ∀ d : Fin m →₀ ℕ,
    (fun x => MvPolynomial.coeff d (MvPolynomial.C (t x) : MvPolynomial (Fin m) O)) ∈ T
  intro d
  rcases eq_or_ne d 0 with rfl | hd
  · simpa using ht
  · have h0 : (fun x => MvPolynomial.coeff d (MvPolynomial.C (t x) : MvPolynomial (Fin m) O)) = 0 := by
      funext x
      simp [MvPolynomial.coeff_C, Ne.symm hd]
    rw [h0]
    exact T.zero_mem

theorem det_comb_mem {O X Q : Type} [CommRing O] [CommRing Q] (T : Subalgebra O (X → O)) {n : ℕ}
    (R : Subalgebra O (X → Matrix (Fin n) (Fin n) O))
    (hR : ∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, a k ∈ R) →
      ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) ∈ T)
    (φ : O →+* Q) (S : Subalgebra Q (X → Q)) (hS : ∀ t ∈ T, (fun x => φ (t x)) ∈ S)
    {J : Type} [Fintype J] (b : J → X → Matrix (Fin n) (Fin n) O) (hb : ∀ j, b j ∈ R)
    (c : J → Q) : (fun x => Matrix.det (∑ j, c j • (b j x).map φ)) ∈ S := by
  classical

  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let a : Fin (Fintype.card J) → X → Matrix (Fin n) (Fin n) O := fun k => b (e k)

  let A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (Fintype.card J)) (X → O)) :=
    Matrix.of fun i j => ∑ k, MvPolynomial.X k * MvPolynomial.C (fun x => a k x i j)
  have hcoef : ∀ d, MvPolynomial.coeff d A.det ∈ T := by
    intro d
    have h1 : MvPolynomial.coeff d A.det = fun x => MvPolynomial.coeff d (Matrix.det
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin (Fintype.card J)) O) •
          (a k x).map MvPolynomial.C)) := by
      funext x
      have h2 : MvPolynomial.map (Pi.evalRingHom (fun _ : X => O) x) A.det =
          Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin (Fintype.card J)) O) •
            (a k x).map MvPolynomial.C) := by
        rw [RingHom.map_det]
        congr 1
        ext i j
        simp [A, Matrix.sum_apply]
      rw [← h2, MvPolynomial.coeff_map]
      rfl
    rw [h1]
    exact hR _ a (fun k => hb (e k)) d

  have h3 : ∀ x, Matrix.det (∑ j, c j • (b j x).map φ) =
      MvPolynomial.eval₂ (φ.comp (Pi.evalRingHom (fun _ : X => O) x)) (fun k => c (e k)) A.det := by
    intro x
    rw [← MvPolynomial.coe_eval₂Hom, RingHom.map_det]
    congr 1
    ext i j
    simp only [A, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      MvPolynomial.eval₂_C, RingHom.comp_apply, Pi.evalRingHom_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    exact (e.sum_comp (fun j' => c j' * φ (b j' x i j))).symm
  have key : (fun x => Matrix.det (∑ j, c j • (b j x).map φ)) =
      ∑ d ∈ A.det.support, (fun x => φ (MvPolynomial.coeff d A.det x)) *
        algebraMap Q (X → Q) (∏ k, c (e k) ^ d k) := by
    funext x
    rw [h3, MvPolynomial.eval₂_eq', Finset.sum_apply]
    simp
  rw [key]
  exact S.sum_mem fun d _ => S.mul_mem (hS _ (hcoef d)) (S.algebraMap_mem _)

private theorem mem_coeffSub_iff_forall_coeff_mem {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (m : ℕ)
    (f : X → MvPolynomial (Fin m) O) :
    f ∈ coeffSub T m ↔ ∀ d, (fun x => MvPolynomial.coeff d (f x)) ∈ T := Iff.rfl

theorem main : ∀ {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (n : ℕ) (R : Subalgebra O (X → Matrix (Fin n) (Fin n) O)), (∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, a k ∈ R) → ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) ∈ T) → ∀ (m g : ℕ) (Θ : Fin m → Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ k p q, Θ k p q ∈ R) → ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) * MvPolynomial.C (Θ k pa.1 qb.1 x pa.2 qb.2)))) ∈ T := by
  intro O X _ T n R hR m g Θ hΘ d
  classical

  let ψ : (X → Matrix (Fin n) (Fin n) O) →+* (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)) :=
    RingHom.compLeft (MvPolynomial.C : O →+* MvPolynomial (Fin m) O).mapMatrix X
  have hψ : ∀ (a : X → Matrix (Fin n) (Fin n) O) x, ψ a x = (a x).map MvPolynomial.C :=
    fun _ _ => rfl
  let s : Submonoid (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)) := R.toSubmonoid.map ψ
  let R' : Subalgebra (MvPolynomial (Fin m) O) (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)) :=
    Algebra.adjoin (MvPolynomial (Fin m) O) (s : Set _)

  have hrep : ∀ F ∈ R', ∃ (N : ℕ) (c : Fin N → MvPolynomial (Fin m) O)
      (b : Fin N → X → Matrix (Fin n) (Fin n) O), (∀ j, b j ∈ R) ∧ F = ∑ j, c j • ψ (b j) := by
    intro F hF
    have hF' : F ∈ Submodule.span (MvPolynomial (Fin m) O) (s : Set _) := by
      have h := Algebra.adjoin_eq_span (R := MvPolynomial (Fin m) O)
        (s : Set (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)))
      rw [Submonoid.closure_eq] at h
      rw [← h]
      exact hF
    obtain ⟨N, c, b, hsum⟩ := Submodule.mem_span_set'.mp hF'
    choose b' hb' hbe using fun j => Submonoid.mem_map.mp (b j).2
    refine ⟨N, c, b', fun j => hb' j, ?_⟩
    rw [← hsum]
    simp [hbe]

  have hR' : ∀ (m' : ℕ) (a : Fin m' → X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)),
      (∀ k, a k ∈ R') → ∀ d' : Fin m' →₀ ℕ, (fun x => MvPolynomial.coeff d' (Matrix.det
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m') (MvPolynomial (Fin m) O)) •
          (a k x).map MvPolynomial.C))) ∈ coeffSub T m := by
    intro m' a ha d'
    choose N c b hb hab using fun k => hrep (a k) (ha k)
    have hS : ∀ t ∈ T, (fun x => ((MvPolynomial.C : MvPolynomial (Fin m) O →+* MvPolynomial (Fin m')
        (MvPolynomial (Fin m) O)).comp MvPolynomial.C) (t x)) ∈ coeffSub (coeffSub T m) m' :=
      fun t ht => C_mem_coeffSub (coeffSub T m) m' _ (C_mem_coeffSub T m t ht)
    have h := det_comb_mem T R hR ((MvPolynomial.C : MvPolynomial (Fin m) O →+* MvPolynomial (Fin m')
        (MvPolynomial (Fin m) O)).comp MvPolynomial.C) (coeffSub (coeffSub T m) m') hS
      (J := Σ k, Fin (N k)) (fun kj => b kj.1 kj.2) (fun kj => hb kj.1 kj.2)
      (fun kj => MvPolynomial.X kj.1 * MvPolynomial.C (c kj.1 kj.2))
    have heq : ∀ x, (∑ kj : (Σ k, Fin (N k)), (MvPolynomial.X kj.1 * MvPolynomial.C (c kj.1 kj.2) :
          MvPolynomial (Fin m') (MvPolynomial (Fin m) O)) • (b kj.1 kj.2 x).map
          ((MvPolynomial.C : MvPolynomial (Fin m) O →+* MvPolynomial (Fin m')
            (MvPolynomial (Fin m) O)).comp MvPolynomial.C)) =
        ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m') (MvPolynomial (Fin m) O)) •
          (a k x).map MvPolynomial.C := by
      intro x
      ext i j
      simp [hab, hψ, Matrix.sum_apply, Fintype.sum_sigma, Finset.mul_sum, mul_assoc, Finset.sum_apply]
    simp only [heq] at h
    exact (mem_coeffSub_iff_forall_coeff_mem _ _ _).mp h d'

  have hblk : ∀ p q, (fun x => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) •
      (Θ k p q x).map MvPolynomial.C) ∈ R' := by
    intro p q
    have h4 : (fun x => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) •
        (Θ k p q x).map MvPolynomial.C) = ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • ψ (Θ k p q) := by
      funext x
      simp [Finset.sum_apply, hψ]
    rw [h4]
    exact R'.sum_mem fun k _ =>
      R'.smul_mem (Algebra.subset_adjoin (Submonoid.mem_map.mpr ⟨Θ k p q, hΘ k p q, rfl⟩)) _
  have h5 := (mem_coeffSub_iff_forall_coeff_mem _ _ _).mp (GlobalTheory.BlockDet.main (coeffSub T m) n R' hR' g _ hblk) d
  have h6 : ∀ x, (Matrix.of fun (pa qb : Fin g × Fin n) => (∑ k, (MvPolynomial.X k :
        MvPolynomial (Fin m) O) • (Θ k pa.1 qb.1 x).map MvPolynomial.C) pa.2 qb.2) =
      Matrix.of fun (pa qb : Fin g × Fin n) => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) *
        MvPolynomial.C (Θ k pa.1 qb.1 x pa.2 qb.2) := by
    intro x
    ext pa qb
    simp [Matrix.sum_apply]
  simp only [h6] at h5
  exact h5

end GlobalTheory.BlockDetPoly
