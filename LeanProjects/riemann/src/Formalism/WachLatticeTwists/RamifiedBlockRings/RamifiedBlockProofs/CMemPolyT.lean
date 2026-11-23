import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.RingDataObjects
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaDetPoly

open Finset Classical Polynomial

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

section
variable {O : Type} [CommRing O] {Xs : Type} (T : Subalgebra O (Xs → O))
  {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (Xs → Matrix d d O))

def polyT : Subalgebra O[X] (Xs → O[X]) where
  carrier := {f | ∀ k, (fun x => (f x).coeff k) ∈ T}
  mul_mem' := by
    intro f g hf hg k
    have h : (fun x => ((f * g) x).coeff k) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, (fun x => (f x).coeff p.1) * (fun x => (g x).coeff p.2) := by
      funext x; simp [Polynomial.coeff_mul, Finset.sum_apply]
    rw [h]
    exact T.sum_mem fun p _ => T.mul_mem (hf _) (hg _)
  add_mem' := by
    intro f g hf hg k
    have h : (fun x => ((f + g) x).coeff k) = (fun x => (f x).coeff k) + fun x => (g x).coeff k := by
      funext x; simp
    rw [h]
    exact T.add_mem (hf k) (hg k)
  algebraMap_mem' p := by
    intro k
    have h : (fun x => ((algebraMap O[X] (Xs → O[X]) p) x).coeff k) =
        algebraMap O (Xs → O) (p.coeff k) := by
      funext x; simp
    rw [h]
    exact T.algebraMap_mem _

theorem C_mem_polyT {c : Xs → O} (hc : c ∈ T) : (fun x => C (c x)) ∈ polyT T := by
  show ∀ k, (fun x => (C (c x)).coeff k) ∈ T
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hc
  · have h0 : (fun x => (C (c x)).coeff k) = 0 := by
      funext x
      simp [Polynomial.coeff_C, hk.ne']
    rw [h0]
    exact T.zero_mem

def rPoly : G →* (Xs → Matrix d d O[X]) where
  toFun g x := (r g x).map C
  map_one' := by funext x; simp
  map_mul' g h := by funext x; simp [Matrix.map_mul]

theorem lift_mem {a : Xs → Matrix d d O} (ha : a ∈ tSpan T r) :
    (fun x => (a x).map C) ∈ tSpan (polyT T) (rPoly r) := by
  obtain ⟨s, c, hc, rfl⟩ := ha
  refine ⟨s, fun g x => C (c g x), fun g => C_mem_polyT T (hc g), ?_⟩
  funext x
  ext i j
  simp [rPoly, Finset.sum_apply, Matrix.sum_apply, map_sum]

private theorem matrix_charpolyRev_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix d d R) : (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply]
  · simp [Matrix.one_apply, h]

theorem detT (hG1 : ∀ (g : G) (k : ℕ), (fun x => (Matrix.charpolyRev (r g x)).coeff k) ∈ T)
    (M : Xs → Matrix d d O[X]) (hM : M ∈ tSpan (polyT T) (rPoly r)) (k : ℕ) :
    (fun x => (M x).det.coeff k) ∈ T := by
  have h1 : ∀ (g : G) (k : ℕ), FromT (polyT T) (fun x => (Matrix.charpolyRev (rPoly r g x)).coeff k) := by
    intro g k
    refine ⟨fun x => C ((Matrix.charpolyRev (r g x)).coeff k), C_mem_polyT T (hG1 g k), fun x => ?_⟩
    have hx : rPoly r g x = (r g x).map C := rfl
    dsimp only
    rw [hx, matrix_charpolyRev_map, Polynomial.coeff_map]
    rfl
  obtain ⟨u, hu, hux⟩ := det_poly_statement O[X] O[X] Xs G d (polyT T) (rPoly r) h1 1 (fun _ => M)
    (fun _ => hM) (Finsupp.single 0 (Fintype.card d))
  have key : ∀ x, u x = (M x).det := by
    intro x
    have hx := hux x
    dsimp only at hx
    rw [Fin.sum_univ_one, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, mul_comm,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow] at hx
    simpa using hx
  have hfun : (fun x => (M x).det.coeff k) = fun x => (u x).coeff k := by
    funext x
    rw [key x]
  rw [hfun]
  exact hu k

end

theorem charT : StatCharT := by
  intro O _ X T d _ _ G _ r hG1 a ha k
  have hA : (fun x => (a x).map C) ∈ spanSub (polyT T) (rPoly r) := lift_mem T r ha
  have hM : (fun x => 1 - (Polynomial.X : O[X]) • (a x).map C) ∈ spanSub (polyT T) (rPoly r) := by
    have he : (fun x => 1 - (Polynomial.X : O[X]) • (a x).map C) =
        1 - algebraMap O[X] (X → Matrix d d O[X]) Polynomial.X * (fun x => (a x).map C) := by
      funext x
      simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc]
    rw [he]
    exact Subalgebra.sub_mem _ (Subalgebra.one_mem _)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hA)
  exact detT T r hG1 _ hM k

theorem blockPolyT : StatBlockPolyT := by
  intro O _ X T d _ _ G _ r hG1 e he a ha k
  have hE : (fun x => (e x).map C) ∈ spanSub (polyT T) (rPoly r) := lift_mem T r he
  have hA : (fun x => (a x).map C) ∈ spanSub (polyT T) (rPoly r) := lift_mem T r ha
  have hM : (fun x => (Polynomial.X : O[X]) • (e x).map C - (a x).map C + (1 - e x).map C) ∈
      spanSub (polyT T) (rPoly r) := by
    have hq : (fun x => (Polynomial.X : O[X]) • (e x).map C - (a x).map C + (1 - e x).map C) =
        algebraMap O[X] (X → Matrix d d O[X]) Polynomial.X * (fun x => (e x).map C) -
          (fun x => (a x).map C) + (1 - fun x => (e x).map C) := by
      funext x
      ext i j
      by_cases h : i = j
      · subst h
        simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_apply]
      · simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_apply, h]
    rw [hq]
    exact Subalgebra.add_mem _ (Subalgebra.sub_mem _
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hE) hA)
      (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hE)
  exact detT T r hG1 _ hM k

end Formalism.RepresentationBoundsCohomology.ringDataObjects
