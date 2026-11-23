import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.Localization.FractionRing

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section SlopeTestRemainingChoices

variable {n : ℕ} {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
  (F : ∀ (S : Type) [CommRing S] [Algebra k S], Matrix ι ι S →* S)
  (nat : ∀ (S T : Type) [CommRing S] [Algebra k S] [CommRing T] [Algebra k T] (f : S →ₐ[k] T) (M : Matrix ι ι S),
    F T (M.map f) = f (F S M))
  (hom : ∀ (S : Type) [CommRing S] [Algebra k S] (b : S) (M : Matrix ι ι S), F S (b • M) = b ^ n * F S M)

include nat in
private theorem dm_transv (S : Type) [CommRing S] [Algebra k S] {i j : ι} (hij : i ≠ j) (s : S) :
    F S (Matrix.transvection i j s) = 1 := by
  have hm : ∀ (S : Type) [CommRing S] [Algebra k S] (s : S),
      F S (Matrix.transvection i j s) = aeval s (F k[X] (Matrix.transvection i j X)) := by
    intro S _ _ s
    rw [← nat]
    congr 1
    ext a b
    simp only [Matrix.transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, map_add]
    split_ifs <;> simp
  have hu : IsUnit (F k[X] (Matrix.transvection i j X)) := by
    refine IsUnit.of_mul_eq_one (F k[X] (Matrix.transvection i j (-X))) ?_
    rw [← map_mul, Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel, Matrix.transvection_zero, map_one]
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.1 hu
  have h0 := hm k 0
  rw [Matrix.transvection_zero, map_one, ← hc] at h0
  rw [hm, ← hc]
  simp at h0
  simp [← h0]

private theorem dm_diag_prod (S : Type) [CommRing S] [Algebra k S] (d : ι → S) :
    F S (Matrix.diagonal d) = ∏ i, F S (Matrix.diagonal (Pi.mulSingle i (d i))) := by
  have := map_prod ((F S).comp (Matrix.diagonalRingHom ι S).toMonoidHom) (fun i => Pi.mulSingle i (d i)) Finset.univ
  rw [Finset.univ_prod_mulSingle] at this
  exact this

include nat in
private theorem dm_single (S : Type) [CommRing S] [Algebra k S] (i : ι) (s : S) :
    F S (Matrix.diagonal (Pi.mulSingle i s)) = aeval s (F k[X] (Matrix.diagonal (Pi.mulSingle i X))) := by
  rw [← nat]
  congr 1
  ext a b
  simp only [Matrix.map_apply, Matrix.diagonal_apply, Pi.mulSingle_apply]
  split_ifs <;> simp

private theorem dm_swap (S : Type) [CommRing S] [Algebra k S] (i j : ι) (s : S) :
    F S (Matrix.diagonal (Pi.mulSingle i s)) = F S (Matrix.diagonal (Pi.mulSingle j s)) := by
  have h : Matrix.swap S i j * Matrix.diagonal (Pi.mulSingle i s) * Matrix.swap S i j =
      Matrix.diagonal (Pi.mulSingle j s) := by
    simp only [Matrix.swap, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, Pi.mulSingle_apply, id, Equiv.symm_swap,
      EmbeddingLike.apply_eq_iff_eq, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  rw [← h, map_mul, map_mul, mul_right_comm, ← map_mul, Matrix.swap_mul_self, map_one, one_mul]

include hom in
private theorem dm_X : ∏ i : ι, F k[X] (Matrix.diagonal (Pi.mulSingle i X)) = X ^ n := by
  have := hom k[X] X 1
  rw [map_one, mul_one, Matrix.smul_one_eq_diagonal, dm_diag_prod] at this
  exact this

include nat hom in
private theorem dm_diag [Nonempty ι] : ∃ m, n = m * Fintype.card ι ∧
    ∀ (S : Type) [CommRing S] [Algebra k S] (d : ι → S), F S (Matrix.diagonal d) = (Matrix.diagonal d).det ^ m := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have h := dm_X F hom
  have hd : F k[X] (Matrix.diagonal (Pi.mulSingle i₀ X)) ∣ X ^ n := h ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ i₀)
  obtain ⟨m, -, u, hu⟩ := (dvd_prime_pow Polynomial.prime_X n).1 hd
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.1 u.isUnit
  have h1 := dm_single F nat k i₀ 1
  rw [Pi.mulSingle_one, show (1 : ι → k) = fun _ => 1 from rfl, Matrix.diagonal_one, map_one] at h1
  have h2 := congrArg (aeval (1 : k)) hu
  rw [map_mul, ← h1, ← hc] at h2
  have hc1 : c = 1 := by simpa using h2
  rw [← hc, hc1, map_one, mul_one] at hu
  have hall : ∀ i : ι, F k[X] (Matrix.diagonal (Pi.mulSingle i X)) = X ^ m := fun i => (dm_swap F _ i i₀ _).trans hu
  refine ⟨m, ?_, fun S _ _ d => ?_⟩
  · simp only [hall, Finset.prod_const, Finset.card_univ, ← pow_mul] at h
    have := congrArg natDegree h
    simpa using this.symm
  · rw [dm_diag_prod, Matrix.det_diagonal, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [dm_single F nat, hall]
    simp

include nat hom in
private theorem dm_main [Nonempty ι] : ∃ m, n = m * Fintype.card ι ∧
    ∀ (S : Type) [CommRing S] [Algebra k S] (M : Matrix ι ι S), F S M = M.det ^ m := by
  obtain ⟨m, hm, hd⟩ := dm_diag F nat hom
  refine ⟨m, hm, fun S _ _ M => ?_⟩
  have hK : ∀ (K : Type) [Field K] [Algebra k K] (M : Matrix ι ι K), F K M = M.det ^ m := by
    intro K _ _ M
    refine Matrix.diagonal_transvection_induction (fun M => F K M = M.det ^ m) M (fun d _ => hd K d)
      (fun t => ?_) (fun A B hA hB => ?_)
    · rw [t.det, one_pow]
      exact dm_transv F nat K t.hij t.c
    · rw [map_mul, hA, hB, Matrix.det_mul, mul_pow]
  let R := MvPolynomial (ι × ι) k
  let G : Matrix ι ι R := Matrix.of fun i j => MvPolynomial.X (i, j)
  have hG : F R G = G.det ^ m := by
    apply IsFractionRing.injective R (FractionRing R)
    have := nat R (FractionRing R) (IsScalarTower.toAlgHom k R (FractionRing R)) G
    rw [hK] at this
    rw [map_pow, RingHom.map_det]
    exact this.symm
  have h := nat R S (MvPolynomial.aeval fun p => M p.1 p.2) G
  rw [hG, map_pow, AlgHom.map_det] at h
  have hM : G.map (MvPolynomial.aeval fun p : ι × ι => M p.1 p.2 : R →ₐ[k] S) = M := by
    ext a b
    simp [G, R]
  rw [AlgHom.mapMatrix_apply, hM] at h
  exact h

private theorem dm_rep (S : Type) [CommRing S] [Algebra k S] (y : S ⊗[k] Matrix ι ι k) :
    matrixEquivTensor ι k S (Det.repS (AlgHom.id k _) S y) = y := by
  rw [← AlgEquiv.eq_symm_apply]
  induction y with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s x =>
    rw [Det.repS_tmul, matrixEquivTensor_apply_symm]
    ext a b
    simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.CA.d_matrix :
    ∀ {n d : ℕ} {k : Type} [Field k] (D : Det n k (Matrix (Fin (d + 1)) (Fin (d + 1)) k)), ∃ m, n = m * (d + 1) ∧ ∀ (S : Type) [CommRing S] [Algebra k S] (y : S ⊗[k] Matrix (Fin (d + 1)) (Fin (d + 1)) k), D.D S y = (Det.repS (AlgHom.id k _) S y).det ^ m := by
  intro n d k _ D
  obtain ⟨m, hm, h⟩ := dm_main (n := n) (k := k) (ι := Fin (d + 1))
    (fun S _ _ => (D.D S).comp (matrixEquivTensor (Fin (d + 1)) k S).toAlgHom.toMonoidHom)
    (fun S T _ _ _ _ f M => by
      change D.D T (matrixEquivTensor _ k T (M.map f)) = f (D.D S (matrixEquivTensor _ k S M))
      rw [← D.nat]
      congr 1
      simp [matrixEquivTensor_apply, map_sum])
    (fun S _ _ b M => by
      change D.D S (matrixEquivTensor _ k S (b • M)) = b ^ n * D.D S (matrixEquivTensor _ k S M)
      rw [← D.homog]
      congr 1
      simp [matrixEquivTensor_apply, Finset.smul_sum, smul_tmul'])
  refine ⟨m, by simpa using hm, fun S _ _ y => ?_⟩
  rw [← h]
  exact congrArg (D.D S) (dm_rep S y).symm
