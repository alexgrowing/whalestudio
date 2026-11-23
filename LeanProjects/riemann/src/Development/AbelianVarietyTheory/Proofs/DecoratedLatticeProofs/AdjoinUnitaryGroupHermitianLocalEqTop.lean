import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

noncomputable section

namespace GlobalTheory.UnitaryGen
variable {R : Type} [CommRing R] (s : R →+* R)

theorem refl_unitary (hs : ∀ x, s (s x) = x) {n : ℕ} (d : Fin n → R) (hd : ∀ k, s (d k) = d k)
    (c : R) (v : Fin n → R) (hc : c + s c + c * s c * ∑ k, s (v k) * d k * v k = 0) :
    cT s (1 + c • vecMulVec v (fun k => s (v k) * d k)) * diagonal d *
      (1 + c • vecMulVec v (fun k => s (v k) * d k)) = diagonal d := by
  ext a b
  set r := 1 + c • vecMulVec v (fun k => s (v k) * d k) with hr
  have e1 : ∀ k, cT s r a k * d k = (1 : Matrix (Fin n) (Fin n) R) a k * d k +
      (s c * (v a * d a)) * (s (v k) * d k) := by
    intro k
    simp only [hr, cT, transpose_apply, map_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
      map_add, map_mul, hs, hd]
    by_cases h : k = a
    · subst h; simp only [one_apply_eq, map_one]; ring
    · rw [one_apply_ne h, one_apply_ne (Ne.symm h), map_zero]; ring
  have e2 : ∀ k, r k b = (1 : Matrix (Fin n) (Fin n) R) k b + c * v k * (s (v b) * d b) := by
    intro k
    simp only [hr, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]; ring
  rw [mul_apply]
  simp only [mul_diagonal]
  rw [Finset.sum_congr rfl (fun k _ => by rw [e1, e2])]
  have e3 : ∀ k, ((1 : Matrix (Fin n) (Fin n) R) a k * d k + (s c * (v a * d a)) * (s (v k) * d k)) *
      ((1 : Matrix (Fin n) (Fin n) R) k b + c * v k * (s (v b) * d b)) =
      (1 : Matrix (Fin n) (Fin n) R) a k * (d k * (1 : Matrix (Fin n) (Fin n) R) k b) +
      (1 : Matrix (Fin n) (Fin n) R) a k * (d k * (c * v k * (s (v b) * d b))) +
      (1 : Matrix (Fin n) (Fin n) R) k b * ((s c * (v a * d a)) * (s (v k) * d k)) +
      (s c * (v a * d a) * c * (s (v b) * d b)) * (s (v k) * d k * v k) := fun k => by ring
  rw [Finset.sum_congr rfl (fun k _ => e3 k)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hab : a = b
  · subst hab; simp; linear_combination (v a * d a * (s (v a) * d a)) * hc
  · simp [hab]; linear_combination (v a * d a * (s (v b) * d b)) * hc

abbrev uAlg {n : ℕ} (J : Matrix (Fin n) (Fin n) R) : Subalgebra R (Matrix (Fin n) (Fin n) R) :=
  Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' (UJ s J : Set (GL (Fin n) R)))

theorem mem_uAlg_of_unitary {n : ℕ} {J : Matrix (Fin n) (Fin n) R} (hJ : IsUnit J.det)
    {M : Matrix (Fin n) (Fin n) R} (hM : cT s M * J * M = J) : M ∈ uAlg s J := by
  have hdet : IsUnit M.det := by
    have h := congrArg Matrix.det hM
    rw [det_mul] at h
    exact isUnit_of_mul_isUnit_right (h ▸ hJ)
  exact Algebra.subset_adjoin ⟨nonsingInvUnit M hdet, hM, rfl⟩

theorem isUnit_det_diagonal {n : ℕ} {d : Fin n → R} (hdu : ∀ k, IsUnit (d k)) : IsUnit (diagonal d).det := by
  rw [det_diagonal, isUnit_iff_exists_inv]
  exact ⟨∏ k, ((hdu k).unit⁻¹ : Rˣ), by rw [← Finset.prod_mul_distrib]; simp⟩

theorem vec_mem (hs : ∀ x, s (s x) = x) {ζ : R} (hζ : ζ * s ζ = 1) (hζ1 : IsUnit (ζ - 1)) {n : ℕ}
    {d : Fin n → R} (hdu : ∀ k, IsUnit (d k)) (hd : ∀ k, s (d k) = d k) (v : Fin n → R)
    (hN : IsUnit (∑ k, s (v k) * d k * v k)) :
    vecMulVec v (fun k => s (v k) * d k) ∈ uAlg s (diagonal d) := by
  set N := ∑ k, s (v k) * d k * v k with hNdef
  have hsN : s N = N := by
    rw [hNdef, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul, map_mul, hs, hd]; ring
  set Ni : R := ((hN.unit⁻¹ : Rˣ) : R) with hNidef
  have hNi : Ni * N = 1 := hN.val_inv_mul
  have hsNi' : s Ni * N = 1 := by rw [← hsN, ← map_mul, hNi, map_one]
  have hsNi : s Ni = Ni := by
    calc s Ni = s Ni * (N * Ni) := by rw [mul_comm N, hNi, mul_one]
      _ = (s Ni * N) * Ni := by ring
      _ = Ni := by rw [hsNi', one_mul]
  set c := (ζ - 1) * Ni with hcdef
  have hc : c + s c + c * s c * N = 0 := by
    rw [hcdef, map_mul, hsNi, map_sub, map_one]
    linear_combination ((ζ - 1) * (s ζ - 1) * Ni) * hNi + Ni * hζ
  have hcu : IsUnit c := hζ1.mul (Units.isUnit _)
  have hr := mem_uAlg_of_unitary s (isUnit_det_diagonal hdu) (refl_unitary s hs d hd c v hc)
  have hX : vecMulVec v (fun k => s (v k) * d k) =
      ((hcu.unit⁻¹ : Rˣ) : R) • ((1 + c • vecMulVec v (fun k => s (v k) * d k)) - 1) := by
    rw [add_sub_cancel_left, smul_smul, hcu.val_inv_mul, one_smul]
  rw [hX]
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ hr (Subalgebra.one_mem _)) _

theorem single_mem_of_isUnit {n : ℕ} {J : Matrix (Fin n) (Fin n) R} (i j : Fin n) {u : R} (hu : IsUnit u)
    (h : single i j u ∈ uAlg s J) : single i j (1 : R) ∈ uAlg s J := by
  have : single i j (1 : R) = ((hu.unit⁻¹ : Rˣ) : R) • single i j u := by
    rw [smul_single, smul_eq_mul, hu.val_inv_mul]
  rw [this]; exact Subalgebra.smul_mem _ h _

theorem ind_mem (hs : ∀ x, s (s x) = x) {ζ : R} (hζ : ζ * s ζ = 1) (hζ1 : IsUnit (ζ - 1)) {n : ℕ}
    {d : Fin n → R} (hdu : ∀ k, IsUnit (d k)) (hd : ∀ k, s (d k) = d k) (S : Finset (Fin n))
    (hN : IsUnit (∑ k ∈ S, d k)) :
    vecMulVec (fun k => if k ∈ S then (1 : R) else 0) (fun k => if k ∈ S then d k else 0) ∈ uAlg s (diagonal d) := by
  have h := vec_mem s hs hζ hζ1 hdu hd (fun k => if k ∈ S then (1 : R) else 0) (by
    convert hN using 1
    rw [← Finset.univ_inter S, ← Finset.sum_ite_mem]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp_all)
  convert h using 2
  funext k
  split_ifs <;> simp

theorem single_mem_diag (hs : ∀ x, s (s x) = x) [IsLocalRing R] {ζ : R} (hζ : ζ * s ζ = 1) (hζ1 : IsUnit (ζ - 1))
    {n : ℕ} (hn : 3 ≤ n) {d : Fin n → R} (hdu : ∀ k, IsUnit (d k)) (hd : ∀ k, s (d k) = d k) (i j : Fin n) :
    single i j (1 : R) ∈ uAlg s (diagonal d) := by
  have hii : ∀ i, single i i (1 : R) ∈ uAlg s (diagonal d) := by
    intro i
    have h := ind_mem s hs hζ hζ1 hdu hd {i} (by simpa using hdu i)
    refine single_mem_of_isUnit s i i (hdu i) ?_
    convert h using 1
    ext a b
    by_cases ha : a = i <;> by_cases hb : b = i <;> simp [vecMulVec_apply, single_apply, ha, hb] <;> intros <;> simp_all
  have hS : ∀ S : Finset (Fin n), i ∈ S → j ∈ S → IsUnit (∑ k ∈ S, d k) →
      single i j (1 : R) ∈ uAlg s (diagonal d) := by
    intro S hi hj hN
    have h := ind_mem s hs hζ hζ1 hdu hd S hN
    have h2 := Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hii i) h) (hii j)
    rw [single_mul_mul_single] at h2
    refine single_mem_of_isUnit s i j ?_ h2
    simpa [vecMulVec_apply, hi, hj] using hdu j
  by_cases hij : i = j
  · subst hij; exact hii i
  by_cases hu : IsUnit (d i + d j)
  · exact hS {i, j} (by simp) (by simp) (by rwa [Finset.sum_pair hij])
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {i, j}) (t := Finset.univ) (by
    rw [Finset.card_univ, Fintype.card_fin]; exact lt_of_le_of_lt Finset.card_le_two (by omega))
  refine hS {l, i, j} (by simp) (by simp) ?_
  rw [Finset.sum_insert hl, Finset.sum_pair hij]
  by_contra h
  have h1 : d l + (d i + d j) + -(d i + d j) ∈ nonunits R :=
    IsLocalRing.nonunits_add h (by rw [mem_nonunits_iff, IsUnit.neg_iff]; exact hu)
  rw [add_neg_cancel_right] at h1
  exact h1 (hdu l)

theorem eq_top_of_single {n : ℕ} {A : Subalgebra R (Matrix (Fin n) (Fin n) R)}
    (h : ∀ i j, single i j (1 : R) ∈ A) : A = ⊤ := by
  refine eq_top_iff.2 fun M _ => ?_
  rw [matrix_eq_sum_single M]
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => ?_
  have : single i j (M i j) = M i j • single i j (1 : R) := by rw [smul_single, smul_eq_mul, mul_one]
  rw [this]; exact Subalgebra.smul_mem _ (h i j) _

theorem isUnit_det_cT {n : ℕ} {Q : Matrix (Fin n) (Fin n) R} (hQ : IsUnit Q.det) : IsUnit (cT s Q).det := by
  rw [cT, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact hQ.map s

theorem uAlg_conj {n : ℕ} {J Q : Matrix (Fin n) (Fin n) R} (hQ : IsUnit Q.det) (hJ : IsUnit J.det)
    {M : Matrix (Fin n) (Fin n) R} (hM : M ∈ uAlg s J) : Q⁻¹ * M * Q ∈ uAlg s (cT s Q * J * Q) := by
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQ
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQ
  refine Algebra.adjoin_induction (p := fun M _ => Q⁻¹ * M * Q ∈ uAlg s (cT s Q * J * Q)) ?_ ?_ ?_ ?_ hM
  · rintro x ⟨g, hg, rfl⟩
    refine mem_uAlg_of_unitary s ?_ ?_
    · rw [det_mul, det_mul]
      exact ((isUnit_det_cT s hQ).mul hJ).mul hQ
    · have hg' : cT s (g : Matrix (Fin n) (Fin n) R) * J * (g : Matrix (Fin n) (Fin n) R) = J := hg
      have hc1 : cT s (Q⁻¹) * cT s Q = 1 := by rw [← cT_mul, hQQ, cT_one]
      calc cT s (Q⁻¹ * (g : Matrix (Fin n) (Fin n) R) * Q) * (cT s Q * J * Q) * (Q⁻¹ * (g : Matrix (Fin n) (Fin n) R) * Q)
          = cT s Q * (cT s (g : Matrix (Fin n) (Fin n) R) * (cT s (Q⁻¹) * cT s Q) * J * (Q * Q⁻¹) *
              (g : Matrix (Fin n) (Fin n) R)) * Q := by
            rw [cT_mul, cT_mul]; simp only [Matrix.mul_assoc]
        _ = cT s Q * J * Q := by rw [hc1, hQQ, Matrix.mul_one, Matrix.mul_one, hg']
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQQ', ← Algebra.algebraMap_eq_smul_one]
    exact Subalgebra.algebraMap_mem _ r
  · intro x y _ _ hx hy
    rw [Matrix.mul_add, Matrix.add_mul]; exact Subalgebra.add_mem _ hx hy
  · intro x y _ _ hx hy
    have : Q⁻¹ * (x * y) * Q = (Q⁻¹ * x * Q) * (Q⁻¹ * y * Q) := by
      calc Q⁻¹ * (x * y) * Q = Q⁻¹ * x * (Q * Q⁻¹) * y * Q := by rw [hQQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = (Q⁻¹ * x * Q) * (Q⁻¹ * y * Q) := by simp only [Matrix.mul_assoc]
    rw [this]; exact Subalgebra.mul_mem _ hx hy

theorem adjoin_unitary_eq_top : ∀ (R : Type) [CommRing R] [IsLocalRing R] (s : R →+* R), (∀ x, s (s x) = x) →
    (∃ δ : R, IsUnit (δ - s δ)) → ∀ n : ℕ, 3 ≤ n → ∀ G : Matrix (Fin n) (Fin n) R, cT s G = G → IsUnit G →
    Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' (UJ s G : Set (GL (Fin n) R))) = ⊤ := by
  intro R _ _ s hs ⟨δ, hδ⟩ n hn G hG hGu
  obtain ⟨δ', hδ'u, hδ'⟩ : ∃ δ', IsUnit δ' ∧ IsUnit (δ' - s δ') := by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self δ with h | h
    · exact ⟨δ, h, hδ⟩
    · refine ⟨1 - δ, h, ?_⟩
      have : 1 - δ - s (1 - δ) = -(δ - s δ) := by rw [map_sub, map_one]; ring
      rw [this, IsUnit.neg_iff]; exact hδ
  have hsu : IsUnit (s δ') := hδ'u.map s
  set i : R := ((hsu.unit⁻¹ : Rˣ) : R) with hidef
  have h1 : i * s δ' = 1 := hsu.val_inv_mul
  have h2 : s i * δ' = 1 := by have := congrArg s h1; rwa [map_mul, hs, map_one] at this
  have hζ : δ' * i * s (δ' * i) = 1 := by
    rw [map_mul]; linear_combination (δ' * s i) * h1 + h2
  have hζ1 : IsUnit (δ' * i - 1) := by
    have : δ' * i - 1 = (δ' - s δ') * i := by linear_combination h1
    rw [this]; exact hδ'.mul (Units.isUnit _)

  have hw : ∃ w, w + s w = 1 := by
    set ui : R := ((hδ.unit⁻¹ : Rˣ) : R)
    have e1 : ui * (δ - s δ) = 1 := hδ.val_inv_mul
    have e2 : s ui * (s δ - δ) = 1 := by have := congrArg s e1; rwa [map_mul, map_sub, hs, map_one] at this
    have e3 : s ui = -ui := by
      calc s ui = s ui * ((δ - s δ) * ui) := by rw [mul_comm (δ - s δ), e1, mul_one]
        _ = -(s ui * (s δ - δ)) * ui := by ring
        _ = -ui := by rw [e2]; ring
    refine ⟨δ * ui, ?_⟩
    rw [map_mul, e3]; linear_combination e1
  have hGab : ∀ a b, s (G a b) = G b a := fun a b => congrFun (congrFun hG b) a
  have hdetG : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hGu
  obtain ⟨P, d, hP, hdu, hd, hGe⟩ := GlobalTheory.UnramifiedHermitian.exists_eq_diagonal_of_isUnit_or s hs
    (fun x _ => IsLocalRing.isUnit_or_isUnit_one_sub_self x) hw hGab hdetG
  set Q := P.map s with hQdef
  have hcQ : cT s Q = Pᵀ := by
    ext a b; simp [cT, hQdef, hs]
  have hQ : IsUnit Q.det := by
    rw [hQdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hP.map s
  have hGQ : cT s Q * diagonal d * Q = G := by rw [hcQ, hGe]
  have htop := eq_top_of_single (single_mem_diag s hs hζ hζ1 hn hdu hd)
  refine eq_top_of_single (A := uAlg s G) fun a b => ?_
  have hm := uAlg_conj s hQ (isUnit_det_diagonal hdu) (M := Q * single a b (1 : R) * Q⁻¹) (by rw [htop]; trivial)
  rw [hGQ] at hm
  have : Q⁻¹ * (Q * single a b (1 : R) * Q⁻¹) * Q = single a b 1 := by
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hQ, Matrix.mul_one]
  rwa [this] at hm

end GlobalTheory.UnitaryGen

end
