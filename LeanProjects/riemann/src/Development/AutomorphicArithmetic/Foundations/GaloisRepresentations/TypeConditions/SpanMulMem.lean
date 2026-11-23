import Mathlib

noncomputable section

namespace UpperTheory.GalS.Dbl

open Polynomial Matrix

theorem span_mul_mem {R P Γ : Type} [CommRing R] [Ring P] [Algebra R P] [Monoid Γ] (Φ : Γ →* P) {p q : P}
    (hp : p ∈ Submodule.span R (Set.range Φ)) (hq : q ∈ Submodule.span R (Set.range Φ)) :
    p * q ∈ Submodule.span R (Set.range Φ) := by
  have h := Submodule.mul_mem_mul hp hq
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
  exact ⟨a * b, map_mul Φ a b⟩

theorem span_pair {k Γ : Type} [Field k] [Monoid Γ] {a t : ℕ} (ha : 2 ≤ a) (ρ : Γ →* Matrix (Fin a) (Fin a) k)
    (χ : Fin t → Γ →* k) (hχ : Function.Injective χ) (hρ : Submodule.span k (Set.range ρ) = ⊤)
    (M : Matrix (Fin a) (Fin a) k) (v : Fin t → k) :
    (M, v) ∈ Submodule.span k (Set.range (ρ.prod (Pi.monoidHom χ))) := by
  set B := Submodule.span k (Set.range (ρ.prod (Pi.monoidHom χ))) with hB
  have h1 : ∀ N : Matrix (Fin a) (Fin a) k, ∃ w, (N, w) ∈ B := fun N => by
    have hN : N ∈ Submodule.span k (Set.range ρ) := hρ ▸ Submodule.mem_top
    induction hN using Submodule.span_induction with
    | mem _ h => obtain ⟨g, rfl⟩ := h; exact ⟨_, Submodule.subset_span ⟨g, rfl⟩⟩
    | zero => exact ⟨0, B.zero_mem⟩
    | add _ _ _ _ h h' => obtain ⟨w, h⟩ := h; obtain ⟨w', h'⟩ := h'; exact ⟨_, B.add_mem h h'⟩
    | smul c _ _ h => obtain ⟨w, h⟩ := h; exact ⟨_, B.smul_mem c h⟩
  have h2 : ∀ w : Fin t → k, ∃ N, (N, w) ∈ B := fun w => by
    have hli : LinearIndependent k (fun j => (χ j : Γ → k)) := (linearIndependent_monoidHom Γ k).comp χ hχ
    have hw : w ∈ Submodule.span k (Set.range (flip fun j => (χ j : Γ → k))) :=
      (span_flip_eq_top_iff_linearIndependent.2 hli) ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem _ h => obtain ⟨g, rfl⟩ := h; exact ⟨_, Submodule.subset_span ⟨g, rfl⟩⟩
    | zero => exact ⟨0, B.zero_mem⟩
    | add _ _ _ _ h h' => obtain ⟨w, h⟩ := h; obtain ⟨w', h'⟩ := h'; exact ⟨_, B.add_mem h h'⟩
    | smul c _ _ h => obtain ⟨w, h⟩ := h; exact ⟨_, B.smul_mem c h⟩
  have h3 : ∀ N N' : Matrix (Fin a) (Fin a) k, (N', (0 : Fin t → k)) ∈ B → (N * N', (0 : Fin t → k)) ∈ B := fun N N' h => by
    obtain ⟨w, hw⟩ := h1 N
    simpa using span_mul_mem (R := k) _ hw h
  have h4 : ∀ N N' : Matrix (Fin a) (Fin a) k, (N * N' - N' * N, (0 : Fin t → k)) ∈ B := fun N N' => by
    obtain ⟨w, hw⟩ := h1 N
    obtain ⟨w', hw'⟩ := h1 N'
    have := B.sub_mem (span_mul_mem (R := k) _ hw hw') (span_mul_mem (R := k) _ hw' hw)
    simpa [mul_comm w w'] using this
  haveI : Nontrivial (Fin a) := Fin.nontrivial_iff_two_le.2 ha
  have h5 : ∀ i : Fin a, (single i i (1 : k), (0 : Fin t → k)) ∈ B := fun i => by
    obtain ⟨j, hj⟩ := exists_ne i
    have e := h3 (single i j 1) _ (h4 (single j j 1) (single j i 1))
    rw [single_mul_single_same, single_mul_single_of_ne (h := hj.symm), sub_zero, single_mul_single_same] at e
    simpa using e
  have h6 : ((1 : Matrix (Fin a) (Fin a) k), (0 : Fin t → k)) ∈ B := by
    have := B.sum_mem (t := Finset.univ) fun i _ => h5 i
    rwa [← prod_mk_sum, sum_single_one, Finset.sum_const_zero] at this
  obtain ⟨N, hN⟩ := h2 v
  have := B.add_mem hN (h3 (M - N) 1 h6)
  simpa using this

theorem hankel_zero {K : Type} [Field K] {n d u : ℕ} (h : d + u < n) (A : Matrix (Fin d) (Fin d) K)
    (B : Matrix (Fin u) (Fin u) K) :
    (Matrix.of fun i j : Fin n => 2 * (A ^ ((i : ℕ) + j)).trace + (B ^ ((i : ℕ) + j)).trace).det = 0 := by
  have hm : (A.charpoly * B.charpoly).Monic := A.charpoly_monic.mul B.charpoly_monic
  have hdeg : (A.charpoly * B.charpoly).natDegree = d + u := by
    rw [A.charpoly_monic.natDegree_mul B.charpoly_monic]; simp
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun j => (A.charpoly * B.charpoly).coeff j, fun e => ?_, ?_⟩
  · have := congrFun e ⟨d + u, h⟩
    simp only [Pi.zero_apply] at this
    rw [← hdeg, hm.coeff_natDegree] at this
    exact one_ne_zero this
  · funext i
    have key : ∀ {m : ℕ} (C : Matrix (Fin m) (Fin m) K), aeval C (A.charpoly * B.charpoly) = 0 →
        ∑ j : Fin n, (C ^ ((i : ℕ) + j)).trace * (A.charpoly * B.charpoly).coeff j = 0 := fun C hC => by
      rw [aeval_eq_sum_range' (n := n) (by omega), Finset.sum_range] at hC
      have := congrArg (fun Z => (C ^ (i : ℕ) * Z).trace) hC
      simp only [Finset.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul, mul_zero, trace_zero, ← pow_add] at this
      simpa [mul_comm] using this
    have hA := key A (by rw [map_mul, Matrix.aeval_self_charpoly, zero_mul])
    have hB := key B (by rw [map_mul, Matrix.aeval_self_charpoly, mul_zero])
    simp only [mulVec, dotProduct, of_apply, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, hA, hB, Pi.zero_apply]
    simp

theorem hankel_ne {k : Type} [Field k] {n : ℕ} (ν : Fin n → k) (hν : Function.Injective ν) :
    (Matrix.of fun i j : Fin n => ∑ c, ν c ^ ((i : ℕ) + j)).det ≠ 0 := by
  have e : (Matrix.of fun i j : Fin n => ∑ c, ν c ^ ((i : ℕ) + j)) = (vandermonde ν)ᵀ * vandermonde ν := by
    ext i j; simp [Matrix.mul_apply, pow_add]
  rw [e, det_mul, det_transpose]
  exact mul_ne_zero (det_vandermonde_ne_zero_iff.2 hν) (det_vandermonde_ne_zero_iff.2 hν)

theorem core {O K k Γ : Type} [CommRing O] [Field K] [Field k] [Monoid Γ] (f : O →+* K) (hf : Function.Injective f)
    (res : O →+* k) (hres : Function.Surjective res) {a t d u : ℕ} (ha : 2 ≤ a) (hdu : d + u < a + t)
    (r : Γ →* Matrix (Fin (a + t)) (Fin (a + t)) O) (σ : Γ →* Matrix (Fin d) (Fin d) K) (υ : Γ →* Matrix (Fin u) (Fin u) K)
    (ρ : Γ →* Matrix (Fin a) (Fin a) k) (χ : Fin t → Γ →* k) (hχ : Function.Injective χ)
    (hρ : Submodule.span k (Set.range ρ) = ⊤)
    (h1 : ∀ g, f (r g).trace = 2 * (σ g).trace + (υ g).trace)
    (h2 : ∀ g, res (r g).trace = (ρ g).trace + ∑ j, χ j g) (ν : Fin (a + t) → k) (hν : Function.Injective ν) : False := by
  letI := f.toAlgebra
  letI := res.toAlgebra
  let Φ := r.prod ((σ.prod υ).prod (ρ.prod (Pi.monoidHom χ)))
  let S := Submodule.span O (Set.range Φ)
  have hS : ∀ p ∈ S, f p.1.trace = 2 * p.2.1.1.trace + p.2.1.2.trace ∧ res p.1.trace = p.2.2.1.trace + ∑ j, p.2.2.2 j := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem _ h => obtain ⟨g, rfl⟩ := h; exact ⟨h1 g, h2 g⟩
    | zero => simp
    | add _ _ _ _ h h' =>
      simp only [Prod.fst_add, Prod.snd_add, trace_add, map_add, h.1, h.2, h'.1, h'.2, Pi.add_apply, Finset.sum_add_distrib]
      constructor <;> ring
    | smul c _ _ h =>
      have a1 : ∀ z : K, c • z = f c * z := fun z => Algebra.smul_def c z
      have a2 : ∀ z : k, c • z = res c * z := fun z => Algebra.smul_def c z
      simp only [Prod.smul_fst, Prod.smul_snd, trace_smul, smul_eq_mul, map_mul, h.1, h.2, Pi.smul_apply, a1, a2,
        ← Finset.mul_sum]
      constructor <;> ring
  have hl : ∀ q ∈ Submodule.span k (Set.range (ρ.prod (Pi.monoidHom χ))), ∃ p ∈ S, p.2.2 = q := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem _ h => obtain ⟨g, rfl⟩ := h; exact ⟨Φ g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
    | zero => exact ⟨0, S.zero_mem, rfl⟩
    | add _ _ _ _ h h' => obtain ⟨p, hp, rfl⟩ := h; obtain ⟨p', hp', rfl⟩ := h'; exact ⟨_, S.add_mem hp hp', rfl⟩
    | smul c _ _ h =>
      obtain ⟨p, hp, rfl⟩ := h
      obtain ⟨c, rfl⟩ := hres c
      exact ⟨_, S.smul_mem c hp, (algebraMap_smul k c p.2.2).symm⟩
  obtain ⟨p, hp, e⟩ := hl _ (span_pair ha ρ χ hχ hρ (diagonal fun i => ν (Fin.castAdd t i)) fun j => ν (Fin.natAdd a j))
  have hpow : ∀ m : ℕ, p ^ m ∈ S := fun m => by
    induction m with
    | zero => exact Submodule.subset_span ⟨1, by rw [map_one, pow_zero]⟩
    | succ m ih => rw [pow_succ]; exact span_mul_mem Φ ih hp
  let Hm : Matrix (Fin (a + t)) (Fin (a + t)) O := Matrix.of fun i j => (p.1 ^ ((i : ℕ) + j)).trace
  have e1 : f.mapMatrix Hm = Matrix.of fun i j : Fin (a + t) =>
      2 * (p.2.1.1 ^ ((i : ℕ) + j)).trace + (p.2.1.2 ^ ((i : ℕ) + j)).trace := by
    ext i j; exact (hS _ (hpow _)).1
  have e2 : res.mapMatrix Hm = Matrix.of fun i j : Fin (a + t) => ∑ c, ν c ^ ((i : ℕ) + j) := by
    ext i j
    have := (hS _ (hpow ((i : ℕ) + j))).2
    simp only [Prod.pow_snd, Prod.pow_fst, e, diagonal_pow, trace_diagonal, Pi.pow_apply] at this
    rw [of_apply, Fin.sum_univ_add]
    exact this
  have z : Hm.det = 0 := hf (by rw [RingHom.map_det, e1, hankel_zero hdu, map_zero])
  exact hankel_ne ν hν (by rw [← e2, ← RingHom.map_det, z, map_zero])

end UpperTheory.GalS.Dbl
