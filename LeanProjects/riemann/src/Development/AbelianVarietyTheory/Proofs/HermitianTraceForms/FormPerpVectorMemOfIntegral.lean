import Mathlib

open scoped BigOperators Nat

namespace GlobalTheory

section Covector

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

def pairingMatrix (ε : ι → Module.Dual R M) (e' : ι → M) : Matrix ι ι R :=
  Matrix.of fun a' a => ε a (e' a')

def perpVector (ε : ι → Module.Dual R M) (e' : ι → M) (g : M) : M :=
  (pairingMatrix ε e').det • g
    - ∑ a, ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a'

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem pairingMatrix_apply (ε : ι → Module.Dual R M) (e' : ι → M) (a' a : ι) :
    pairingMatrix ε e' a' a = ε a (e' a') := rfl

theorem apply_perpVector (ε : ι → Module.Dual R M) (e' : ι → M) (g : M) (c : ι) :
    ε c (perpVector ε e' g) = 0 := by
  have key : ∀ a, ∑ a', (pairingMatrix ε e').adjugate a a' * ε a g * ε c (e' a')
      = ε a g * ((pairingMatrix ε e').det * if a = c then 1 else 0) := by
    intro a
    have h := congrFun (congrFun (Matrix.adjugate_mul (pairingMatrix ε e')) a) c
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [pairingMatrix_apply]; ring
  simp only [perpVector, map_sub, map_sum, map_smul, smul_eq_mul, key]
  simp [mul_comm]

theorem perpVector_of_apply_eq_zero (ε : ι → Module.Dual R M) (e' : ι → M) {g : M}
    (hg : ∀ a, ε a g = 0) : perpVector ε e' g = (pairingMatrix ε e').det • g := by
  simp [perpVector, hg]

theorem map_perpVector {S N : Type*} [CommRing S] [AddCommGroup N] [Module S N] {ρ : R →+* S}
    (ψ : M →ₛₗ[ρ] N) (ε : ι → Module.Dual R M) (η : ι → Module.Dual S N) (e' : ι → M) (g : M)
    (he : ∀ a a', η a (ψ (e' a')) = ρ (ε a (e' a'))) (hg : ∀ a, η a (ψ g) = ρ (ε a g)) :
    ψ (perpVector ε e' g) = perpVector η (fun a => ψ (e' a)) (ψ g) := by
  have hm : pairingMatrix η (fun a => ψ (e' a)) = ρ.mapMatrix (pairingMatrix ε e') := by
    ext a' a; simp [he]
  simp only [perpVector, map_sub, map_sum, LinearMap.map_smulₛₗ, hm, ← RingHom.map_det,
    ← RingHom.map_adjugate, hg, map_mul]
  simp

section Integral

variable {A : Type*} [CommRing A] [Algebra A R]

theorem det_pairingMatrix_mem_range (ε : ι → Module.Dual R M) (e' : ι → M)
    (he : ∀ a a', ε a (e' a') ∈ (algebraMap A R).range) :
    (pairingMatrix ε e').det ∈ (algebraMap A R).range := by
  choose x hx using he
  have hm : pairingMatrix ε e' = (algebraMap A R).mapMatrix (Matrix.of fun a' a => x a a') := by
    ext a' a; simp [hx]
  exact ⟨(Matrix.of fun a' a => x a a').det, by rw [hm, RingHom.map_det]⟩

theorem perpVector_mem [Module A M] [IsScalarTower A R M] (L : Submodule A M)
    (ε : ι → Module.Dual R M) {e' : ι → M} {g : M} (he' : ∀ a, e' a ∈ L) (hgL : g ∈ L)
    (he : ∀ a a', ε a (e' a') ∈ (algebraMap A R).range)
    (hg : ∀ a, ε a g ∈ (algebraMap A R).range) : perpVector ε e' g ∈ L := by
  choose x hx using he
  choose y hy using hg
  have hm : pairingMatrix ε e' = (algebraMap A R).mapMatrix (Matrix.of fun a' a => x a a') := by
    ext a' a; simp [hx]
  rw [perpVector, hm, ← RingHom.map_det, ← RingHom.map_adjugate]
  refine L.sub_mem ?_ (L.sum_mem fun a _ => L.sum_mem fun a' _ => ?_)
  · rw [algebraMap_smul]; exact L.smul_mem _ hgL
  · rw [← hy, RingHom.mapMatrix_apply, Matrix.map_apply, ← map_mul, algebraMap_smul]
    exact L.smul_mem _ (he' a')

end Integral

end Covector

section Size

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private theorem seminorm_sum_le {G κ : Type*} [AddCommGroup G] (ν : AddGroupSeminorm G)
    (s : Finset κ) (x : κ → G) {C : ℝ} (hx : ∀ k ∈ s, ν (x k) ≤ C) :
    ν (∑ k ∈ s, x k) ≤ s.card * C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.card_insert_of_notMem hk]
    have h1 := map_add_le_add ν (x k) (∑ k ∈ s, x k)
    have h2 := hx k (Finset.mem_insert_self _ _)
    have h3 := ih fun j hj => hx j (Finset.mem_insert_of_mem hj)
    push_cast
    linarith

private theorem ringSeminorm_prod_le {κ : Type*} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (s : Finset κ) (x : κ → R) {C : ℝ} (hx : ∀ k ∈ s, ν (x k) ≤ C) :
    ν (∏ k ∈ s, x k) ≤ C ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h1
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.card_insert_of_notMem hk, pow_succ']
    have h2 := hx k (Finset.mem_insert_self _ _)
    have h3 := ih fun j hj => hx j (Finset.mem_insert_of_mem hj)
    exact (map_mul_le_mul ν _ _).trans
      (mul_le_mul h2 h3 (apply_nonneg ν _) ((apply_nonneg ν _).trans h2))

theorem ringSeminorm_det_le {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : RingSeminorm R)
    (h1 : ν 1 ≤ 1) (H : Matrix ι ι R) {C : ℝ} (hH : ∀ i j, ν (H i j) ≤ C) :
    ν H.det ≤ (Fintype.card ι)! * C ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  have := seminorm_sum_le ν.toAddGroupSeminorm Finset.univ
    (fun σ : Equiv.Perm ι => Equiv.Perm.sign σ • ∏ i, H (σ i) i) (C := C ^ Fintype.card ι) (by
      intro σ _
      have h := ringSeminorm_prod_le ν h1 Finset.univ (fun i => H (σ i) i) fun i _ => hH _ _
      rw [Finset.card_univ] at h
      change ν _ ≤ _
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]; exact h
      · rw [hs, Units.neg_smul, one_smul, map_neg_eq_map]; exact h)
  rwa [Finset.card_univ, Fintype.card_perm] at this

theorem ringSeminorm_adjugate_le {n : ℕ} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) R) {C : ℝ} (hH : ∀ i j, ν (H i j) ≤ C)
    (i j : Fin (n + 1)) : ν (H.adjugate i j) ≤ n ! * C ^ n := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have h := ringSeminorm_det_le ν h1 (H.submatrix j.succAbove i.succAbove) (C := C)
    fun _ _ => hH _ _
  rw [Fintype.card_fin] at h
  rcases neg_one_pow_eq_or R ((j : ℕ) + i) with hs | hs
  · rw [hs, one_mul]; exact h
  · rw [hs, neg_one_mul, map_neg_eq_map]; exact h

theorem seminorm_perpVector_le {p : ℕ} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (μ : AddGroupSeminorm M) (hsmul : ∀ (x : R) (v : M), μ (x • v) ≤ ν x * μ v)
    (ε : Fin p → Module.Dual R M) (e' : Fin p → M) (g : M) {C r : ℝ}
    (he : ∀ a a', ν (ε a (e' a')) ≤ C) (hg : ∀ a, ν (ε a g) ≤ C)
    (he' : ∀ a, μ (e' a) ≤ r) (hgr : μ g ≤ r) :
    μ (perpVector ε e' g) ≤ (p + 1)! * C ^ p * r := by
  have hdet := ringSeminorm_det_le ν h1 (pairingMatrix ε e') (C := C) fun i j => he j i
  rw [Fintype.card_fin] at hdet
  have hA : μ ((pairingMatrix ε e').det • g) ≤ p ! * C ^ p * r :=
    (hsmul _ _).trans (mul_le_mul hdet hgr (apply_nonneg μ _) ((apply_nonneg ν _).trans hdet))
  have hB : μ (∑ a, ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
      ≤ p * (p ! * C ^ p * r) := by
    cases p with
    | zero => simp
    | succ n =>
      have h := seminorm_sum_le μ Finset.univ
        (fun a => ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
        (C := ((n + 1 : ℕ) : ℝ) * (n ! * C ^ n * C * r)) (by
          intro a _
          have h' := seminorm_sum_le μ Finset.univ
            (fun a' => ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
            (C := n ! * C ^ n * C * r) (by
              intro a' _
              have hadj := ringSeminorm_adjugate_le ν h1 (pairingMatrix ε e') (C := C)
                (fun i j => he j i) a a'
              have hm : ν ((pairingMatrix ε e').adjugate a a' * ε a g) ≤ n ! * C ^ n * C :=
                (map_mul_le_mul ν _ _).trans
                  (mul_le_mul hadj (hg a) (apply_nonneg ν _) ((apply_nonneg ν _).trans hadj))
              exact (hsmul _ _).trans
                (mul_le_mul hm (he' a') (apply_nonneg μ _) ((apply_nonneg ν _).trans hm)))
          rwa [Finset.card_univ, Fintype.card_fin] at h')
      rw [Finset.card_univ, Fintype.card_fin] at h
      refine h.trans (le_of_eq ?_)
      rw [Nat.factorial_succ]; push_cast; ring
  have hsub := map_sub_le_add μ ((pairingMatrix ε e').det • g)
    (∑ a, ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
  rw [perpVector, Nat.factorial_succ]
  push_cast
  linarith

end Size

section Degree

open MvPolynomial

variable {S τ : Type*} [CommRing S]

theorem totalDegree_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι (MvPolynomial τ S)) {d : ℕ} (hH : ∀ i j, (H i j).totalDegree ≤ d) :
    H.det.totalDegree ≤ Fintype.card ι * d := by
  rw [Matrix.det_apply]
  refine totalDegree_finsetSum_le fun σ _ => ?_
  have h : (∏ i, H (σ i) i).totalDegree ≤ Fintype.card ι * d :=
    (totalDegree_finsetProd _ _).trans <| by
      simpa using Finset.sum_le_card_nsmul Finset.univ (fun i => (H (σ i) i).totalDegree) d
        fun i _ => hH _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact h
  · rw [hs, Units.neg_smul, one_smul, totalDegree_neg]; exact h

theorem totalDegree_perpVector_le {p : ℕ} {κ : Type*}
    (ε : Fin p → Module.Dual (MvPolynomial τ S) (κ → MvPolynomial τ S))
    (e' : Fin p → κ → MvPolynomial τ S) (g : κ → MvPolynomial τ S) {d m : ℕ}
    (he : ∀ a a', (ε a (e' a')).totalDegree ≤ d) (hg : ∀ a, (ε a g).totalDegree ≤ d)
    (he' : ∀ a k, (e' a k).totalDegree ≤ m) (hgm : ∀ k, (g k).totalDegree ≤ m) (k : κ) :
    (perpVector ε e' g k).totalDegree ≤ p * d + m := by
  have hdet := totalDegree_det_le (pairingMatrix ε e') (d := d) fun i j => he j i
  rw [Fintype.card_fin] at hdet
  simp only [perpVector, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_mul _ _).trans (add_le_add hdet (hgm k))
  · refine totalDegree_finsetSum_le fun a _ => totalDegree_finsetSum_le fun a' _ => ?_
    refine (totalDegree_mul _ _).trans (add_le_add ?_ (he' a' k))
    cases p with
    | zero => exact a.elim0
    | succ n =>
      refine (totalDegree_mul _ _).trans ?_
      rw [Nat.succ_mul]
      refine add_le_add ?_ (hg a)
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      have h := totalDegree_det_le ((pairingMatrix ε e').submatrix a'.succAbove a.succAbove)
        (d := d) fun _ _ => he _ _
      rw [Fintype.card_fin] at h
      rcases neg_one_pow_eq_or (MvPolynomial τ S) ((a' : ℕ) + a) with hs | hs
      · rw [hs, one_mul]; exact h
      · rw [hs, neg_one_mul, totalDegree_neg]; exact h

end Degree

section Form

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
  {σ : R →+* R}

def formPairMatrix (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) : Matrix ι ι R :=
  pairingMatrix (fun a => h.flip (e a)) e'

def formPerpVector (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) (g : M) : M :=
  perpVector (fun a => h.flip (e a)) e' g

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem formPairMatrix_apply (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) (a' a : ι) :
    formPairMatrix h e e' a' a = h (e' a') (e a) := rfl

theorem formPerpVector_eq (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) (g : M) :
    formPerpVector h e e' g = (formPairMatrix h e e').det • g
      - ∑ a, ∑ a', ((formPairMatrix h e e').adjugate a a' * h g (e a)) • e' a' := rfl

theorem form_formPerpVector (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) (g : M) (c : ι) :
    h (formPerpVector h e e' g) (e c) = 0 :=
  apply_perpVector (fun a => h.flip (e a)) e' g c

theorem formPerpVector_of_perp (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) {g : M}
    (hg : ∀ a, h g (e a) = 0) : formPerpVector h e e' g = (formPairMatrix h e e').det • g :=
  perpVector_of_apply_eq_zero (fun a => h.flip (e a)) e' hg

theorem formPerpVector_mem {A : Type*} [CommRing A] [Algebra A R] [Module A M]
    [IsScalarTower A R M] (L : Submodule A M) (h : M →ₗ[R] M →ₛₗ[σ] R) (e : ι → M) {e' : ι → M}
    {g : M} (he' : ∀ a, e' a ∈ L) (hgL : g ∈ L)
    (he : ∀ a a', h (e' a') (e a) ∈ (algebraMap A R).range)
    (hg : ∀ a, h g (e a) ∈ (algebraMap A R).range) : formPerpVector h e e' g ∈ L :=
  perpVector_mem L (fun a => h.flip (e a)) he' hgL he hg

theorem formPerpVector_mem_of_integral {A : Type*} [CommRing A] [Algebra A R] [Module A M]
    [IsScalarTower A R M] (L : Submodule A M) (h : M →ₗ[R] M →ₛₗ[σ] R)
    (hL : ∀ u ∈ L, ∀ v ∈ L, h u v ∈ (algebraMap A R).range) {e e' : ι → M} {g : M}
    (he : ∀ a, e a ∈ L) (he' : ∀ a, e' a ∈ L) (hg : g ∈ L) : formPerpVector h e e' g ∈ L :=
  formPerpVector_mem L h e he' hg (fun a a' => hL _ (he' a') _ (he a))
    fun a => hL _ hg _ (he a)

theorem formPerpVector_mem_subring (A : Subring R) (L : Submodule A M)
    (h : M →ₗ[R] M →ₛₗ[σ] R) (e : ι → M) {e' : ι → M} {g : M} (he' : ∀ a, e' a ∈ L) (hgL : g ∈ L)
    (he : ∀ a a', h (e' a') (e a) ∈ A) (hg : ∀ a, h g (e a) ∈ A) :
    formPerpVector h e e' g ∈ L :=
  formPerpVector_mem L h e he' hgL (fun a a' => ⟨⟨_, he a a'⟩, rfl⟩) fun a => ⟨⟨_, hg a⟩, rfl⟩

theorem seminorm_formPerpVector_le {p : ℕ} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (μ : AddGroupSeminorm M) (hsmul : ∀ (x : R) (v : M), μ (x • v) ≤ ν x * μ v)
    (h : M →ₗ[R] M →ₛₗ[σ] R) (hcs : ∀ u v, ν (h u v) ≤ μ u * μ v)
    (e e' : Fin p → M) (g : M) {r : ℝ}
    (he : ∀ a, μ (e a) ≤ r) (he' : ∀ a, μ (e' a) ≤ r) (hg : μ g ≤ r) :
    μ (formPerpVector h e e' g) ≤ (p + 1)! * r ^ (2 * p + 1) := by
  have hr : 0 ≤ r := (apply_nonneg μ g).trans hg
  have key : ∀ u v, μ u ≤ r → μ v ≤ r → ν (h u v) ≤ r ^ 2 := fun u v hu hv =>
    (hcs u v).trans (by rw [sq]; exact mul_le_mul hu hv (apply_nonneg μ _) hr)
  have := seminorm_perpVector_le ν h1 μ hsmul (fun a => h.flip (e a)) e' g (C := r ^ 2)
    (fun a a' => key _ _ (he' a') (he a)) (fun a => key _ _ hg (he a)) he' hg
  rwa [← pow_mul, mul_assoc, ← pow_succ] at this

theorem seminorm_det_formPairMatrix_le {p : ℕ} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (μ : AddGroupSeminorm M) (h : M →ₗ[R] M →ₛₗ[σ] R) (hcs : ∀ u v, ν (h u v) ≤ μ u * μ v)
    (e e' : Fin p → M) {r : ℝ} (he : ∀ a, μ (e a) ≤ r) (he' : ∀ a, μ (e' a) ≤ r) :
    ν (formPairMatrix h e e').det ≤ p ! * r ^ (2 * p) := by
  have := ringSeminorm_det_le ν h1 (formPairMatrix h e e') (C := r ^ 2) fun i j =>
    (hcs _ _).trans (by
      rw [sq]
      exact mul_le_mul (he' i) (he j) (apply_nonneg μ _) ((apply_nonneg μ _).trans (he' i)))
  rwa [Fintype.card_fin, ← pow_mul] at this

end Form

theorem factorial_mul_pow_mono {p N : ℕ} (hp : p ≤ N) {r : ℝ} (hr : 1 ≤ r) :
    ((p + 1)! : ℝ) * r ^ (2 * p + 1) ≤ (N + 1)! * r ^ (2 * N + 1) := by
  gcongr

section InnerProduct

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]

noncomputable def innerFormLeft (V : Type*) [SeminormedAddCommGroup V] [InnerProductSpace ℂ V] :
    V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  (innerₛₗ ℂ).flip

@[simp] theorem innerFormLeft_apply (u v : V) : innerFormLeft V u v = inner ℂ v u := rfl

theorem norm_innerFormLeft_le (u v : V) : ‖innerFormLeft V u v‖ ≤ ‖u‖ * ‖v‖ := by
  rw [innerFormLeft_apply, mul_comm]; exact norm_inner_le_norm v u

theorem norm_det_formPairMatrix_le {p : ℕ} (e e' : Fin p → V) {r : ℝ} (he : ∀ a, ‖e a‖ ≤ r)
    (he' : ∀ a, ‖e' a‖ ≤ r) :
    ‖(formPairMatrix (innerFormLeft V) e e').det‖ ≤ p ! * r ^ (2 * p) :=
  seminorm_det_formPairMatrix_le (normRingSeminorm ℂ) (norm_one (α := ℂ)).le
    (normAddGroupSeminorm V) (innerFormLeft V) norm_innerFormLeft_le e e' he he'

theorem norm_formPerpVector_le {p : ℕ} (e e' : Fin p → V) (g : V) {r : ℝ} (he : ∀ a, ‖e a‖ ≤ r)
    (he' : ∀ a, ‖e' a‖ ≤ r) (hg : ‖g‖ ≤ r) :
    ‖formPerpVector (innerFormLeft V) e e' g‖ ≤ (p + 1)! * r ^ (2 * p + 1) :=
  seminorm_formPerpVector_le (normRingSeminorm ℂ) (norm_one (α := ℂ)).le
    (normAddGroupSeminorm V) (fun x v => norm_smul_le x v) (innerFormLeft V)
    norm_innerFormLeft_le e e' g he he' hg

end InnerProduct

section Places

variable {R M T : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]

theorem normSq_place_form_le (h : M →ₗ[R] M →ₗ⋆[R] R) (hh : ∀ u v, h u v = star (h v u))
    (τ : R →+* ℂ) (hτ : ∀ x, τ (star x) = starRingEnd ℂ (τ x))
    (hpos : ∀ v, 0 ≤ (τ (h v v)).re) (u v : M) :
    ‖τ (h u v)‖ ^ 2 ≤ (τ (h u u)).re * (τ (h v v)).re := by
  have him : ∀ w, (τ (h w w)).im = 0 := fun w => by
    have := congrArg Complex.im (hτ (h w w))
    rw [← hh, Complex.conj_im] at this
    linarith
  have hvu : τ (h v u) = starRingEnd ℂ (τ (h u v)) := by rw [hh v u, hτ]
  have expand : ∀ x y : R, τ (h (x • u + y • v) (x • u + y • v))
      = τ x * starRingEnd ℂ (τ x) * τ (h u u) + τ x * starRingEnd ℂ (τ y) * τ (h u v)
        + τ y * starRingEnd ℂ (τ x) * starRingEnd ℂ (τ (h u v))
        + τ y * starRingEnd ℂ (τ y) * τ (h v v) := by
    intro x y
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, starRingEnd_apply, hτ, hvu]
    ring
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  set a := (τ (h u u)).re with ha
  set c := (τ (h v v)).re with hc
  set b₁ := (τ (h u v)).re with hb₁
  set b₂ := (τ (h u v)).im with hb₂
  have ha0 : 0 ≤ a := hpos u
  have hc0 : 0 ≤ c := hpos v
  rcases hc0.eq_or_lt with hc1 | hc1
  · have hn : ∀ n : ℕ, 2 * n * (b₁ * b₁ + b₂ * b₂) ≤ a := by
      intro n
      have := hpos ((1 : R) • u + (-((n : R) * h u v)) • v)
      rw [expand] at this
      simp only [map_one, map_neg, map_mul, map_natCast, Complex.add_re, Complex.mul_re,
        Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im,
        Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im, him, ← ha, ← hc, ← hb₁,
        ← hb₂, ← hc1] at this
      nlinarith
    rw [← hc1, mul_zero]
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn'⟩ := exists_nat_gt (a / (b₁ * b₁ + b₂ * b₂))
    rw [div_lt_iff₀ hlt] at hn'
    have := hn n
    nlinarith
  · have := hpos (h v v • u + (-(h u v)) • v)
    rw [expand] at this
    simp only [map_neg, Complex.add_re, Complex.mul_re,
      Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, him, ← ha, ← hc, ← hb₁, ← hb₂] at this
    have h2 : 0 ≤ c * (a * c - (b₁ * b₁ + b₂ * b₂)) := by nlinarith
    have h3 := (mul_nonneg_iff_of_pos_left hc1).1 h2
    linarith

theorem places_formPerpVector_le [Fintype T] {p : ℕ} (h : M →ₗ[R] M →ₗ⋆[R] R)
    (hh : ∀ u v, h u v = star (h v u)) (τ : T → R →+* ℂ)
    (hτ : ∀ t x, τ t (star x) = starRingEnd ℂ (τ t x)) (hpos : ∀ t v, 0 ≤ (τ t (h v v)).re)
    (e e' : Fin p → M) (g : M) {r : ℝ}
    (he : ∀ a, √(∑ t, (τ t (h (e a) (e a))).re) ≤ r)
    (he' : ∀ a, √(∑ t, (τ t (h (e' a) (e' a))).re) ≤ r)
    (hg : √(∑ t, (τ t (h g g)).re) ≤ r) :
    (∀ t, ‖τ t (formPairMatrix h e e').det‖ ≤ p ! * r ^ (2 * p)) ∧
      √(∑ t, (τ t (h (formPerpVector h e e' g) (formPerpVector h e e' g))).re)
        ≤ (p + 1)! * r ^ (2 * p + 1) := by
  have hsum : ∀ v, 0 ≤ ∑ t, (τ t (h v v)).re := fun v => Finset.sum_nonneg fun t _ => hpos t v
  have hcs1 : ∀ t u v, ‖τ t (h u v)‖ ≤ √(τ t (h u u)).re * √(τ t (h v v)).re := by
    intro t u v
    rw [← Real.sqrt_mul (hpos t u)]
    exact Real.le_sqrt_of_sq_le (normSq_place_form_le h hh (τ t) (hτ t) (hpos t) u v)
  have hsm : ∀ t (x : R) v, (τ t (h (x • v) (x • v))).re = ‖τ t x‖ ^ 2 * (τ t (h v v)).re := by
    intro t x v
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, map_mul,
      starRingEnd_apply, hτ]
    rw [← mul_assoc, ← starRingEnd_apply, Complex.conj_mul', ← Complex.ofReal_pow,
      Complex.re_ofReal_mul]
  let π : R →+* (T → ℂ) := RingHom.pi τ
  let ν : RingSeminorm R :=
    { toFun := fun x => ‖π x‖
      map_zero' := by simp
      add_le' := fun x y => by rw [map_add]; exact norm_add_le _ _
      neg' := fun x => by rw [map_neg, norm_neg]
      mul_le' := fun x y => by rw [map_mul]; exact norm_mul_le _ _ }
  have hν : ∀ t x, ‖τ t x‖ ≤ ν x := fun t x => norm_le_pi_norm (π x) t
  have hν1 : ν 1 ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun t => by simp [π]
  let μ : AddGroupSeminorm M :=
    { toFun := fun v => √(∑ t, (τ t (h v v)).re)
      map_zero' := by simp
      add_le' := fun u v => by
        refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
        have h1 : ∑ t, √(τ t (h u u)).re * √(τ t (h v v)).re
            ≤ √(∑ t, (τ t (h u u)).re) * √(∑ t, (τ t (h v v)).re) :=
          Real.sum_sqrt_mul_sqrt_le _ (fun t => hpos t u) fun t => hpos t v
        have h2 : ∑ t, (τ t (h (u + v) (u + v))).re
            ≤ ∑ t, ((τ t (h u u)).re + 2 * (√(τ t (h u u)).re * √(τ t (h v v)).re)
              + (τ t (h v v)).re) := by
          refine Finset.sum_le_sum fun t _ => ?_
          have a1 := (Complex.re_le_norm _).trans (hcs1 t u v)
          have a2 := (Complex.re_le_norm _).trans (hcs1 t v u)
          simp only [map_add, LinearMap.add_apply, Complex.add_re]
          nlinarith
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at h2
        rw [add_sq, Real.sq_sqrt (hsum u), Real.sq_sqrt (hsum v)]
        linarith
      neg' := fun v => by simp }
  have hμ : ∀ t v, √(τ t (h v v)).re ≤ μ v := fun t v =>
    Real.sqrt_le_sqrt (Finset.single_le_sum (fun s _ => hpos s v) (Finset.mem_univ t))
  have hcs : ∀ u v, ν (h u v) ≤ μ u * μ v := fun u v =>
    (pi_norm_le_iff_of_nonneg (mul_nonneg (apply_nonneg μ u) (apply_nonneg μ v))).2 fun t =>
      (hcs1 t u v).trans
        (mul_le_mul (hμ t u) (hμ t v) (Real.sqrt_nonneg _) (apply_nonneg μ u))
  have hsmul : ∀ (x : R) (v : M), μ (x • v) ≤ ν x * μ v := by
    intro x v
    refine Real.sqrt_le_iff.2 ⟨mul_nonneg (apply_nonneg ν x) (apply_nonneg μ v), ?_⟩
    have : μ v ^ 2 = ∑ t, (τ t (h v v)).re := Real.sq_sqrt (hsum v)
    rw [mul_pow, this, Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [hsm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hν t x) 2) (hpos t v)
  exact ⟨fun t => (hν t _).trans (seminorm_det_formPairMatrix_le ν hν1 μ h hcs e e' he he'),
    seminorm_formPerpVector_le ν hν1 μ hsmul h hcs e e' g he he' hg⟩

end Places

theorem perpendicular_pairs {p q : ℕ} :
    (∀ {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
      (h : M →ₗ[R] M →ₗ⋆[R] R) (e e' : Fin p → M) (g : Fin q → M),
      (∀ b c, h (formPerpVector h e e' (g b)) (e c) = 0) ∧
      (∀ (A : Subring R) (L : Submodule A M), (∀ a, e' a ∈ L) → (∀ b, g b ∈ L) →
        (∀ a a', h (e' a') (e a) ∈ A) → (∀ b a, h (g b) (e a) ∈ A) →
        ∀ b, formPerpVector h e e' (g b) ∈ L) ∧
      (∀ b, (∀ a, h (g b) (e a) = 0) →
        formPerpVector h e e' (g b) = (formPairMatrix h e e').det • g b)) ∧
    (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (e e' : Fin p → V) (g : Fin q → V) (r : ℝ),
      (∀ a, ‖e a‖ ≤ r) → (∀ a, ‖e' a‖ ≤ r) → (∀ b, ‖g b‖ ≤ r) →
      ‖(formPairMatrix (innerFormLeft V) e e').det‖ ≤ p ! * r ^ (2 * p) ∧
      ∀ b, ‖formPerpVector (innerFormLeft V) e e' (g b)‖ ≤ (p + 1)! * r ^ (2 * p + 1)) :=
  ⟨fun h e e' g => ⟨fun b c => form_formPerpVector h e e' (g b) c,
      fun A L he' hg he hv b => formPerpVector_mem_subring A L h e he' (hg b) he (hv b),
      fun _ hb => formPerpVector_of_perp h e e' hb⟩,
    fun e e' g _ he he' hg => ⟨norm_det_formPairMatrix_le e e' he he',
      fun b => norm_formPerpVector_le e e' (g b) he he' (hg b)⟩⟩

end GlobalTheory
