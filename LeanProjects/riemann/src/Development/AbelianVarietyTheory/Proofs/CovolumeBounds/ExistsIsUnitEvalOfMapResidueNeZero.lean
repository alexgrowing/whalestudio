import Mathlib

open scoped BigOperators
open Module

namespace GlobalTheory

section PolynomialFunction

variable (K : Type*) [CommSemiring K] {M : Type*} [AddCommMonoid M] [Module K M]

def IsPolynomialFunction (P : M → K) : Prop :=
  P ∈ Algebra.adjoin K (Set.range fun φ : Module.Dual K M => (φ : M → K))

variable {K}

theorem IsPolynomialFunction.linear (φ : Module.Dual K M) : IsPolynomialFunction K φ :=
  Algebra.subset_adjoin ⟨φ, rfl⟩

theorem IsPolynomialFunction.const (c : K) : IsPolynomialFunction K (fun _ : M => c) :=
  Subalgebra.algebraMap_mem _ c

theorem IsPolynomialFunction.add {P Q : M → K} (hP : IsPolynomialFunction K P)
    (hQ : IsPolynomialFunction K Q) : IsPolynomialFunction K (fun x => P x + Q x) :=
  Subalgebra.add_mem _ hP hQ

theorem IsPolynomialFunction.mul {P Q : M → K} (hP : IsPolynomialFunction K P)
    (hQ : IsPolynomialFunction K Q) : IsPolynomialFunction K (fun x => P x * Q x) :=
  Subalgebra.mul_mem _ hP hQ

theorem IsPolynomialFunction.eval {σ : Type*} (L : σ → Module.Dual K M) (p : MvPolynomial σ K) :
    IsPolynomialFunction K (fun x => MvPolynomial.eval (fun i => L i x) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using IsPolynomialFunction.const c
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (IsPolynomialFunction.linear (L i))

theorem IsPolynomialFunction.comp {N : Type*} [AddCommMonoid N] [Module K N] {P : M → K}
    (hP : IsPolynomialFunction K P) (L : N →ₗ[K] M) : IsPolynomialFunction K (fun y => P (L y)) := by
  induction hP using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨φ, rfl⟩ := hf
    exact IsPolynomialFunction.linear (φ ∘ₗ L)
  | algebraMap c => exact IsPolynomialFunction.const c
  | add f g _ _ hf hg => exact hf.add hg
  | mul f g _ _ hf hg => exact hf.mul hg

theorem IsPolynomialFunction.continuous {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] {P : E → 𝕜}
    (hP : IsPolynomialFunction 𝕜 P) : Continuous P := by
  induction hP using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨φ, rfl⟩ := hf
    exact φ.continuous_of_finiteDimensional
  | algebraMap c => exact continuous_const
  | add f g _ _ hf hg => exact hf.add hg
  | mul f g _ _ hf hg => exact hf.mul hg

end PolynomialFunction

section Frames

variable {ι : Type*} {K : Type*} {V : ι → Type*}

section Semiring

variable [CommSemiring K] [∀ s, AddCommMonoid (V s)] [∀ s, Module K (V s)]
  {l m n : ι → Type*} [∀ s, Fintype (l s)] [∀ s, Fintype (m s)]

def frameMul (x : ∀ s, m s → V s) (b : ∀ s, Matrix (m s) (n s) K) : ∀ s, n s → V s :=
  fun s j => ∑ i, b s i j • x s i

theorem frameMul_frameMul (x : ∀ s, l s → V s) (b : ∀ s, Matrix (l s) (m s) K)
    (c : ∀ s, Matrix (m s) (n s) K) :
    frameMul (frameMul x b) c = frameMul x (fun s => b s * c s) := by
  funext s j
  simp only [frameMul, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem frameMul_diagonal [∀ s, DecidableEq (m s)] (x : ∀ s, m s → V s) (d : ∀ s, m s → K) :
    frameMul x (fun s => Matrix.diagonal (d s)) = fun s j => d s j • x s j := by
  funext s j
  simp [frameMul, Matrix.diagonal_apply, ite_smul]

abbrev EntryIndex (m n : ι → Type*) : Type _ := Σ s, m s × n s

def entries {α : Type*} (b : ∀ s, Matrix (m s) (n s) α) : EntryIndex m n → α :=
  fun k => b k.1 k.2.1 k.2.2

def ofEntries {α : Type*} (ξ : EntryIndex m n → α) : ∀ s, Matrix (m s) (n s) α :=
  fun s => Matrix.of fun i j => ξ ⟨s, i, j⟩

omit [∀ s, Fintype (m s)] in
@[simp] theorem entries_apply {α : Type*} (b : ∀ s, Matrix (m s) (n s) α) (s : ι) (i : m s)
    (j : n s) : entries b ⟨s, i, j⟩ = b s i j := rfl

omit [∀ s, Fintype (m s)] in
@[simp] theorem ofEntries_apply {α : Type*} (ξ : EntryIndex m n → α) (s : ι) (i : m s)
    (j : n s) : ofEntries ξ s i j = ξ ⟨s, i, j⟩ := rfl

omit [∀ s, Fintype (m s)] in
@[simp] theorem entries_ofEntries {α : Type*} (ξ : EntryIndex m n → α) :
    entries (ofEntries ξ) = ξ := rfl

omit [∀ s, Fintype (m s)] in
@[simp] theorem ofEntries_entries {α : Type*} (b : ∀ s, Matrix (m s) (n s) α) :
    ofEntries (entries b) = b := rfl

def frameMulLinear (n : ι → Type*) (w : ∀ s, m s → V s) :
    (EntryIndex m n → K) →ₗ[K] (∀ s, n s → V s) where
  toFun ξ := frameMul w (ofEntries ξ)
  map_add' ξ η := by
    funext s j
    simp [frameMul, add_smul, Finset.sum_add_distrib]
  map_smul' c ξ := by
    funext s j
    simp [frameMul, Finset.smul_sum, smul_smul]

end Semiring

variable [Fintype ι] {r : ι → ℕ} [Field K] [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)]
  {W : Type*} [AddCommGroup W] [Module K W]

variable (K) in

def HasTriangularWeight (a : ∀ s, Fin (r s) → ℕ) (P : (∀ s, Fin (r s) → V s) → W) : Prop :=
  ∀ (x : ∀ s, Fin (r s) → V s) (b : ∀ s, Matrix (Fin (r s)) (Fin (r s)) K),
    (∀ s, (b s).IsUpperTriangular) → (∀ s i, b s i i ≠ 0) →
      P (frameMul x b) = (∏ s, ∏ i, b s i i ^ a s i) • P x

theorem HasTriangularWeight.smul {a : ∀ s, Fin (r s) → ℕ} {P : (∀ s, Fin (r s) → V s) → W}
    (hP : HasTriangularWeight K a P) (x : ∀ s, Fin (r s) → V s) (d : ∀ s, Fin (r s) → K)
    (hd : ∀ s i, d s i ≠ 0) :
    P (fun s i => d s i • x s i) = (∏ s, ∏ i, d s i ^ a s i) • P x := by
  rw [← frameMul_diagonal, hP x _ (fun s => Matrix.blockTriangular_diagonal _)
    (fun s i => by simpa using hd s i)]
  simp

end Frames

section Hadamard

variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜] {V : ι → Type*}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

theorem HasTriangularWeight.of_continuous [∀ s, AddCommGroup (V s)] [∀ s, Module 𝕜 (V s)]
    {a : ∀ s, Fin (r s) → ℕ} {P : (∀ s, Fin (r s) → V s) → W} (hP : HasTriangularWeight 𝕜 a P)
    (x : ∀ s, Fin (r s) → V s)
    (hc : Continuous fun b : ∀ s, Matrix (Fin (r s)) (Fin (r s)) 𝕜 => P (frameMul x b))
    (b : ∀ s, Matrix (Fin (r s)) (Fin (r s)) 𝕜) (hb : ∀ s, (b s).IsUpperTriangular) :
    P (frameMul x b) = (∏ s, ∏ i, b s i i ^ a s i) • P x := by
  let c : 𝕜 → ∀ s, Matrix (Fin (r s)) (Fin (r s)) 𝕜 := fun t s => b s + Matrix.diagonal fun _ => t
  have hcc : Continuous c := by
    refine continuous_pi fun s => continuous_const.add ?_
    exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
  have hfin : (Set.range fun k : Σ s, Fin (r s) => -b k.1 k.2 k.2).Finite := Set.finite_range _
  have hd : Dense (Set.range fun k : Σ s, Fin (r s) => -b k.1 k.2 k.2)ᶜ := hfin.countable.dense_compl 𝕜
  have h1 : Continuous fun t => P (frameMul x (c t)) := hc.comp hcc
  have h2 : Continuous fun t => (∏ s, ∏ i, c t s i i ^ a s i) • P x := by
    refine Continuous.smul ?_ continuous_const
    refine continuous_finset_prod _ fun s _ => continuous_finset_prod _ fun i _ => ?_
    exact (((continuous_apply s).comp hcc).matrix_elem i i).pow _
  have h3 := Continuous.ext_on hd h1 h2 (fun t ht => by
    refine hP x (c t) (fun s => (hb s).add (Matrix.blockTriangular_diagonal _)) fun s i h => ht ?_
    refine ⟨⟨s, i⟩, ?_⟩
    simp only [c, Matrix.add_apply, Matrix.diagonal_apply_eq] at h
    exact neg_eq_of_add_eq_zero_right h)
  simpa [c] using congrFun h3 0

section Inner

variable [∀ s, NormedAddCommGroup (V s)] [∀ s, InnerProductSpace 𝕜 (V s)]
  [∀ s, FiniteDimensional 𝕜 (V s)]

theorem exists_orthonormal_frameMul_eq (hV : ∀ s, finrank 𝕜 (V s) = r s)
    (x : ∀ s, Fin (r s) → V s) :
    ∃ (y : ∀ s, Fin (r s) → V s) (b : ∀ s, Matrix (Fin (r s)) (Fin (r s)) 𝕜),
      (∀ s, Orthonormal 𝕜 (y s)) ∧ (∀ s, (b s).IsUpperTriangular) ∧
        (∀ s i, ‖b s i i‖ ≤ ‖x s i‖) ∧ frameMul y b = x := by
  have h : ∀ s, finrank 𝕜 (V s) = Fintype.card (Fin (r s)) := fun s => by simp [hV]
  let e := fun s => InnerProductSpace.gramSchmidtOrthonormalBasis (h s) (x s)
  refine ⟨fun s => e s, fun s => (e s).toBasis.toMatrix (x s), fun s => (e s).orthonormal,
    fun s => InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular (h s) (x s),
    fun s i => ?_, ?_⟩
  · change ‖(e s).toBasis.toMatrix (x s) i i‖ ≤ _
    rw [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [(e s).orthonormal.1 i, one_mul]
  · funext s j
    exact (e s).toBasis.sum_toMatrix_smul_self (x s) j

theorem HasTriangularWeight.norm_le_prod (hV : ∀ s, finrank 𝕜 (V s) = r s)
    {a : ∀ s, Fin (r s) → ℕ} {P : (∀ s, Fin (r s) → V s) → W} (hP : HasTriangularWeight 𝕜 a P)
    (hc : Continuous P) {C : ℝ} (hC : ∀ y, (∀ s, Orthonormal 𝕜 (y s)) → ‖P y‖ ≤ C)
    (x : ∀ s, Fin (r s) → V s) : ‖P x‖ ≤ C * ∏ s, ∏ i, ‖x s i‖ ^ a s i := by
  obtain ⟨y, b, hy, hb, hbx, rfl⟩ := exists_orthonormal_frameMul_eq hV x
  rw [hP.of_continuous y (hc.comp (by unfold frameMul; fun_prop)) b hb, norm_smul, mul_comm]
  refine mul_le_mul (hC y hy) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hC y hy))
  simp only [norm_prod, norm_pow]
  gcongr with s _ i _
  exact hbx s i

theorem HasTriangularWeight.norm_le_prod_pow (hV : ∀ s, finrank 𝕜 (V s) = r s)
    {a : ∀ s, Fin (r s) → ℕ} {P : (∀ s, Fin (r s) → V s) → W} (hP : HasTriangularWeight 𝕜 a P)
    (hc : Continuous P) {C : ℝ} (hC : ∀ y, (∀ s, Orthonormal 𝕜 (y s)) → ‖P y‖ ≤ C)
    {R : ι → ℝ} {x : ∀ s, Fin (r s) → V s} (hx : ∀ s i, ‖x s i‖ ≤ R s) :
    ‖P x‖ ≤ C * ∏ s, R s ^ ∑ i, a s i := by
  have hC0 : 0 ≤ C := by
    obtain ⟨y, -, hy, -⟩ := exists_orthonormal_frameMul_eq hV x
    exact (norm_nonneg _).trans (hC y hy)
  refine (hP.norm_le_prod hV hc hC x).trans ?_
  simp only [← Finset.prod_pow_eq_pow_sum]
  gcongr with s _ i _
  exact hx s i

end Inner

end Hadamard

section PolynomialWeight

variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {K : Type*} [Field K]

def HasTriangularWeightPoly (a : ∀ s, Fin (r s) → ℕ)
    (p : MvPolynomial (EntryIndex (fun s => Fin (r s)) (fun s => Fin (r s))) K) : Prop :=
  ∀ x b : ∀ s, Matrix (Fin (r s)) (Fin (r s)) K,
    (∀ s, (b s).IsUpperTriangular) → (∀ s i, b s i i ≠ 0) →
      MvPolynomial.eval (entries fun s => x s * b s) p =
        (∏ s, ∏ i, b s i i ^ a s i) * MvPolynomial.eval (entries x) p

theorem HasTriangularWeight.poly {V : ι → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)]
    {a : ∀ s, Fin (r s) → ℕ} {P : (∀ s, Fin (r s) → V s) → K} (hP : HasTriangularWeight K a P)
    (w : ∀ s, Fin (r s) → V s)
    {p : MvPolynomial (EntryIndex (fun s => Fin (r s)) (fun s => Fin (r s))) K}
    (hp : ∀ ξ : ∀ s, Matrix (Fin (r s)) (Fin (r s)) K,
      P (frameMul w ξ) = MvPolynomial.eval (entries ξ) p) : HasTriangularWeightPoly a p := by
  intro x b hb hb0
  rw [← hp, ← hp, ← frameMul_frameMul, hP _ b hb hb0, smul_eq_mul]

theorem HasTriangularWeightPoly.hasTriangularWeight {V : ι → Type*} [∀ s, AddCommGroup (V s)]
    [∀ s, Module K (V s)] {a : ∀ s, Fin (r s) → ℕ}
    {p : MvPolynomial (EntryIndex (fun s => Fin (r s)) (fun s => Fin (r s))) K}
    (hp : HasTriangularWeightPoly a p) (L : ∀ s, Fin (r s) → Module.Dual K (V s)) :
    HasTriangularWeight K a fun y : ∀ s, Fin (r s) → V s =>
      MvPolynomial.eval (entries fun s => Matrix.of fun i j => L s i (y s j)) p := by
  intro y b hb hb0
  have : (fun s => Matrix.of fun i j => L s i (frameMul y b s j)) =
      fun s => (Matrix.of fun i j => L s i (y s j)) * b s := by
    funext s
    ext i j
    simp [frameMul, Matrix.mul_apply, mul_comm]
  exact (congrArg (fun z => MvPolynomial.eval (entries z) p) this).trans (hp _ b hb hb0)

noncomputable def detProdPoly (R : Type*) [CommRing R] (n : ι → Type*) [∀ s, Fintype (n s)]
    [∀ s, DecidableEq (n s)] : MvPolynomial (EntryIndex n n) R :=
  ∏ s, (ofEntries MvPolynomial.X s).det

theorem eval₂Hom_detProdPoly {R S : Type*} [CommRing R] [CommRing S] {n : ι → Type*}
    [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)] (f : R →+* S) (ξ : EntryIndex n n → S) :
    MvPolynomial.eval₂Hom f ξ (detProdPoly R n) = ∏ s, (ofEntries ξ s).det := by
  rw [detProdPoly, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

theorem eval_detProdPoly {R : Type*} [CommRing R] {n : ι → Type*}
    [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)] (ξ : EntryIndex n n → R) :
    MvPolynomial.eval ξ (detProdPoly R n) = ∏ s, (ofEntries ξ s).det :=
  eval₂Hom_detProdPoly (RingHom.id R) ξ

end PolynomialWeight

section HadamardPolynomial

variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜]

theorem HasTriangularWeightPoly.norm_eval_le {a : ∀ s, Fin (r s) → ℕ}
    {p : MvPolynomial (EntryIndex (fun s => Fin (r s)) (fun s => Fin (r s))) 𝕜}
    (hp : HasTriangularWeightPoly a p) {C : ℝ}
    (hC : ∀ u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) 𝕜,
      (∀ s, u s ∈ Matrix.unitaryGroup (Fin (r s)) 𝕜) → ‖MvPolynomial.eval (entries u) p‖ ≤ C)
    {R : ι → ℝ} (hR : ∀ s, 0 ≤ R s) {x : ∀ s, Matrix (Fin (r s)) (Fin (r s)) 𝕜}
    (hx : ∀ s j, ∑ i, ‖x s i j‖ ^ 2 ≤ R s ^ 2) :
    ‖MvPolynomial.eval (entries x) p‖ ≤ C * ∏ s, R s ^ ∑ i, a s i := by
  let L : ∀ s, Fin (r s) → Module.Dual 𝕜 (EuclideanSpace 𝕜 (Fin (r s))) := fun s i =>
    EuclideanSpace.projₗ i
  have hw := hp.hasTriangularWeight L
  have hc : Continuous fun y : ∀ s, Fin (r s) → EuclideanSpace 𝕜 (Fin (r s)) =>
      MvPolynomial.eval (entries fun s => Matrix.of fun i j => L s i (y s j)) p := by
    refine (MvPolynomial.continuous_eval p).comp (continuous_pi fun k => ?_)
    change Continuous fun y : ∀ s, Fin (r s) → EuclideanSpace 𝕜 (Fin (r s)) => y k.1 k.2.2 k.2.1
    fun_prop
  refine hw.norm_le_prod_pow (fun s => by simp) hc (fun y hy => hC _ fun s => ?_)
    (x := fun s j => WithLp.toLp 2 fun i => x s i j) fun s j => ?_
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have := orthonormal_iff_ite.1 (hy s) i j
    rw [PiLp.inner_apply] at this
    simpa [L, Matrix.mul_apply, Matrix.one_apply, mul_comm] using this
  · refine (sq_le_sq₀ (norm_nonneg _) (hR s)).1 ?_
    rw [EuclideanSpace.norm_sq_eq]
    exact hx s j

end HadamardPolynomial

section Gauss

open MvPolynomial IsLocalRing

variable {K Γ O : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ}
  [CommRing O] [Algebra O K]

variable [IsLocalRing O] [Infinite (ResidueField O)]

variable {ι : Type*} [Fintype ι]

section Matrices

variable {n : ι → Type*} [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]

end Matrices

section Lattices

variable {V : ι → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ s, Module O (V s)]
  [∀ s, IsScalarTower O K (V s)] {Λ : ∀ s, Submodule O (V s)}

variable {r : ι → ℕ}

end Lattices

end Gauss

end GlobalTheory
