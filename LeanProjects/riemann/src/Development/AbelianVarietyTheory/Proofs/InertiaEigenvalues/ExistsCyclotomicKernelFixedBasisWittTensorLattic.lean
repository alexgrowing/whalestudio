import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicActionOnRootTower

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.FixedBasis

section Average

variable {H R M : Type} [Group H] [CommRing R] [AddCommGroup M] [Module R M]

theorem shift_mem (τ : H → M →+ M) (hmul : ∀ g h x, τ (g * h) x = τ g (τ h x))
    (J : AddSubgroup M) (hJ : ∀ g, ∀ x ∈ J, τ g x ∈ J) (N : Subgroup H) [Fintype (H ⧸ N)] (x : M)
    (hx : ∀ ν ∈ N, τ ν x - x ∈ J) (h : H) :
    τ h (∑ q : H ⧸ N, τ q.out x) - ∑ q : H ⧸ N, τ q.out x ∈ J := by
  rw [map_sum, ← Equiv.sum_comp (MulAction.toPerm h) (fun q : H ⧸ N => τ q.out x),
    ← Finset.sum_sub_distrib]
  refine J.sum_mem fun q _ => ?_
  obtain ⟨ν, hν⟩ := QuotientGroup.mk_out_eq_mul N (h * q.out)
  have e : (MulAction.toPerm h q : H ⧸ N) = ((h * q.out : H) : H ⧸ N) :=
    (MulAction.Quotient.mk_smul_out N h q).symm
  rw [e, hν, ← hmul, hmul _ (ν : H), ← map_sub, ← neg_sub, map_neg]
  exact J.neg_mem (hJ _ _ (hx _ ν.2))

theorem exists_fixed (σ : H → R → R) (τ : H → M →+ M) (hmul : ∀ g h x, τ (g * h) x = τ g (τ h x))
    (hsm : ∀ g c x, τ g (c • x) = σ g c • τ g x)
    (J : ℕ → Submodule R M) (hJ : ∀ n g, ∀ x ∈ J n, τ g x ∈ J n)
    (hcomp : ∀ f : ℕ → M, (∀ n, f (n + 1) - f n ∈ J n) → ∃ L, ∀ n, f n - L ∈ J n)
    (hsep : ∀ x, (∀ n, x ∈ J n) → x = 0)
    (𝒩 : Set (Subgroup H)) (hnorm : ∀ N ∈ 𝒩, N.Normal)
    (hdir : ∀ N ∈ 𝒩, ∀ N' ∈ 𝒩, ∃ N'' ∈ 𝒩, N'' ≤ N ∧ N'' ≤ N')
    (htr : ∀ N ∈ 𝒩, ∃ (_ : Fintype (H ⧸ N)) (b : R), (∀ ν ∈ N, σ ν b = b) ∧
      ∑ q : H ⧸ N, σ q.out b = 1)
    (x₀ : M) (hx₀ : ∀ m, ∃ N ∈ 𝒩, ∀ ν ∈ N, τ ν x₀ - x₀ ∈ J m)
    (N₀ : Subgroup H) (hN₀ : N₀ ∈ 𝒩) [Fintype (H ⧸ N₀)] (h₀ : ∀ ν ∈ N₀, τ ν x₀ - x₀ ∈ J 0)
    (y : R) (hy : ∀ ν ∈ N₀, σ ν y = y) :
    ∃ x, (∀ h, τ h x = x) ∧ ∑ q : H ⧸ N₀, σ q.out y • τ q.out x₀ - x ∈ J 0 := by
  let Sm : M → Prop := fun x => ∀ m, ∃ N ∈ 𝒩, ∀ ν ∈ N, τ ν x - x ∈ J m
  have av : ∀ (m : ℕ) (x : M), Sm x → ∀ N ∈ 𝒩, ∀ [Fintype (H ⧸ N)], (∀ ν ∈ N, τ ν x - x ∈ J m) →
      ∀ c : R, (∀ ν ∈ N, σ ν c = c) → Sm (∑ q : H ⧸ N, τ q.out (c • x)) ∧
        ∀ h, τ h (∑ q : H ⧸ N, τ q.out (c • x)) - ∑ q : H ⧸ N, τ q.out (c • x) ∈ J m := by
    intro m x hx N hN _ hNx c hc
    refine ⟨fun k => ?_, shift_mem τ hmul (J m).toAddSubgroup (hJ m) N _ fun ν hν => ?_⟩
    · obtain ⟨N₁, hN₁, h₁⟩ := hx k
      obtain ⟨N₂, hN₂, hle, hle'⟩ := hdir N hN N₁ hN₁
      refine ⟨N₂, hN₂, fun ν hν => ?_⟩
      rw [map_sum, ← Finset.sum_sub_distrib]
      refine (J k).sum_mem fun q _ => ?_
      have hν' := (hnorm N₂ hN₂).conj_mem' ν hν q.out
      have e : ν * q.out = q.out * (q.out⁻¹ * ν * q.out) := by group
      rw [← hmul, e, hmul, ← map_sub, hsm, hc _ (hle hν'), ← smul_sub]
      exact hJ k _ _ ((J k).smul_mem _ (h₁ _ (hle' hν')))
    · rw [hsm, hc ν hν, ← smul_sub]
      exact (J m).smul_mem _ (hNx ν hν)
  let X : ℕ → Type := fun n => {x : M // Sm x ∧ ∀ h, τ h x - x ∈ J n}
  have step : ∀ n (a : X n), ∃ a' : X (n + 1), a'.1 - a.1 ∈ J n := by
    intro n a
    obtain ⟨N, hN, h₁⟩ := a.2.1 (n + 1)
    obtain ⟨_, b, hb, hb1⟩ := htr N hN
    refine ⟨⟨_, av (n + 1) a.1 a.2.1 N hN h₁ b hb⟩, ?_⟩
    have e : a.1 = ∑ q : H ⧸ N, σ q.out b • a.1 := by rw [← Finset.sum_smul, hb1, one_smul]
    change ∑ q : H ⧸ N, τ q.out (b • a.1) - a.1 ∈ J n
    conv => enter [2, 2]; rw [e]
    rw [← Finset.sum_sub_distrib]
    refine (J n).sum_mem fun q _ => ?_
    rw [hsm, ← smul_sub]
    exact (J n).smul_mem _ (a.2.2 _)
  choose nx hnx using step
  let f : ∀ n, X n := fun n => Nat.rec ⟨_, av 0 x₀ hx₀ N₀ hN₀ h₀ y hy⟩ nx n
  obtain ⟨L, hL⟩ := hcomp (fun n => (f n).1) fun n => hnx n (f n)
  refine ⟨L, fun h => sub_eq_zero.1 (hsep _ fun n => ?_), ?_⟩
  · have e : τ h L - L = (τ h (f n).1 - (f n).1) + ((f n).1 - L) - τ h ((f n).1 - L) := by
      rw [map_sub]; abel
    rw [e]
    exact (J n).sub_mem ((J n).add_mem ((f n).2.2 h) (hL n)) (hJ n _ _ (hL n))
  · have := hL 0
    simp only [← hsm]
    exact this

end Average

section Complete

variable {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]

def mult (M : Type) [AddCommGroup M] [Module R M] (p : R) (n : ℕ) : Submodule R M :=
  LinearMap.range (LinearMap.lsmul R M (p ^ (n + 1)))

theorem mem_mult {p : R} {n : ℕ} {x : M} : x ∈ mult M p n ↔ ∃ z, p ^ (n + 1) • z = x := Iff.rfl

theorem mem_mult_iff (b : Module.Basis ι R M) {p : R} {n : ℕ} {x : M} :
    x ∈ mult M p n ↔ ∀ i, p ^ (n + 1) ∣ b.repr x i := by
  constructor
  · rintro ⟨z, rfl⟩ i
    exact ⟨b.repr z i, by simp⟩
  · intro h
    choose r hr using h
    refine mem_mult.2 ⟨∑ i, r i • b i, ?_⟩
    conv_rhs => rw [← b.sum_repr x]
    simp only [Finset.smul_sum, hr, mul_smul]

theorem mult_sep (b : Module.Basis ι R M) (p : R) [h : IsAdicComplete (Ideal.span {p}) R] (x : M)
    (hx : ∀ n, x ∈ mult M p n) : x = 0 := by
  refine b.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine h.haus' _ fun n => ?_
  simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero,
    Ideal.mem_span_singleton]
  exact (pow_dvd_pow p n.le_succ).trans ((mem_mult_iff b).1 (hx n) i)

theorem mult_complete (b : Module.Basis ι R M) (p : R) [h : IsAdicComplete (Ideal.span {p}) R]
    (f : ℕ → M) (hf : ∀ n, f (n + 1) - f n ∈ mult M p n) : ∃ L, ∀ n, f n - L ∈ mult M p n := by
  have h1 : ∀ i, ∃ L, ∀ n, p ^ (n + 1) ∣ b.repr (f n) i - L := by
    intro i
    have h2 : ∀ n, p ^ (n + 1) ∣ b.repr (f n) i - b.repr (f (n + 1)) i := fun n => by
      have := (mem_mult_iff b).1 (hf n) i
      rw [map_sub, Finsupp.sub_apply] at this
      exact dvd_sub_comm.1 this
    obtain ⟨L, hL⟩ := h.prec' (fun n => b.repr (f n) i)
      ((AdicCompletion.isAdicCauchy_iff (Ideal.span {p}) R _).2 fun n => by
        simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem,
          Ideal.mem_span_singleton]
        exact (pow_dvd_pow p n.le_succ).trans (h2 n))
    refine ⟨L, fun n => ?_⟩
    have hn := hL (n + 1)
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem,
      Ideal.mem_span_singleton] at hn
    rw [← sub_add_sub_cancel _ (b.repr (f (n + 1)) i)]
    exact (h2 n).add hn
  choose L hL using h1
  refine ⟨b.equivFun.symm L, fun n => (mem_mult_iff b).2 fun i => ?_⟩
  rw [map_sub, Finsupp.sub_apply, ← b.equivFun_apply (b.equivFun.symm L), LinearEquiv.apply_symm_apply]
  exact hL i n

theorem exists_basis [Nontrivial R] (b : Module.Basis ι R M) (p : R) [IsAdicComplete (Ideal.span {p}) R]
    (u : M →ₗ[R] M) (hu : Function.Surjective u) (e : ι → M) (he : ∀ i, u (b i) - e i ∈ mult M p 0) :
    ∃ e' : Module.Basis ι R M, ∀ i, e' i = e i := by
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  have htop : ⊤ ≤ Submodule.span R (Set.range e) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsAdicComplete.le_jacobson_bot (Ideal.span {p})) ?_
    rw [← LinearMap.range_eq_top.2 hu, LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span,
      Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨z, hz⟩ := mem_mult.1 (he i)
    rw [← sub_add_cancel (u (b i)) (e i), add_comm, ← hz]
    refine Submodule.add_mem_sup (Submodule.subset_span ⟨i, rfl⟩) ?_
    refine Submodule.smul_mem_smul ?_ ?_
    · rw [zero_add, pow_one]; exact Ideal.mem_span_singleton_self p
    · rw [← Submodule.map_span, b.span_eq, ← LinearMap.range_eq_map, LinearMap.range_eq_top.2 hu]
      trivial
  exact ⟨basisOfTopLeSpanOfCardEqFinrank e htop (Module.finrank_eq_card_basis b).symm,
    fun i => by simp⟩

theorem surjective_of_matrix {W : Type} [CommRing W] [DecidableEq ι] (j : W →+* R) (m : ι → M)
    (hm : Submodule.span R (Set.range m) = ⊤) (u : M →ₗ[R] M) (U : Matrix ι ι W)
    (hU : IsUnit U.det) (hu : ∀ k, u (m k) = ∑ i, j (U i k) • m i) : Function.Surjective u := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hm, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  refine ⟨∑ a, j (U⁻¹ a k) • m a, ?_⟩
  simp only [map_sum, map_smul, hu, Finset.smul_sum, smul_smul, ← map_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, ← map_sum]
  have : ∀ i, ∑ a, U⁻¹ a k * U i a = (1 : Matrix ι ι W) i k := fun i => by
    rw [← Matrix.mul_nonsing_inv U hU, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  simp [this, Matrix.one_apply, apply_ite j]

end Complete

section Independent

theorem exists_det_ne_zero {A C Q ι : Type} [CommRing A] [Field C] [Fintype Q] [Fintype ι]
    [DecidableEq ι] (s : Q → A →+* C) (hs : Function.Injective s) (S : Set C) (hS : S.Infinite)
    (hSA : ∀ c ∈ S, ∃ a : A, ∀ q, s q a = c) (B : Q → Matrix ι ι C) (q₀ : Q) (hB : (B q₀).det ≠ 0) :
    ∃ y : A, (∑ q, s q y • B q).det ≠ 0 := by
  classical
  have hli : LinearIndependent C fun q => (s q : A → C) :=
    (linearIndependent_monoidHom A C).comp (fun q => (s q : A →* C)) fun q q' h =>
      hs (RingHom.ext fun a => DFunLike.congr_fun h a)
  have hsp := span_flip_eq_top_iff_linearIndependent.2 hli
  have hmem : (Pi.single q₀ 1 : Q → C) ∈ Submodule.span C
      (Set.range (flip fun q => (s q : A → C))) := by rw [hsp]; trivial
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  let F : MvPolynomial A C :=
    (∑ q, (∑ a ∈ c.support, MvPolynomial.X a * MvPolynomial.C (s q a) : MvPolynomial A C) •
      (B q).map MvPolynomial.C).det
  have hF : ∀ x : A → C, MvPolynomial.eval x F =
      (∑ q, (∑ a ∈ c.support, x a * s q a) • B q).det := fun x => by
    rw [RingHom.map_det]
    congr 1
    ext i k
    simp [Matrix.sum_apply]
  by_contra hcon
  push_neg at hcon
  have h0 : F = 0 := by
    refine MvPolynomial.funext_set (fun _ => S) (fun _ => hS) fun x hx => ?_
    choose a ha using fun i => hSA (x i) (hx i trivial)
    rw [hF, map_zero, ← hcon (∑ i ∈ c.support, a i * i)]
    simp [ha]
  have h1 := hF c
  have h2 : ∀ q, ∑ a ∈ c.support, c a * s q a = (Pi.single q₀ 1 : Q → C) q := fun q => by
    rw [← hc, Finsupp.sum, Finset.sum_apply]
    rfl
  simp only [h2, h0, map_zero] at h1
  rw [Finset.sum_eq_single q₀ (fun q _ hq => by simp [hq]) (by simp)] at h1
  exact hB (by simpa using h1.symm)

end Independent

section Generic

variable {H Z O W T ι κ : Type} [Group H] [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
  [Algebra Z W] [AddCommGroup T] [Module O T] [Module Z T] [IsScalarTower Z O T] [Fintype ι]
  [Fintype κ] [DecidableEq κ]

theorem generic (b : Module.Basis ι O T) (c : Module.Basis κ Z T) (ρ : H →* (T →ₗ[O] T))
    (a : H →* (W ≃ₐ[Z] W)) (p : ℕ) [Nontrivial (O ⊗[Z] W)]
    [IsAdicComplete (Ideal.span {(p : O ⊗[Z] W)}) (O ⊗[Z] W)]
    (𝒩 : Set (Subgroup H)) (hnorm : ∀ N ∈ 𝒩, N.Normal)
    (hdir : ∀ N ∈ 𝒩, ∀ N' ∈ 𝒩, ∃ N'' ∈ 𝒩, N'' ≤ N ∧ N'' ≤ N')
    (hfin : ∀ N ∈ 𝒩, Finite (H ⧸ N))
    (hsmall : ∀ m, ∃ N ∈ 𝒩, ∀ ν ∈ N, ∀ i, ρ ν (b i) - b i ∈ mult T (p : Z) m)
    (hbase : ∀ N ∈ 𝒩, ∀ [Fintype (H ⧸ N)] {μ : Type} [Fintype μ] [DecidableEq μ]
      (B : H ⧸ N → Matrix μ μ Z) (q₀ : H ⧸ N), IsUnit (B q₀).det →
      ∃ y : W, (∀ ν ∈ N, a ν y = y) ∧ IsUnit (∑ q, a q.out y • (B q).map (algebraMap Z W)).det) :
    ∃ e : Module.Basis ι (O ⊗[Z] W) ((O ⊗[Z] W) ⊗[O] T), ∀ g i,
      TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id O O) (a g).toAlgHom).toLinearMap
        (ρ g) (e i) = e i := by
  classical
  let σ : H → (O ⊗[Z] W →ₐ[O] O ⊗[Z] W) := fun g =>
    Algebra.TensorProduct.map (AlgHom.id O O) (a g).toAlgHom
  have hσ : ∀ g (w : W), σ g ((1 : O) ⊗ₜ[Z] w) = (1 : O) ⊗ₜ[Z] a g w := fun g w => by simp [σ]
  have hσmul : ∀ g h x, σ (g * h) x = σ g (σ h x) := fun g h x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o w => simp [σ]
    | add x y hx hy => simp [hx, hy]
  let τ : H → (O ⊗[Z] W) ⊗[O] T →+ (O ⊗[Z] W) ⊗[O] T := fun g =>
    (TensorProduct.map (σ g).toLinearMap (ρ g)).toAddMonoidHom
  have hτ : ∀ g r t, τ g (r ⊗ₜ[O] t) = σ g r ⊗ₜ[O] ρ g t := fun g r t => by simp [τ]
  have hmul : ∀ g h x, τ (g * h) x = τ g (τ h x) := fun g h x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r t => simp [hτ, hσmul]
    | add x y hx hy => simp [hx, hy]
  have hsm : ∀ g r x, τ g (r • x) = σ g r • τ g x := fun g r x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r' t => simp only [TensorProduct.smul_tmul', hτ, smul_eq_mul, map_mul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  let bM := Algebra.TensorProduct.basis (O ⊗[Z] W) b
  have hbM : ∀ i, bM i = 1 ⊗ₜ[O] b i := fun i => Algebra.TensorProduct.basis_apply b i
  let J := mult ((O ⊗[Z] W) ⊗[O] T) (p : O ⊗[Z] W)
  have hJ : ∀ n g, ∀ x ∈ J n, τ g x ∈ J n := by
    rintro n g _ ⟨z, rfl⟩
    exact ⟨τ g z, by simp only [LinearMap.lsmul_apply, hsm, map_pow, map_natCast]⟩
  have htr : ∀ N ∈ 𝒩, ∃ (_ : Fintype (H ⧸ N)) (b : O ⊗[Z] W), (∀ ν ∈ N, σ ν b = b) ∧
      ∑ q : H ⧸ N, σ q.out b = 1 := by
    intro N hN
    haveI := hfin N hN
    letI := Fintype.ofFinite (H ⧸ N)
    obtain ⟨y, hy, hu⟩ := hbase N hN (μ := Unit) (fun _ => 1) ((1 : H) : H ⧸ N) (by simp)
    rw [Matrix.det_unique, Matrix.sum_apply] at hu
    have hu' : IsUnit (∑ q : H ⧸ N, a q.out y) := by simpa using hu
    have ht : ∀ h, a h (∑ q : H ⧸ N, a q.out y) = ∑ q : H ⧸ N, a q.out y := fun h => by
      have := shift_mem (fun g => (a g).toAddEquiv.toAddMonoidHom) (fun g h x => by simp) ⊥
        (fun g x hx => by rw [AddSubgroup.mem_bot] at hx ⊢; simp [hx]) N y
        (fun ν hν => by simp [hy ν hν]) h
      exact sub_eq_zero.1 (AddSubgroup.mem_bot.1 this)
    obtain ⟨w, hw⟩ := hu'.exists_right_inv
    have hwf : ∀ h, a h w = w := fun h => by
      have h1 := congrArg (a h) hw
      rw [map_mul, map_one, ht h] at h1
      exact hu'.mul_left_cancel (h1.trans hw.symm)
    refine ⟨inferInstance, (1 : O) ⊗ₜ[Z] (y * w), fun ν hν => ?_, ?_⟩
    · rw [hσ, map_mul, hy ν hν, hwf]
    · simp only [hσ, map_mul, hwf]
      rw [← TensorProduct.tmul_sum, ← Finset.sum_mul, hw]
      rfl
  have hz : ∀ (z : Z) (t : T), (1 : O ⊗[Z] W) ⊗ₜ[O] (z • t) =
      ((1 : O) ⊗ₜ[Z] algebraMap Z W z) • ((1 : O ⊗[Z] W) ⊗ₜ[O] t) := fun z t => by
    rw [← algebraMap_smul O z t, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hsmall' : ∀ m, ∃ N ∈ 𝒩, ∀ i, ∀ ν ∈ N, τ ν (bM i) - bM i ∈ J m := fun m => by
    obtain ⟨N, hN, h⟩ := hsmall m
    refine ⟨N, hN, fun i ν hν => ?_⟩
    obtain ⟨z, hz'⟩ := mem_mult.1 (h ν hν i)
    refine mem_mult.2 ⟨1 ⊗ₜ[O] z, ?_⟩
    rw [hbM, hτ, map_one, ← TensorProduct.tmul_sub, ← hz', hz, map_pow, map_natCast]
    congr 1
    have := map_pow (Algebra.TensorProduct.includeRight : W →ₐ[Z] O ⊗[Z] W) (p : W) (m + 1)
    rw [map_natCast] at this
    exact this.symm
  obtain ⟨N₀, hN₀, h₀⟩ := hsmall' 0
  haveI := hfin N₀ hN₀
  letI := Fintype.ofFinite (H ⧸ N₀)
  obtain ⟨y, hy, hu⟩ := hbase N₀ hN₀
    (fun q => LinearMap.toMatrix c c ((ρ q.out).restrictScalars Z)) ((1 : H) : H ⧸ N₀) (by
      haveI := Module.Free.of_basis c
      haveI := Module.Finite.of_basis c
      rw [LinearMap.det_toMatrix, ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]
      exact (Module.End.isUnit_iff (ρ _)).1 ((Group.isUnit _).map ρ))
  have hex := fun i => exists_fixed (fun g => σ g) τ hmul hsm J hJ (mult_complete bM _)
    (mult_sep bM _) 𝒩 hnorm hdir htr (bM i)
    (fun m => (hsmall' m).imp fun N h => ⟨h.1, h.2 i⟩) N₀ hN₀ (h₀ i) ((1 : O) ⊗ₜ[Z] y)
    (fun ν hν => by rw [hσ, hy ν hν])
  choose e he he' using hex
  let u : (O ⊗[Z] W) ⊗[O] T →ₗ[O ⊗[Z] W] (O ⊗[Z] W) ⊗[O] T :=
    ∑ q : H ⧸ N₀, ((1 : O) ⊗ₜ[Z] a q.out y) • (ρ q.out).baseChange (O ⊗[Z] W)
  have hut : ∀ t, u (1 ⊗ₜ[O] t) =
      ∑ q : H ⧸ N₀, ((1 : O) ⊗ₜ[Z] a q.out y) • ((1 : O ⊗[Z] W) ⊗ₜ[O] ρ q.out t) := fun t => by
    simp only [u, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul]
  have hsurj : Function.Surjective u := by
    refine surjective_of_matrix
      (Algebra.TensorProduct.includeRight : W →ₐ[Z] O ⊗[Z] W).toRingHom
      (fun k => 1 ⊗ₜ[O] c k) ?_ u _ hu fun k => ?_
    · rw [eq_top_iff, ← bM.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [hbM, ← c.sum_repr (b i), TensorProduct.tmul_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [hz]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · rw [hut]
      simp only [Matrix.sum_apply, map_sum, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      conv_lhs => rw [← c.sum_repr (ρ q.out (c k)), TensorProduct.tmul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hz, smul_smul]
      simp [LinearMap.toMatrix_apply]
  obtain ⟨e', he''⟩ := exists_basis bM _ u hsurj e fun i => by
    have := he' i
    simp only [hbM, hσ, hτ, map_one] at this
    rw [hbM, hut]
    exact this
  exact ⟨e', fun g i => by rw [he'']; exact he i g⟩

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime]

theorem exists_normal {U : Set (GQ l)} (hU : U ∈ nhds (1 : GQ l)) :
    ∃ L : FinExt l, (GK L).Normal ∧ (GK L : Set (GQ l)) ⊆ U := by
  obtain ⟨E, h1, h2, h3⟩ := (krullTopology_mem_nhds_one_iff_of_normal ℚ_[l] (Om l) U).1 hU
  refine ⟨⟨E, h1⟩, ?_, h3⟩
  change E.fixingSubgroup.Normal
  rw [← IntermediateField.restrictNormalHom_ker]
  infer_instance

theorem GK_mem_nhds (L : FinExt l) : (GK L : Set (GQ l)) ∈ nhds (1 : GQ l) :=
  haveI := L.2
  L.1.fixingSubgroup_isOpen.mem_nhds (GK L).one_mem

theorem finiteIndex_GK (L : FinExt l) : (GK L).FiniteIndex := by
  haveI := L.2
  haveI := Subgroup.quotient_finite_of_isOpen (GK L) L.1.fixingSubgroup_isOpen
  exact Subgroup.finiteIndex_of_finite_quotient

variable {P : LocPrime l} (AI : LocAinf l P)

theorem act_teich (g : GQ l) (y : OCb l) :
    AI.actWCbHom g (WittVector.teichmuller l (algebraMap (OCb l) (Cb l) y)) =
      WittVector.teichmuller l (algebraMap (OCb l) (Cb l) (AI.actT g y)) := by
  change AI.actWCb g _ = _
  rw [LocAinf.actWCb, WittVector.map_teichmuller, ← autCb_alg]
  rfl

theorem act_eps (g : GQ l) (hg : P.χQ g = 1) : AI.actT g AI.ε = AI.ε := by
  have h2 := GlobalTheory.ExpImage.actT_εroot_eq_pow l P AI g 1 (by rw [hg]; simp) 0
  simpa [LocAinf.εroot] using h2

theorem pow_injective : Function.Injective fun n : ℕ => (AI.ε - 1) ^ n := by
  refine pow_injective_of_not_isUnit (fun h => ?_) (sub_ne_zero.2 AI.ε_ne_one)
  have h1 := h.map (PreTilt.coeff (O := OC l) (p := l) 0)
  rw [map_sub, AI.ε_coeff, AI.ζ_zero, map_one, map_one, sub_self] at h1
  exact not_isUnit_zero h1

theorem base (hF : FaithH AI) {H : Type} [Group H] (f : H →* GQ l) (hf : ∀ h, P.χQ (f h) = 1)
    (L : FinExt l) (hL : ∀ g ∈ GK L, P.χQ g = 1 → g ∈ f.range) (N : Subgroup H)
    (hN : ∀ h, h ∈ N ↔ f h ∈ GK L) [Fintype (H ⧸ N)] {μ : Type} [Fintype μ] [DecidableEq μ]
    (B : H ⧸ N → Matrix μ μ ℤ_[l]) (q₀ : H ⧸ N) (hB : IsUnit (B q₀).det) :
    ∃ y : WCb l, (∀ ν ∈ N, AI.actWCbHom (f ν) y = y) ∧
      IsUnit (∑ q, AI.actWCbHom (f q.out) y • (B q).map (algebraMap ℤ_[l] (WCb l))).det := by
  let A : Subring (OCb l) :=
    { carrier := {x | ∀ ν ∈ N, AI.actT (f ν) x = x}
      mul_mem' := fun hx hy ν hν => by rw [map_mul, hx ν hν, hy ν hν]
      one_mem' := fun ν _ => map_one _
      add_mem' := fun hx hy ν hν => by rw [map_add, hx ν hν, hy ν hν]
      zero_mem' := fun ν _ => map_zero _
      neg_mem' := fun hx ν hν => by rw [map_neg, hx ν hν] }
  let s : H ⧸ N → A →+* Cb l := fun q =>
    (algebraMap (OCb l) (Cb l)).comp ((AI.actT (f q.out)).toRingHom.comp A.subtype)
  have hs : ∀ q (x : A), s q x = algebraMap (OCb l) (Cb l) (AI.actT (f q.out) x) := fun _ _ => rfl
  have hinj := IsFractionRing.injective (OCb l) (Cb l)
  have hsi : Function.Injective s := fun q q' h => by
    rw [← q.out_eq', ← q'.out_eq', QuotientGroup.eq, hN]
    refine hF L _ (hf _) fun x hx => ?_
    have hxA : x ∈ A := fun ν hν => hx _ ((hN ν).1 hν) (hf ν)
    have h1 : AI.actT (f q.out) x = AI.actT (f q'.out) x :=
      hinj (DFunLike.congr_fun h ⟨x, hxA⟩)
    rw [map_mul, map_mul, RingAut.mul_apply]
    erw [← h1]
    rw [← RingAut.mul_apply, ← map_mul, ← map_mul]
    erw [inv_mul_cancel]
    rw [map_one, map_one]
    rfl
  have hfix : ∀ (n : ℕ) h, AI.actT (f h) ((AI.ε - 1) ^ n) = (AI.ε - 1) ^ n := fun n h => by
    rw [map_pow, map_sub, map_one, act_eps AI _ (hf h)]
  let z : ℤ_[l] →+* Cb l := WittVector.constantCoeff.comp (algebraMap ℤ_[l] (WCb l))
  obtain ⟨y, hy⟩ := exists_det_ne_zero s hsi
    (Set.range fun n : ℕ => algebraMap (OCb l) (Cb l) ((AI.ε - 1) ^ n))
    (Set.infinite_range_of_injective (hinj.comp (pow_injective AI)))
    (by
      rintro _ ⟨n, rfl⟩
      exact ⟨⟨(AI.ε - 1) ^ n, fun ν _ => hfix n ν⟩, fun q => by rw [hs, hfix]⟩)
    (fun q => (B q).map z) q₀ (by
      have := (hB.map z).ne_zero
      rwa [RingHom.map_det] at this)
  refine ⟨WittVector.teichmuller l (algebraMap (OCb l) (Cb l) y), fun ν hν => ?_, ?_⟩
  · rw [act_teich, y.2 ν hν]
  · apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [← WittVector.constantCoeff_apply, RingHom.map_det]
    refine fun h0 => hy (Eq.trans (congrArg Matrix.det ?_) h0)
    symm
    ext i k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, map_sum, map_mul, act_teich, hs]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rfl

section Lattice

variable {G L O : Type} [Group G] [TopologicalSpace G] [Field L] [Algebra ℚ_[l] L] [CommRing O]
  [Algebra O L] [TopologicalSpace L] [Algebra ℤ_[l] O] [FiniteDimensional ℚ_[l] L]
  [IsTopologicalRing L] [T2Space L] [ContinuousSMul ℚ_[l] L]

theorem small (hc : ∀ c : ℤ_[l], algebraMap O L (algebraMap ℤ_[l] O c) =
      algebraMap ℚ_[l] L (algebraMap ℤ_[l] ℚ_[l] c)) (T : LocLat G ℚ_[l] L O) {ι κ : Type}
    [Fintype ι] [Fintype κ] (x : ι → ↥T.L.T) (m : ℕ) :
    letI := Module.compHom ↥T.L.T (algebraMap ℤ_[l] O)
    ∀ _ : Module.Basis κ ℤ_[l] ↥T.L.T, ∀ᶠ g : G in nhds 1,
      ∀ i, T.actT g (x i) - x i ∈ mult ↥T.L.T (l : ℤ_[l]) m := by
  letI := Module.compHom ↥T.L.T (algebraMap ℤ_[l] O)
  intro c
  have hp : l.Prime := Fact.out
  simp only [mem_mult_iff c, Filter.eventually_all]
  intro i k
  have h1 := (GlobalTheory.Cyc.continuous_coord_lat hc T c (x i) k).tendsto 1
  have h2 : actT T.L 1 (x i) = x i := Subtype.ext (by
    change T.ρ 1 (x i : T.V) = x i
    rw [map_one]; rfl)
  rw [h2] at h1
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := by have := hp.pos; positivity
  filter_upwards [Metric.tendsto_nhds.1 h1 _ hpos] with g hg
  rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow, map_sub,
    Finsupp.sub_apply]
  rw [dist_eq_norm, ← map_sub] at hg
  exact hg.le

theorem lattice [Nontrivial O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (hc : ∀ c : ℤ_[l], algebraMap O L (algebraMap ℤ_[l] O c) =
      algebraMap ℚ_[l] L (algebraMap ℤ_[l] ℚ_[l] c)) (T : LocLat G ℚ_[l] L O)
    {W : Type} [CommRing W] [Nontrivial W] [Algebra ℤ_[l] W]
    (hW : IsAdicComplete (Ideal.span {((l : ℕ) : O ⊗[ℤ_[l]] W)}) (O ⊗[ℤ_[l]] W))
    (H : Subgroup G) (a : ↥H →* (W ≃ₐ[ℤ_[l]] W))
    (𝒩 : Set (Subgroup ↥H)) (hnorm : ∀ N ∈ 𝒩, N.Normal)
    (hdir : ∀ N ∈ 𝒩, ∀ N' ∈ 𝒩, ∃ N'' ∈ 𝒩, N'' ≤ N ∧ N'' ≤ N')
    (hfin : ∀ N ∈ 𝒩, Finite (↥H ⧸ N))
    (hopen : ∀ U ∈ nhds (1 : G), ∃ N ∈ 𝒩, ∀ ν ∈ N, (ν : G) ∈ U)
    (hbase : ∀ N ∈ 𝒩, ∀ [Fintype (↥H ⧸ N)] {μ : Type} [Fintype μ] [DecidableEq μ]
      (B : ↥H ⧸ N → Matrix μ μ ℤ_[l]) (q₀ : ↥H ⧸ N), IsUnit (B q₀).det →
      ∃ y : W, (∀ ν ∈ N, a ν y = y) ∧
        IsUnit (∑ q, a q.out y • (B q).map (algebraMap ℤ_[l] W)).det) :
    ∃ e : Module.Basis (Fin (Module.finrank O ↥T.L.T)) (O ⊗[ℤ_[l]] W) (TW (O ⊗[ℤ_[l]] W) T),
      ∀ (g : ↥H) i, TWact (Algebra.TensorProduct.map (AlgHom.id O O) (a g).toAlgHom) T (g : G)
        (e i) = e i := by
  letI := Module.compHom ↥T.L.T (algebraMap ℤ_[l] O)
  obtain ⟨d, ⟨c⟩⟩ := GlobalTheory.Cyc.exists_basis_lat (R := ℤ_[l]) T
  haveI : IsScalarTower ℤ_[l] O ↥T.L.T := ⟨fun c a x => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  haveI := T.L.free
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  haveI : Nontrivial (O ⊗[ℤ_[l]] W) :=
    Module.FaithfullyFlat.lTensor_nontrivial ℤ_[l] O W
  let ρ : ↥H →* (↥T.L.T →ₗ[O] ↥T.L.T) :=
    { toFun := fun h => T.actT (h : G)
      map_one' := LinearMap.ext fun x => Subtype.ext (by
        change T.ρ 1 (x : T.V) = x
        rw [map_one]; rfl)
      map_mul' := fun g h => LinearMap.ext fun x => Subtype.ext (by
        change T.ρ ((g : G) * h) (x : T.V) = T.ρ g (T.ρ h (x : T.V))
        rw [map_mul]; rfl) }
  refine generic (Module.finBasis O ↥T.L.T) c ρ a l 𝒩 hnorm hdir hfin (fun m => ?_) hbase
  exact hopen _ (small hc T (Module.finBasis O ↥T.L.T) m c)

end Lattice

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), FaithH AI →
    ∀ (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
    ∃ e : Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (RW LL) (TW (RW LL) T),
      FixBasis AI T e := by
  intro l _ P AI hF K LL T
  have := LL.2
  have hc : ∀ c : ℤ_[l], algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) c) =
      algebraMap ℚ_[l] ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] c) := fun c =>
    (IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL) ↥LL.1 c).symm.trans
      (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1 c)
  haveI := Module.Free.of_basis (GlobalTheory.Decompl.basisO LL)
  haveI := Module.Finite.of_basis (GlobalTheory.Decompl.basisO LL)
  let H : Subgroup ↥(GK K) := (P.χQ.comp (GK K).subtype).ker
  let f : ↥H →* GQ l := (GK K).subtype.comp H.subtype
  obtain ⟨e, he⟩ := lattice hc T (TensorWitt.main l LL).1 H (AI.actWCbHom.comp f)
    {N | ∃ L : FinExt l, (GK L).Normal ∧ GK L ≤ GK K ∧ N = (GK L).comap f}
    (by rintro _ ⟨L, hL, -, rfl⟩; infer_instance)
    (by
      rintro _ ⟨L, -, hL, rfl⟩ _ ⟨L', -, -, rfl⟩
      obtain ⟨E, h1, h2⟩ := exists_normal (Filter.inter_mem (GK_mem_nhds L) (GK_mem_nhds L'))
      exact ⟨_, ⟨E, h1, fun g hg => hL (h2 hg).1, rfl⟩, fun g hg => (h2 hg).1,
        fun g hg => (h2 hg).2⟩)
    (by
      rintro _ ⟨L, -, -, rfl⟩
      haveI := finiteIndex_GK L
      exact (inferInstance : Finite (↥H ⧸ ((GK L).subgroupOf (GK K)).subgroupOf H)))
    (fun V hV => by
      obtain ⟨U, hU, h⟩ := (mem_nhds_subtype _ _ _).1 hV
      obtain ⟨E, h1, h2⟩ := exists_normal (Filter.inter_mem hU (GK_mem_nhds K))
      exact ⟨_, ⟨E, h1, fun g hg => (h2 hg).2, rfl⟩, fun ν hν => h (h2 hν).1⟩)
    (by
      rintro _ ⟨L, -, hL, rfl⟩ _ μ _ _ B q₀ hB
      exact base AI hF f (fun h => h.2) L (fun g hg hχ => ⟨⟨⟨g, hL hg⟩, hχ⟩, rfl⟩) _
        (fun _ => Iff.rfl) B q₀ hB)
  exact ⟨e, fun g hg i => he ⟨g, hg⟩ i⟩

end Concrete

end GlobalTheory.HWL.FixedBasis
