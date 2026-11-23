import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Formalism.PadicSubsetSums.StableGradedCounts.ExistsNeZeroAevalEqZero
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniNilp
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.PairClass

theorem exists_aeval_eq_of_separable {F A : Type} [Field F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (a : A) (hs : (LinearMap.mulLeft F a).charpoly.Separable) (y : A) :
    ∃ q : F[X], y = aeval a q := by
  obtain ⟨w, hw⟩ := Formalism.IrreducibleCountingLemmas.Z.base_change_cyclic_vector F A (LinearMap.mulLeft F a) hs
  have key : ∀ (p : F[X]) (z : A), aeval (LinearMap.mulLeft F a) p z = aeval a p * z := by
    intro p z
    have h1 : aeval (Algebra.lmul F A a) p = Algebra.lmul F A (aeval a p) :=
      aeval_algHom_apply (Algebra.lmul F A) a p
    have h2 : Algebra.lmul F A a = LinearMap.mulLeft F a := rfl
    rw [← h2, h1]
    rfl
  obtain ⟨p1, hp1⟩ := hw 1
  obtain ⟨p2, hp2⟩ := hw (w * w)
  obtain ⟨p3, hp3⟩ := hw y
  rw [key] at hp1 hp2 hp3
  have hw2 : w = aeval a p2 := by
    calc w = w * w * aeval a p1 := by rw [mul_assoc, mul_comm w (aeval a p1), hp1, mul_one]
      _ = aeval a p2 * (aeval a p1 * w) := by rw [← hp2]; ring
      _ = aeval a p2 := by rw [hp1, mul_one]
  exact ⟨p3 * p2, by rw [← hp3, map_mul, hw2]⟩

theorem aeval_mulLeft_apply {F A : Type} [Field F] [CommRing A] [Algebra F A] (a : A) (p : F[X]) (z : A) :
    aeval (LinearMap.mulLeft F a) p z = aeval a p * z := by
  have h1 : aeval (Algebra.lmul F A a) p = Algebra.lmul F A (aeval a p) :=
    aeval_algHom_apply (Algebra.lmul F A) a p
  have h2 : Algebra.lmul F A a = LinearMap.mulLeft F a := rfl
  rw [← h2, h1]
  rfl

theorem trace_nondeg (F A : Type) [Field F] [CharZero F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (a : A) (hs : (LinearMap.mulLeft F a).charpoly.Separable) (x : A)
    (hx : ∀ y, Algebra.trace F A (x * y) = 0) : x = 0 := by
  classical
  let b := Module.finBasis F A
  have hM : IsNilpotent (Algebra.leftMulMatrix b x) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [pow_succ', hx]
  obtain ⟨k, hk⟩ := hM
  have hxk : x ^ k = 0 := by
    rw [← map_pow] at hk
    exact Algebra.leftMulMatrix_injective b (by rw [hk, map_zero])
  obtain ⟨q, rfl⟩ := exists_aeval_eq_of_separable a hs x
  obtain ⟨e₀, -, he⟩ := Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq (LinearMap.mulLeft F a) hs _ dvd_rfl
  have h1 : (LinearMap.mulLeft F a).charpoly ∣ q ^ (k + 1) :=
    he _ (by rw [aeval_mulLeft_apply, map_pow, pow_succ, hxk, zero_mul, zero_mul])
  obtain ⟨r, hr⟩ := (Squarefree.dvd_pow_iff_dvd hs.squarefree (Nat.succ_ne_zero k)).1 h1
  have h3 : aeval (LinearMap.mulLeft F a) q = 0 := by
    rw [hr, map_mul, LinearMap.aeval_self_charpoly, zero_mul]
  have h4 := LinearMap.congr_fun h3 1
  rwa [aeval_mulLeft_apply, mul_one] at h4

theorem trace_σ (K : UQ) (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  classical
  have σsm : ∀ (r : K.E) (y : B.A), B.σ (r • y) = K.c r • B.σ y := by
    intro r y
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  let b := Module.finBasis K.E B.A
  have hσsum : ∀ y : B.A, B.σ y = ∑ i, K.c (b.repr y i) • B.σ (b i) := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    simp only [σsm]
  have hli : LinearIndependent K.E (fun i => B.σ (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro r hr i
    have h1 := congrArg B.σ hr
    rw [map_sum, map_zero] at h1
    simp only [σsm, B.σ_σ] at h1
    have h2 := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ h1 i
    have := congrArg K.c h2
    rwa [K.c_c, map_zero] at this
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range fun i => B.σ (b i)) := by
    intro y _
    rw [← B.σ_σ y, hσsum (B.σ y)]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = B.σ (b i) := fun i => Module.Basis.mk_apply hli hsp i
  have hrepr : ∀ (y : B.A) (i), b'.repr (B.σ y) i = K.c (b.repr y i) := by
    intro y i
    have : B.σ y = ∑ j, K.c (b.repr y j) • b' j := by
      rw [hσsum y]; simp only [hb']
    rw [this, b'.repr_sum_self]
  rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hb', ← map_mul, hrepr]

theorem exists_degreeLT_equiv (F V : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (f : V →ₗ[F] V) (P : F[X]) (hP : f.charpoly = P) (hs : P.Separable) :
    ∃ (e₀ : V) (ψ : degreeLT F P.natDegree ≃ₗ[F] V), ∀ p, ψ p = aeval f (p : F[X]) e₀ := by
  subst hP
  obtain ⟨e₀, -, he⟩ := Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq f hs f.charpoly dvd_rfl
  let ψ : degreeLT F f.charpoly.natDegree →ₗ[F] V :=
    ((LinearMap.applyₗ e₀) ∘ₗ (aeval f).toLinearMap) ∘ₗ (degreeLT F _).subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    have h1 : f.charpoly ∣ (q : F[X]) := he _ hq
    have h2 : (q : F[X]).degree < f.charpoly.degree := by
      rw [degree_eq_natDegree f.charpoly_monic.ne_zero]
      exact mem_degreeLT.1 q.2
    exact Subtype.ext (eq_zero_of_dvd_of_degree_lt h1 h2)
  have : FiniteDimensional F (degreeLT F f.charpoly.natDegree) :=
    (degreeLTEquiv F _).symm.finiteDimensional
  have hdim : Module.finrank F (degreeLT F f.charpoly.natDegree) = Module.finrank F V := by
    rw [(degreeLTEquiv F _).finrank_eq, Module.finrank_fin_fun, LinearMap.charpoly_natDegree]
  exact ⟨e₀, LinearMap.linearEquivOfInjective ψ hinj hdim, fun p => rfl⟩

theorem exists_intertwine (F V W : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] (f : V →ₗ[F] V) (g : W →ₗ[F] W)
    (hs : f.charpoly.Separable) (he : f.charpoly = g.charpoly) : ∃ e : V ≃ₗ[F] W, ∀ v, e (f v) = g (e v) := by
  set P := f.charpoly with hPdef
  have hP : P.Monic := f.charpoly_monic
  obtain ⟨e₁, ψ₁, hψ₁⟩ := exists_degreeLT_equiv F V f P rfl hs
  obtain ⟨e₂, ψ₂, hψ₂⟩ := exists_degreeLT_equiv F W g P he.symm hs
  refine ⟨ψ₁.symm.trans ψ₂, fun v => ?_⟩
  obtain ⟨p, rfl⟩ := ψ₁.surjective v
  have hm : (X * (p : F[X])) %ₘ P ∈ degreeLT F P.natDegree := by
    rw [mem_degreeLT, ← degree_eq_natDegree hP.ne_zero]
    exact degree_modByMonic_lt _ hP
  have h1 : f (ψ₁ p) = ψ₁ ⟨_, hm⟩ := by
    rw [hψ₁, hψ₁, aeval_modByMonic_eq_self_of_root (LinearMap.aeval_self_charpoly f), map_mul, aeval_X,
      Module.End.mul_apply]
  have h2 : ψ₂ ⟨_, hm⟩ = g (ψ₂ p) := by
    rw [hψ₂, hψ₂, aeval_modByMonic_eq_self_of_root (show aeval g P = 0 by rw [he]; exact LinearMap.aeval_self_charpoly g),
      map_mul, aeval_X, Module.End.mul_apply]
  rw [h1, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, h2, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

theorem exists_herm_model : ∀ (K : UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V] [Module.Finite K.E V] (h : V → V → K.E), (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) → (∀ x y, h y x = K.c (h x y)) → (∀ y, (∀ z, h y z = 0) → y = 0) → ∀ (B : InvAlg K) (g : V →ₗ[K.E] V), B.P.Separable → g.charpoly = B.P → ((B.g * B.σ B.g = 1 ∧ ∀ y z, h (g y) (g z) = h y z) ∨ (B.σ B.g = B.g ∧ ∀ y z, h (g y) z = h y (g z))) → ∃ (x : B.Aˣ) (e : B.A ≃ₗ[K.E] V), B.σ (x : B.A) = x ∧ (∀ y, e (B.g * y) = g (e y)) ∧ ∀ y z, h (e y) (e z) = B.herm x y z := by
  intro K V _ _ _ _ _ h hadd hsm hherm hnd B g hsep hchar hcase
  have hsep' : (LinearMap.mulLeft K.E B.g).charpoly.Separable := hsep
  obtain ⟨e, he⟩ := exists_intertwine K.E B.A V (LinearMap.mulLeft K.E B.g) g hsep hchar.symm
  have he' : ∀ y, e (B.g * y) = g (e y) := fun y => he y
  have hadd2 : ∀ x y z, h x (y + z) = h x y + h x z := by
    intro x y z
    rw [hherm (y + z) x, hadd, map_add, ← hherm y x, ← hherm z x]
  have hsm2 : ∀ (c : K.E) x z, h x (c • z) = K.c c * h x z := by
    intro c x z
    rw [hherm (c • z) x, hsm, map_mul, ← hherm z x]
  let S : B.A → Prop := fun a => ∀ y z, h (e (a * y)) (e z) = h (e y) (e (B.σ a * z))
  have Salg : ∀ c : K.E, S (algebraMap K.E B.A c) := by
    intro c y z
    rw [B.σ_alg, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul, hsm, hsm2, K.c_c]
  have Sg : S B.g := by
    intro y z
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hz : z = B.g * (B.σ B.g * z) := by rw [← mul_assoc, h1, one_mul]
      conv_lhs => rw [hz]
      rw [he', he', h2]
    · rw [h1, he', he', h2]
  have Sadd : ∀ a b, S a → S b → S (a + b) := by
    intro a b ha hb y z
    rw [add_mul, map_add, hadd, ha, hb, map_add, add_mul, map_add, hadd2]
  have Smul : ∀ a b, S a → S b → S (a * b) := by
    intro a b ha hb y z
    rw [mul_assoc, ha, hb, show B.σ b * (B.σ a * z) = B.σ (a * b) * z by rw [map_mul B.σ]; ring]
  have Spoly : ∀ q : K.E[X], S (aeval B.g q) := by
    intro q
    induction q using Polynomial.induction_on with
    | C c => rw [aeval_C]; exact Salg c
    | add p q hp hq => rw [map_add]; exact Sadd _ _ hp hq
    | monomial n c ih =>
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]; exact Smul _ _ ih Sg
  have Sall : ∀ a, S a := by
    intro a
    obtain ⟨q, rfl⟩ := exists_aeval_eq_of_separable B.g hsep' a
    exact Spoly q

  let φ : Module.Dual K.E B.A :=
    { toFun := fun y => h (e y) (e 1)
      map_add' := fun y z => by rw [map_add, hadd]
      map_smul' := fun c y => by rw [map_smul, hsm]; rfl }
  have hinj : Function.Injective (Algebra.traceForm K.E B.A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact trace_nondeg K.E B.A B.g hsep' x fun y => by
      have := LinearMap.congr_fun hx y
      rwa [Algebra.traceForm_apply] at this
  have hsurj : Function.Surjective (Algebra.traceForm K.E B.A) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨x, hx⟩ := hsurj φ
  have hxy : ∀ y, Algebra.trace K.E B.A (x * y) = h (e y) (e 1) := fun y => by
    rw [← Algebra.traceForm_apply, hx]; rfl
  have hrep : ∀ y z, h (e y) (e z) = Algebra.trace K.E B.A (x * y * B.σ z) := by
    intro y z
    have := Sall (B.σ z) y 1
    rw [B.σ_σ, mul_one] at this
    rw [← this, ← hxy]
    congr 1
    ring
  have hfix : B.σ x = x := by
    have h0 := trace_nondeg K.E B.A B.g hsep' (B.σ x - x) fun y => by
      have h1 : Algebra.trace K.E B.A (B.σ x * y) = K.c (Algebra.trace K.E B.A (x * B.σ y)) := by
        rw [← trace_σ, map_mul B.σ x (B.σ y), B.σ_σ]
      have h2 : Algebra.trace K.E B.A (x * B.σ y) = h (e 1) (e y) := by
        rw [hrep]; ring_nf
      rw [sub_mul, map_sub, h1, h2, hherm (e y) (e 1), K.c_c, hxy, sub_self]
    exact sub_eq_zero.1 h0
  have hunit : IsUnit x := by
    have hi : Function.Injective (LinearMap.mulLeft K.E x) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      have hy' : x * y = 0 := hy
      apply e.injective
      rw [map_zero]
      apply hnd
      intro v
      rw [← e.apply_symm_apply v, hrep, hy', zero_mul, map_zero]
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hi) 1
    exact IsUnit.of_mul_eq_one y hy
  exact ⟨hunit.unit, e, hfix, he', fun y z => hrep y z⟩

end GlobalTheory.UnitLemma.PairClass
