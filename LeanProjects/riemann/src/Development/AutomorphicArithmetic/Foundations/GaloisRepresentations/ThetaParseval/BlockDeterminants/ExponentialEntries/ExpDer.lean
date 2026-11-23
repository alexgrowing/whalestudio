import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

open GlobalTheory.RealLift

noncomputable section

namespace UpperTheory.TP.RP.Der

variable {R : Type} [CommRing R] [Algebra ℂ R]

theorem hasSum_cauchy {a b : ℕ → ℂ} {A B : ℂ} (ha : HasSum a A) (hb : HasSum b B) :
    HasSum (fun k => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, a p.1 * b p.2) (A * B) := by
  have na := ha.summable.norm
  have nb := hb.summable.norm
  have e := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm na nb
  rw [ha.tsum_eq, hb.tsum_eq] at e
  rw [e]
  exact (summable_norm_sum_mul_antidiagonal_of_summable_norm na nb).of_norm.hasSum

theorem fact_choose {i j : ℕ} :
    (((i + j).factorial : ℂ))⁻¹ * ((i + j).choose i : ℂ) = ((i.factorial : ℂ))⁻¹ * ((j.factorial : ℂ))⁻¹ := by
  have h := Nat.add_choose_mul_factorial_mul_factorial i j
  rw [← Nat.choose_symm_add] at h
  have h' : ((i + j).choose i : ℂ) * i.factorial * j.factorial = (i + j).factorial := by exact_mod_cast h
  have a : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have b : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have f : ((i + j).factorial : ℂ) ≠ 0 := by exact_mod_cast (i + j).factorial_ne_zero
  rw [inv_mul_eq_div, div_eq_iff f, ← h']
  field_simp

theorem der_pow_mul (D : Derivation ℂ R R) (k : ℕ) (P Q : R) :
    (D.toLinearMap ^ k) (P * Q) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      (k.choose p.1 : R) * ((D.toLinearMap ^ p.1) P * (D.toLinearMap ^ p.2) Q) := by
  have st : ∀ (i : ℕ) (x : R), D ((D.toLinearMap ^ i) x) = (D.toLinearMap ^ (i + 1)) x := fun i x => by
    rw [pow_succ', Module.End.mul_apply]; rfl
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih,
      Finset.sum_antidiagonal_choose_succ_mul (fun i j => (D.toLinearMap ^ i) P * (D.toLinearMap ^ j) Q) k,
      map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hc : k.choose p.2 = k.choose p.1 :=
      (Nat.choose_symm_of_eq_add (Finset.HasAntidiagonal.mem_antidiagonal.1 hp).symm).symm
    rw [hc, ← nsmul_eq_mul, map_nsmul, ← mul_add, ← nsmul_eq_mul]
    congr 1
    change D _ = _
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, st, st, mul_comm ((D.toLinearMap ^ p.2) Q)]

def Good (D : Derivation ℂ R R) (P u : R) : Prop :=
  (∃ N : Submodule ℂ R, FiniteDimensional ℂ N ∧ P ∈ N ∧ ∀ y ∈ N, D y ∈ N) ∧
    ∀ l : R →ₗ[ℂ] ℂ, HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((D.toLinearMap ^ n) P)) (l u)

theorem pow_mem {D : Derivation ℂ R R} {P : R} {N : Submodule ℂ R} (hP : P ∈ N) (hN : ∀ y ∈ N, D y ∈ N) (n : ℕ) :
    (D.toLinearMap ^ n) P ∈ N := by
  induction n with
  | zero => simpa using hP
  | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hN _ ih

theorem mem_of_sum {D : Derivation ℂ R R} {P u : R}
    (h : ∀ l : R →ₗ[ℂ] ℂ, HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((D.toLinearMap ^ n) P)) (l u))
    {N : Submodule ℂ R} (hP : P ∈ N) (hN : ∀ y ∈ N, D y ∈ N) : u ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l'
  have a := h (l' ∘ₗ N.mkQ)
  have e : (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * (l' ∘ₗ N.mkQ) ((D.toLinearMap ^ n) P)) = fun _ => 0 := by
    funext n
    simp [(Submodule.Quotient.mk_eq_zero N).2 (pow_mem hP hN n)]
  rw [e] at a
  exact a.unique hasSum_zero

theorem Good.add {D : Derivation ℂ R R} {P Q u v : R} (hP : Good D P u) (hQ : Good D Q v) : Good D (P + Q) (u + v) := by
  obtain ⟨⟨N₁, f₁, m₁, s₁⟩, h₁⟩ := hP
  obtain ⟨⟨N₂, f₂, m₂, s₂⟩, h₂⟩ := hQ
  refine ⟨⟨N₁ ⊔ N₂, inferInstance, add_mem (Submodule.mem_sup_left m₁) (Submodule.mem_sup_right m₂), ?_⟩, fun l => ?_⟩
  · intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left (s₁ a ha)) (Submodule.mem_sup_right (s₂ b hb))
  · simpa [mul_add] using (h₁ l).add (h₂ l)

theorem Good.const (D : Derivation ℂ R R) (a : ℂ) : Good D (algebraMap ℂ R a) (algebraMap ℂ R a) := by
  have hz : ∀ n : ℕ, n ≠ 0 → (D.toLinearMap ^ n) (algebraMap ℂ R a) = 0 := fun n hn => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [pow_succ, Module.End.mul_apply]
    have : D.toLinearMap (algebraMap ℂ R a) = 0 := D.map_algebraMap a
    rw [this, map_zero]
  refine ⟨⟨Submodule.span ℂ {algebraMap ℂ R a}, inferInstance, Submodule.mem_span_singleton_self _, ?_⟩, fun l => ?_⟩
  · intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    simp
  · convert hasSum_single (f := fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((D.toLinearMap ^ n) (algebraMap ℂ R a))) 0
      (fun n hn => by simp [hz n hn]) using 1
    simp

theorem Good.mul {D : Derivation ℂ R R} {P Q u v : R} (hP : Good D P u) (hQ : Good D Q v) : Good D (P * Q) (u * v) := by
  obtain ⟨⟨N₁, f₁, m₁, s₁⟩, h₁⟩ := hP
  obtain ⟨⟨N₂, f₂, m₂, s₂⟩, h₂⟩ := hQ
  refine ⟨⟨N₁ * N₂, ?_, Submodule.mul_mem_mul m₁ m₂, ?_⟩, fun l => ?_⟩
  · exact Module.Finite.iff_fg.2 (Submodule.FG.mul (Module.Finite.iff_fg.1 f₁) (Module.Finite.iff_fg.1 f₂))
  · intro y hy
    induction hy using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b]
      exact add_mem (Submodule.mul_mem_mul ha (s₂ b hb)) (Submodule.mul_mem_mul (s₁ a ha) hb)
    | add x _ y _ hx hy => rw [map_add]; exact add_mem hx hy
  · have hv : v ∈ N₂ := mem_of_sum h₂ m₂ s₂
    obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective N₂.subtype (Submodule.ker_subtype N₂)
    let b := Module.finBasis ℂ N₂
    have dec : ∀ y (hy : y ∈ N₂), y = ∑ i, (b.coord i (π y)) • (b i : R) := fun y hy => by
      have e : π y = ⟨y, hy⟩ := LinearMap.congr_fun hπ ⟨y, hy⟩
      rw [e]
      calc y = ((⟨y, hy⟩ : N₂) : R) := rfl
        _ = ((∑ i, b.repr ⟨y, hy⟩ i • b i : N₂) : R) := by rw [b.sum_repr]
        _ = _ := by
          rw [Submodule.coe_sum]
          exact Finset.sum_congr rfl fun i _ => by simp [Module.Basis.coord_apply]
    have key : ∀ (a y : R), y ∈ N₂ → l (a * y) = ∑ i, l (a * b i) * b.coord i (π y) := fun a y hy => by
      conv_lhs => rw [dec y hy]
      rw [Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
    have S := fun i => hasSum_cauchy (h₁ (l ∘ₗ LinearMap.mulRight ℂ (b i : R))) (h₂ (b.coord i ∘ₗ π))
    have T := hasSum_sum (s := Finset.univ) (fun i _ => S i)
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply] at T
    rw [key u v hv]
    convert T using 2 with k
    rw [der_pow_mul, map_sum, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain rfl : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, key _ _ (pow_mem m₂ s₂ _), ← mul_assoc, fact_choose, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem isExp_of_gens {σ : Type} (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (h : ∀ i, Good D (MvPolynomial.X i) (φ (MvPolynomial.X i))) :
    IsExp D.toLinearMap φ.toLinearMap := by
  have g : ∀ P, Good D P (φ P) := fun P => by
    induction P using MvPolynomial.induction_on with
    | C a =>
      have := Good.const D a
      rwa [show algebraMap ℂ (MvPolynomial σ ℂ) a = MvPolynomial.C a from rfl, ← MvPolynomial.algebraMap_eq,
        AlgHom.commutes] at *
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p i hp => rw [map_mul]; exact hp.mul (h i)
  exact fun v l => (g v).2 l

theorem isExp_shift {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (h : IsExp L U) (s : ℂ) :
    IsExp (L + s • 1) (Complex.exp s • U) := by
  intro v l
  have hc : Commute L (s • (1 : Module.End ℂ V)) := (Commute.one_right L).smul_right s
  have b : HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * s ^ n) (Complex.exp s) := by
    have := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) s
    rw [← Complex.exp_eq_exp_ℂ] at this
    simpa [smul_eq_mul] using this
  have T := hasSum_cauchy (h v l) b
  have e : l ((Complex.exp s • U) v) = l (U v) * Complex.exp s := by
    simp [mul_comm]
  rw [e]
  convert T using 2 with k
  rw [hc.add_pow', LinearMap.sum_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain rfl : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have : (s • (1 : Module.End ℂ V)) ^ p.2 = s ^ p.2 • 1 := by rw [smul_pow, one_pow]
  rw [this, LinearMap.smul_apply, Module.End.mul_apply]
  simp only [mul_smul_comm, mul_one, LinearMap.smul_apply, Module.End.one_apply, map_nsmul, map_smul, smul_eq_mul, nsmul_eq_mul]
  rw [← mul_assoc, fact_choose]
  ring

section Mat

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasSum_exp_entry {τ : Type} [Fintype τ] [DecidableEq τ] (Y : Matrix τ τ ℂ) (a c : τ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * (Y ^ n) a c) (NormedSpace.exp Y a c) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h1 := h.map (Matrix.entryAddMonoidHom ℂ a c) (continuous_id.matrix_elem a c)
  simp only [Function.comp_def, Matrix.entryAddMonoidHom_apply, Matrix.smul_apply, smul_eq_mul] at h1
  exact h1

end Mat

theorem good_lin (D : Derivation ℂ R R) {τ : Type} [Fintype τ] [DecidableEq τ] (Y : Matrix τ τ ℂ) (v : τ → R)
    (hD : ∀ c, D (v c) = ∑ a, Y a c • v a) (c : τ) : Good D (v c) (∑ a, NormedSpace.exp Y a c • v a) := by
  have hp : ∀ (k : ℕ) c, (D.toLinearMap ^ k) (v c) = ∑ a, (Y ^ k) a c • v a := fun k => by
    induction k with
    | zero => intro c; simp [Matrix.one_apply, ite_smul]
    | succ k ih =>
      intro c
      rw [pow_succ, Module.End.mul_apply, show D.toLinearMap (v c) = _ from hD c, map_sum]
      simp only [map_smul, ih, pow_succ, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by rw [mul_comm]
  refine ⟨⟨Submodule.span ℂ (Set.range v), FiniteDimensional.span_of_finite ℂ (Set.finite_range v),
    Submodule.subset_span ⟨c, rfl⟩, ?_⟩, fun l => ?_⟩
  · have : Submodule.span ℂ (Set.range v) ≤ (Submodule.span ℂ (Set.range v)).comap D.toLinearMap := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨e, rfl⟩
      change D (v e) ∈ Submodule.span ℂ (Set.range v)
      rw [hD]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    exact fun y hy => this hy
  · have T := hasSum_sum (s := Finset.univ) fun a _ => (hasSum_exp_entry Y a c).mul_right (l (v a))
    have e1 : (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((D.toLinearMap ^ n) (v c))) =
        fun n : ℕ => ∑ a, ((n.factorial : ℂ))⁻¹ * (Y ^ n) a c * l (v a) := by
      funext n
      rw [hp, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, smul_eq_mul, mul_assoc]
    have e2 : l (∑ a, NormedSpace.exp Y a c • v a) = ∑ a, NormedSpace.exp Y a c * l (v a) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul]
    rw [e1, e2]
    exact T

theorem der_sum_apply {ι : Type} (s : Finset ι) (f : ι → Derivation ℂ R R) (x : R) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

end UpperTheory.TP.RP.Der
