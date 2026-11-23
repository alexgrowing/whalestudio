import Formalism.PeriodIntegrals.OrbJetBase

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.OJ

section General

variable {σ K : Type*} [CommSemiring K]

def SerIn (S : Set σ) (T : MvPowerSeries σ K) : Prop :=
  ∀ ν, MvPowerSeries.coeff ν T ≠ 0 → ∀ v, ν v ≠ 0 → v ∈ S

theorem SerIn.mono {S S' : Set σ} (h : S ⊆ S') {T : MvPowerSeries σ K} (hT : SerIn S T) :
    SerIn S' T := fun ν hν v hv => h (hT ν hν v hv)

theorem SerIn.one (S : Set σ) : SerIn S (1 : MvPowerSeries σ K) := by
  intro ν hν v hv
  rw [MvPowerSeries.coeff_one] at hν
  split_ifs at hν with h
  · subst h; simp at hv
  · exact absurd rfl hν

theorem SerIn.mul {S : Set σ} {T1 T2 : MvPowerSeries σ K} (h1 : SerIn S T1) (h2 : SerIn S T2) :
    SerIn S (T1 * T2) := by
  intro ν hν v hv
  rw [MvPowerSeries.coeff_mul] at hν
  obtain ⟨⟨x, y⟩, hxy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hν
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hxy
  have hx : MvPowerSeries.coeff x T1 ≠ 0 := left_ne_zero_of_mul hne
  have hy : MvPowerSeries.coeff y T2 ≠ 0 := right_ne_zero_of_mul hne
  have e := congrArg (fun f => f v) hxy
  simp only [Finsupp.add_apply] at e
  by_cases h : x v = 0
  · exact h2 y hy v (by omega)
  · exact h1 x hx v h

theorem SerIn.prod {ι : Type*} (s : Finset ι) {S : Set σ} {T : ι → MvPowerSeries σ K}
    (h : ∀ i ∈ s, SerIn S (T i)) : SerIn S (∏ i ∈ s, T i) := by
  induction s using Finset.induction_on with
  | empty => simpa using SerIn.one S
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem coeff_mul_of_disjoint {S1 S2 : Set σ} (hS : Disjoint S1 S2) {T1 T2 : MvPowerSeries σ K}
    (h1 : SerIn S1 T1) (h2 : SerIn S2 T2) {a b : σ →₀ ℕ} (ha : ∀ v, a v ≠ 0 → v ∈ S1)
    (hb : ∀ v, b v ≠ 0 → v ∈ S2) :
    MvPowerSeries.coeff (a + b) (T1 * T2) = MvPowerSeries.coeff a T1 * MvPowerSeries.coeff b T2 := by
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (a, b)]
  · rintro ⟨x, y⟩ hxy hne
    by_contra hnz
    have hx : MvPowerSeries.coeff x T1 ≠ 0 := left_ne_zero_of_mul hnz
    have hy : MvPowerSeries.coeff y T2 ≠ 0 := right_ne_zero_of_mul hnz
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hxy
    apply hne
    have key : ∀ v, x v = a v ∧ y v = b v := by
      intro v
      have e := congrArg (fun f => f v) hxy
      simp only [Finsupp.add_apply] at e
      by_cases hv : v ∈ S1
      · have hv2 : v ∉ S2 := fun h => Set.disjoint_left.1 hS hv h
        have : y v = 0 := by by_contra h; exact hv2 (h2 y hy v h)
        have : b v = 0 := by by_contra h; exact hv2 (hb v h)
        omega
      · have : x v = 0 := by by_contra h; exact hv (h1 x hx v h)
        have : a v = 0 := by by_contra h; exact hv (ha v h)
        omega
    exact Prod.ext (Finsupp.ext fun v => (key v).1) (Finsupp.ext fun v => (key v).2)
  · intro h; exact absurd (by simp) h

end General

section Ultra

variable {σ K : Type*} [NormedCommRing K] [IsUltrametricDist K]

theorem norm_coeff_mul_le {A B : MvPolynomial σ K} {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hA : ∀ m, ‖MvPolynomial.coeff m A‖ ≤ a) (hB : ∀ m, ‖MvPolynomial.coeff m B‖ ≤ b) (m : σ →₀ ℕ) :
    ‖MvPolynomial.coeff m (A * B)‖ ≤ a * b := by
  rw [MvPolynomial.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha0 hb0) fun x _ => ?_
  exact (norm_mul_le _ _).trans (mul_le_mul (hA _) (hB _) (norm_nonneg _) ha0)

theorem norm_coeff_prod_le [NormOneClass K] {ι : Type*} (s : Finset ι) {A : ι → MvPolynomial σ K}
    {a : ι → ℝ} (ha0 : ∀ i ∈ s, 0 ≤ a i) (hA : ∀ i ∈ s, ∀ m, ‖MvPolynomial.coeff m (A i)‖ ≤ a i)
    (m : σ →₀ ℕ) : ‖MvPolynomial.coeff m (∏ i ∈ s, A i)‖ ≤ ∏ i ∈ s, a i := by
  induction s using Finset.induction_on generalizing m with
  | empty =>
    simp only [Finset.prod_empty, MvPolynomial.coeff_one]
    split_ifs <;> simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact norm_coeff_mul_le (ha0 j (Finset.mem_insert_self j s))
      (Finset.prod_nonneg fun i hi => ha0 i (Finset.mem_insert_of_mem hi))
      (hA j (Finset.mem_insert_self j s))
      (ih (fun i hi => ha0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => hA i (Finset.mem_insert_of_mem hi))) m

end Ultra

section Apply

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 : ℕ} (l : ℕ) [Fact l.Prime]

def xzLetter : XZ Lt N0 N1 → Lt
  | Sum.inl v => v.1
  | Sum.inr v => v.1

def applyTerm (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (μ : XZ Lt N0 N1 →₀ ℕ) (c : ℤ) :
    MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((c : ℤ) : ℂ_[l]) * ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)

theorem applyAt0_eq_sum (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l Th P = ∑ μ ∈ P.support, applyTerm l Th μ (MvPolynomial.coeff μ P) := rfl

theorem applyTerm_zero (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (μ : XZ Lt N0 N1 →₀ ℕ) :
    applyTerm l Th μ 0 = 0 := by simp [applyTerm]

theorem applyAt0_eq_sum_of_subset (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) (S : Finset (XZ Lt N0 N1 →₀ ℕ)) (hS : P.support ⊆ S) :
    applyAt0 N0 N1 l Th P = ∑ μ ∈ S, applyTerm l Th μ (MvPolynomial.coeff μ P) := by
  rw [applyAt0_eq_sum]
  refine Finset.sum_subset hS fun μ _ hμ => ?_
  have : MvPolynomial.coeff μ P = 0 := by
    by_contra h; exact hμ (MvPolynomial.mem_support_iff.2 h)
  rw [this, applyTerm_zero]

theorem applyAt0_add (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P Q : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l Th (P + Q) = applyAt0 N0 N1 l Th P + applyAt0 N0 N1 l Th Q := by
  have h1 : P.support ⊆ P.support ∪ Q.support := Finset.subset_union_left
  have h2 : Q.support ⊆ P.support ∪ Q.support := Finset.subset_union_right
  rw [applyAt0_eq_sum_of_subset l Th _ _ MvPolynomial.support_add, applyAt0_eq_sum_of_subset l Th _ _ h1,
    applyAt0_eq_sum_of_subset l Th _ _ h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [applyTerm, MvPolynomial.coeff_add, Int.cast_add, add_mul, map_add]

def applyHom (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) :
    MvPolynomial (XZ Lt N0 N1) ℤ →+ MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] where
  toFun := applyAt0 N0 N1 l Th
  map_zero' := by simp [applyAt0]
  map_add' := applyAt0_add l Th

theorem applyHom_apply (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyHom l Th P = applyAt0 N0 N1 l Th P := rfl

theorem applyAt0_monomial (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (μ : XZ Lt N0 N1 →₀ ℕ) (c : ℤ) :
    applyAt0 N0 N1 l Th (MvPolynomial.monomial μ c) = applyTerm l Th μ c := by
  rw [applyAt0_eq_sum_of_subset l Th _ _ MvPolynomial.support_monomial_subset]
  simp

theorem applyAt0_one_one :
    applyAt0 N0 N1 l (1 : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) 1 = 1 := by
  rw [← MvPolynomial.C_1, ← MvPolynomial.monomial_zero', applyAt0_monomial]
  simp [applyTerm]

theorem sumFinsupp_add (μ μ' : XZ Lt N0 N1 →₀ ℕ) :
    Finsupp.sumFinsuppEquivProdFinsupp (μ + μ') =
      ((Finsupp.sumFinsuppEquivProdFinsupp μ).1 + (Finsupp.sumFinsuppEquivProdFinsupp μ').1,
        (Finsupp.sumFinsuppEquivProdFinsupp μ).2 + (Finsupp.sumFinsuppEquivProdFinsupp μ').2) := by
  ext v <;> simp

theorem applyTerm_mul {A1 A2 : Set Lt} (hA : Disjoint A1 A2) {T1 T2 : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]}
    (h1 : SerIn {v | v.1 ∈ A1} T1) (h2 : SerIn {v | v.1 ∈ A2} T2) {μ μ' : XZ Lt N0 N1 →₀ ℕ}
    (hμ : ∀ v, μ v ≠ 0 → xzLetter v ∈ A1) (hμ' : ∀ v, μ' v ≠ 0 → xzLetter v ∈ A2) (c c' : ℤ) :
    applyTerm l (T1 * T2) (μ + μ') (c * c') = applyTerm l T1 μ c * applyTerm l T2 μ' c' := by
  have hS : Disjoint {v : Lt × Fin N0 × Fin N1 | v.1 ∈ A1} {v | v.1 ∈ A2} :=
    Set.disjoint_left.2 fun v h h' => Set.disjoint_left.1 hA h h'
  have ha : ∀ v, (Finsupp.sumFinsuppEquivProdFinsupp μ).2 v ≠ 0 → v ∈ {v : Lt × Fin N0 × Fin N1 | v.1 ∈ A1} :=
    fun v hv => hμ (Sum.inr v) (by simpa [Finsupp.snd_sumFinsuppEquivProdFinsupp] using hv)
  have hb : ∀ v, (Finsupp.sumFinsuppEquivProdFinsupp μ').2 v ≠ 0 → v ∈ {v : Lt × Fin N0 × Fin N1 | v.1 ∈ A2} :=
    fun v hv => hμ' (Sum.inr v) (by simpa [Finsupp.snd_sumFinsuppEquivProdFinsupp] using hv)
  have hdis : Disjoint (Finsupp.sumFinsuppEquivProdFinsupp μ).2.support
      (Finsupp.sumFinsuppEquivProdFinsupp μ').2.support := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact Set.disjoint_left.1 hS (ha v (Finsupp.mem_support_iff.1 hv)) (hb v (Finsupp.mem_support_iff.1 hv'))
  simp only [applyTerm, MvPolynomial.monomial_mul, sumFinsupp_add]
  rw [Finsupp.prod_add_index_of_disjoint hdis, coeff_mul_of_disjoint hS h1 h2 ha hb]
  congr 1
  push_cast
  ring

theorem applyAt0_mul {A1 A2 : Set Lt} (hA : Disjoint A1 A2) {T1 T2 : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]}
    (h1 : SerIn {v | v.1 ∈ A1} T1) (h2 : SerIn {v | v.1 ∈ A2} T2) {P1 P2 : MvPolynomial (XZ Lt N0 N1) ℤ}
    (hP1 : P1 ∈ MvPolynomial.supported ℤ (xzLetter ⁻¹' A1)) (hP2 : P2 ∈ MvPolynomial.supported ℤ (xzLetter ⁻¹' A2)) :
    applyAt0 N0 N1 l (T1 * T2) (P1 * P2) = applyAt0 N0 N1 l T1 P1 * applyAt0 N0 N1 l T2 P2 := by
  have hv1 : ∀ μ ∈ P1.support, ∀ v, μ v ≠ 0 → xzLetter v ∈ A1 := by
    intro μ hμ v hv
    have : v ∈ P1.vars := (MvPolynomial.mem_vars_iff_mem_support v).2 ⟨μ, hμ, Finsupp.mem_support_iff.2 hv⟩
    exact MvPolynomial.mem_supported.1 hP1 (Finset.mem_coe.2 this)
  have hv2 : ∀ μ ∈ P2.support, ∀ v, μ v ≠ 0 → xzLetter v ∈ A2 := by
    intro μ hμ v hv
    have : v ∈ P2.vars := (MvPolynomial.mem_vars_iff_mem_support v).2 ⟨μ, hμ, Finsupp.mem_support_iff.2 hv⟩
    exact MvPolynomial.mem_supported.1 hP2 (Finset.mem_coe.2 this)
  have e1 := P1.as_sum
  have e2 := P2.as_sum
  have hprod : P1 * P2 = ∑ μ ∈ P1.support, ∑ μ' ∈ P2.support,
      MvPolynomial.monomial (μ + μ') (MvPolynomial.coeff μ P1 * MvPolynomial.coeff μ' P2) := by
    conv_lhs => rw [e1, e2]
    rw [Finset.sum_mul_sum]
    simp only [MvPolynomial.monomial_mul]
  rw [hprod]
  conv_rhs => rw [e1, e2]
  simp only [← applyHom_apply, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => Finset.sum_congr rfl fun μ' hμ' => ?_
  simp only [applyHom_apply, applyAt0_monomial]
  exact applyTerm_mul l hA h1 h2 (hv1 μ hμ) (hv2 μ' hμ') _ _

theorem applyAt0_prod {Ω : Type*} (s : Finset Ω) (A : Ω → Set Lt) (hA : (s : Set Ω).PairwiseDisjoint A)
    (T : Ω → MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : Ω → MvPolynomial (XZ Lt N0 N1) ℤ)
    (hT : ∀ ω ∈ s, SerIn {v | v.1 ∈ A ω} (T ω))
    (hP : ∀ ω ∈ s, P ω ∈ MvPolynomial.supported ℤ (xzLetter ⁻¹' A ω)) :
    applyAt0 N0 N1 l (∏ ω ∈ s, T ω) (∏ ω ∈ s, P ω) = ∏ ω ∈ s, applyAt0 N0 N1 l (T ω) (P ω) := by
  induction s using Finset.induction_on with
  | empty => simpa using applyAt0_one_one (Lt := Lt) (N0 := N0) (N1 := N1) l
  | insert a s ha ih =>
    have hA' : (s : Set Ω).PairwiseDisjoint A := hA.subset (by simp)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    have hdis : Disjoint (A a) (⋃ ω ∈ s, A ω) := by
      rw [Set.disjoint_iUnion₂_right]
      intro ω hω
      exact hA (by simp) (by simp [hω]) (fun h => ha (h ▸ hω))
    have hTs : SerIn {v : Lt × Fin N0 × Fin N1 | v.1 ∈ ⋃ ω ∈ s, A ω} (∏ ω ∈ s, T ω) :=
      SerIn.prod s fun ω hω => SerIn.mono (S := {v : Lt × Fin N0 × Fin N1 | v.1 ∈ A ω})
        (fun v hv => (Set.mem_iUnion₂.2 ⟨ω, hω, hv⟩ : v.1 ∈ ⋃ ω ∈ s, A ω)) (hT ω (by simp [hω]))
    rw [applyAt0_mul l hdis (hT a (by simp)) hTs
      (hP a (by simp))
      (Subalgebra.prod_mem _ fun ω hω => MvPolynomial.supported_mono
        (fun v (hv : xzLetter v ∈ A ω) => show xzLetter v ∈ ⋃ ω ∈ s, A ω from
          Set.mem_iUnion₂.2 ⟨ω, hω, hv⟩) (hP ω (by simp [hω])))]
    rw [ih hA' (fun ω hω => hT ω (by simp [hω])) (fun ω hω => hP ω (by simp [hω]))]

end Apply

end PI.OrbJet.OJ

end
