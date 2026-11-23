import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDefs

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

namespace PartialSpanProjection

variable {O : Type} [CommRing O] {σ : Type}

theorem exists_retraction [IsDomain O] [IsPrincipalIdealRing O] (X : Submodule O (MvPolynomial σ O))
    (s : Finset (σ →₀ ℕ)) (hs : ∀ x ∈ X, x.support ⊆ s)
    (hsat : ∀ (c : O) (x : MvPolynomial σ O), c ≠ 0 → c • x ∈ X → x ∈ X) :
    ∃ q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O, (∀ A, q A ∈ X) ∧ ∀ x ∈ X, q x = x := by
  let e : (s → O) →ₗ[O] MvPolynomial σ O := Fintype.linearCombination O (fun m : s => monomial m.1 (1 : O))
  let r : MvPolynomial σ O →ₗ[O] (s → O) := LinearMap.pi (fun m => lcoeff O m.1)
  have her : ∀ x : MvPolynomial σ O, x.support ⊆ s → e (r x) = x := by
    intro x hx
    simp only [e, r, Fintype.linearCombination_apply, LinearMap.pi_apply, lcoeff_apply]
    rw [Finset.sum_coe_sort s (fun m => coeff m x • monomial m (1 : O))]
    conv_rhs => rw [← support_sum_monomial_coeff x]
    symm
    refine (Finset.sum_subset hx ?_).trans ?_
    · intro m _ hm
      rw [notMem_support_iff.1 hm, monomial_zero]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]
  let X' : Submodule O (s → O) := X.comap e
  have htf : Module.IsTorsionFree O ((s → O) ⧸ X') := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro c m h
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      rw [Submodule.Quotient.mk_eq_zero]
      show e f ∈ X
      apply hsat c _ hc
      have h' : e (c • f) ∈ X := h
      rwa [map_smul] at h'
  obtain ⟨g, hg⟩ := X'.mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ X')
  let ρ : (s → O) →ₗ[O] (s → O) := LinearMap.id - g ∘ₗ X'.mkQ
  have hρ1 : ∀ f, ρ f ∈ X' := by
    intro f
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h := LinearMap.congr_fun hg (X'.mkQ f)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
    simp only [ρ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h, sub_self]
  have hρ2 : ∀ f ∈ X', ρ f = f := by
    intro f hf
    have h : X'.mkQ f = 0 := by rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hf
    simp only [ρ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h, map_zero, sub_zero]
  refine ⟨e ∘ₗ ρ ∘ₗ r, fun A => hρ1 _, fun x hx => ?_⟩
  have h1 := her x (hs x hx)
  have h2 : r x ∈ X' := by
    show e (r x) ∈ X
    rwa [h1]
  simp only [LinearMap.comp_apply]
  rw [hρ2 _ h2, h1]

theorem supp_of_mem {S : Set σ} {A : MvPolynomial σ O} (hA : A ∈ supported O S) {a : σ →₀ ℕ}
    (ha : a ∈ A.support) : ∀ v ∈ a.support, v ∈ S := by
  intro v hv
  exact (MvPolynomial.mem_supported.1 hA) ((MvPolynomial.mem_vars v).2 ⟨a, ha, hv⟩)

theorem monomial_mem {S : Set σ} {a : σ →₀ ℕ} (c : O) (ha : ∀ v ∈ a.support, v ∈ S) :
    monomial a c ∈ supported O S := by
  rw [MvPolynomial.mem_supported]
  intro v hv
  obtain ⟨m, hm, hvm⟩ := (MvPolynomial.mem_vars v).1 hv
  have hma : m = a := Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hm)
  subst hma
  exact ha v hvm

variable {ι : Type} (π : σ → ι)

def pj (j : ι) (q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O) : MvPolynomial σ O →ₗ[O] MvPolynomial σ O :=
  (basisMonomials σ O).constr O
    (fun m => q (monomial (m.filter (fun v => π v = j)) 1) * monomial (m.filter (fun v => π v ≠ j)) 1)

theorem pj_monomial (j : ι) (q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O) (m : σ →₀ ℕ) (c : O) :
    pj π j q (monomial m c) =
      c • (q (monomial (m.filter (fun v => π v = j)) 1) * monomial (m.filter (fun v => π v ≠ j)) 1) := by
  have e : monomial m c = c • (basisMonomials σ O m) := by
    rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, pj, Module.Basis.constr_basis]

theorem pj_mono_mul (j : ι) (q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O) {a b : σ →₀ ℕ}
    (ha : ∀ v ∈ a.support, π v = j) (hb : ∀ v ∈ b.support, π v ≠ j) (ca cb : O) :
    pj π j q (monomial a ca * monomial b cb) = q (monomial a ca) * monomial b cb := by
  have h1 : (a + b).filter (fun v => π v = j) = a := by
    ext v
    simp only [Finsupp.filter_apply, Finsupp.add_apply]
    by_cases hv : π v = j
    · rw [if_pos hv]
      have : b v = 0 := by
        by_contra h
        exact hb v (Finsupp.mem_support_iff.2 h) hv
      rw [this, add_zero]
    · rw [if_neg hv]
      by_contra h
      exact hv (ha v (Finsupp.mem_support_iff.2 (Ne.symm h)))
  have h2 : (a + b).filter (fun v => π v ≠ j) = b := by
    ext v
    simp only [Finsupp.filter_apply, Finsupp.add_apply]
    by_cases hv : π v = j
    · rw [if_neg (not_not.2 hv)]
      have : b v = 0 := by
        by_contra h
        exact hb v (Finsupp.mem_support_iff.2 h) hv
      exact this.symm
    · rw [if_pos hv]
      have : a v = 0 := by
        by_contra h
        exact hv (ha v (Finsupp.mem_support_iff.2 h))
      rw [this, zero_add]
  rw [monomial_mul, pj_monomial, h1, h2]
  have e : monomial a ca = ca • monomial a (1 : O) := by rw [smul_monomial, smul_eq_mul, mul_one]
  have e' : monomial b cb = cb • monomial b (1 : O) := by rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, e', map_smul, smul_mul_smul_comm, mul_comm ca cb, mul_smul]

theorem pj_mul (j : ι) (q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O) {A M : MvPolynomial σ O}
    (hA : A ∈ supported O {v | π v = j}) (hM : M ∈ supported O {v | π v ≠ j}) :
    pj π j q (A * M) = q A * M := by
  have eA := A.as_sum
  have eM := M.as_sum
  calc pj π j q (A * M)
      = pj π j q ((∑ a ∈ A.support, monomial a (coeff a A)) * ∑ b ∈ M.support, monomial b (coeff b M)) := by
        rw [← eA, ← eM]
    _ = ∑ a ∈ A.support, ∑ b ∈ M.support, pj π j q (monomial a (coeff a A) * monomial b (coeff b M)) := by
        rw [Finset.sum_mul_sum, map_sum]
        simp only [map_sum]
    _ = ∑ a ∈ A.support, ∑ b ∈ M.support, q (monomial a (coeff a A)) * monomial b (coeff b M) :=
        Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb =>
          pj_mono_mul π j q (supp_of_mem hA ha) (supp_of_mem hM hb) _ _
    _ = q A * M := by
        rw [← Finset.sum_mul_sum, ← map_sum, ← eA, ← eM]

theorem pj_fix (j : ι) (q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O) (Xj : Submodule O (MvPolynomial σ O))
    (hX : ∀ x ∈ Xj, x ∈ supported O {v | π v = j}) (hq : ∀ x ∈ Xj, q x = x) {F : MvPolynomial σ O}
    (hF : F ∈ Submodule.span O {y | ∃ x ∈ Xj, ∃ M ∈ supported O {v | π v ≠ j}, y = x * M}) :
    pj π j q F = F := by
  induction hF using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, M, hM, rfl⟩ := hy
    rw [pj_mul π j q (hX x hx) hM, hq x hx]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz]
  | smul c y _ hy => rw [map_smul, hy]

def W (X : ι → Submodule O (MvPolynomial σ O)) (S : Finset ι) : Submodule O (MvPolynomial σ O) :=
  Submodule.span O {y | ∃ x : ι → MvPolynomial σ O, (∀ j, x j ∈ X j) ∧
    ∃ M ∈ supported O {v | π v ∉ S}, y = (∏ j ∈ S, x j) * M}

theorem projection_mem_partial_span (X : ι → Submodule O (MvPolynomial σ O)) (hX : ∀ j, ∀ x ∈ X j, x ∈ supported O {v | π v = j})
    (S : Finset ι) (j : ι) (hj : j ∉ S) (q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O) (hq : ∀ A, q A ∈ X j)
    {G : MvPolynomial σ O} (hG : G ∈ W π X S) : pj π j q G ∈ W π X (insert j S) := by
  have hle : W π X S ≤ (W π X (insert j S)).comap (pj π j q) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, M, hM, rfl⟩
    show pj π j q ((∏ i ∈ S, x i) * M) ∈ W π X (insert j S)
    have hP : (∏ i ∈ S, x i) ∈ supported O {v | π v ≠ j} := by
      refine Subalgebra.prod_mem _ fun i hi => ?_
      refine supported_mono ?_ (hX i _ (hx i))
      intro v hv
      have hv' : π v = i := hv
      show π v ≠ j
      rw [hv']
      rintro rfl
      exact hj hi
    have hsum : (∏ i ∈ S, x i) * M = ∑ b ∈ M.support,
        monomial (b.filter (fun v => π v = j)) (coeff b M) *
          ((∏ i ∈ S, x i) * monomial (b.filter (fun v => π v ≠ j)) 1) := by
      conv_lhs => rw [← support_sum_monomial_coeff M]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, monomial_mul, mul_one, Finsupp.filter_add_filter_not]
    rw [hsum, map_sum]
    refine Submodule.sum_mem _ fun b hb => ?_
    have hb1 : monomial (b.filter (fun v => π v = j)) (coeff b M) ∈ supported O {v | π v = j} := by
      refine monomial_mem _ fun v hv => ?_
      rw [Finsupp.support_filter, Finset.mem_filter] at hv
      exact hv.2
    have hb2 : ∀ v ∈ (b.filter (fun v => π v ≠ j)).support, π v ≠ j ∧ v ∈ b.support := by
      intro v hv
      rw [Finsupp.support_filter, Finset.mem_filter] at hv
      exact ⟨hv.2, hv.1⟩
    have hb3 : monomial (b.filter (fun v => π v ≠ j)) (1 : O) ∈ supported O {v | π v ≠ j} :=
      monomial_mem _ fun v hv => (hb2 v hv).1
    rw [pj_mul π j q hb1 (Subalgebra.mul_mem _ hP hb3)]
    refine Submodule.subset_span
      ⟨Function.update x j (q (monomial (b.filter (fun v => π v = j)) (coeff b M))), ?_,
        monomial (b.filter (fun v => π v ≠ j)) 1, ?_, ?_⟩
    · intro i
      by_cases hi : i = j
      · subst hi
        rw [Function.update_self]
        exact hq _
      · rw [Function.update_of_ne hi]
        exact hx i
    · refine monomial_mem _ fun v hv => ?_
      show π v ∉ insert j S
      rw [Finset.mem_insert, not_or]
      exact ⟨(hb2 v hv).1, supp_of_mem hM hb v (hb2 v hv).2⟩
    · rw [Finset.prod_insert hj, Function.update_self, mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Function.update_of_ne]
      rintro rfl
      exact hj hi
  exact hle hG

end PartialSpanProjection

open PartialSpanProjection in

theorem atl : ATL := by
  intro O _ _ _ ι σ _ _ π X hX hfin hsat F hF
  have hq : ∀ j, ∃ q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O, (∀ A, q A ∈ X j) ∧ ∀ x ∈ X j, q x = x := by
    intro j
    obtain ⟨s, hs⟩ := hfin j
    exact exists_retraction (X j) s hs (hsat j)
  choose q hq1 hq2 using hq
  have hW : ∀ S : Finset ι, F ∈ W π X S := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine Submodule.subset_span ⟨fun _ => 0, fun j => (X j).zero_mem, F, ?_, ?_⟩
      · rw [mem_supported]
        intro v _
        exact Finset.notMem_empty _
      · rw [Finset.prod_empty, one_mul]
    | insert j S hj ih =>
      have h := projection_mem_partial_span π X hX S j hj (q j) (hq1 j) ih
      rwa [pj_fix π j (q j) (X j) (hX j) (hq2 j) (hF j)] at h
  have hle : W π X Finset.univ ≤
      Submodule.span O {y | ∃ x : ι → MvPolynomial σ O, (∀ j, x j ∈ X j) ∧ y = ∏ j, x j} := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, M, hM, rfl⟩
    have hemp : {v | π v ∉ (Finset.univ : Finset ι)} = (∅ : Set σ) := by
      ext v
      simp
    rw [hemp, supported_empty] at hM
    obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 hM
    have : (∏ j, x j) * algebraMap O (MvPolynomial σ O) c = c • ∏ j, x j := by
      rw [Algebra.smul_def, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  exact hle (hW Finset.univ)

end Formalism.MainNotions.Proposition5Numerics
