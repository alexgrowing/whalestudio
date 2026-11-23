import Formalism.SharpRestriction.GrowthBounds.RootWeights.DegreeZeroWeightsBounded

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem mem_weightSp_iff (E : GLOps n K V) (μ : Fin n → ℤ) (x : V) :
    x ∈ weightSp E μ ↔ ∀ c, E c c x = (μ c : K) • x := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]

private theorem E_apply_mem_weightSp_add_rootW_of_ne {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b)
    {μ : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E μ) : E a b x ∈ weightSp E (μ + rootW a b) := by
  rw [mem_weightSp_iff] at hx ⊢
  intro c
  have hc := LinearMap.congr_fun (hE.1 c c a b) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul] at hc
  rw [sub_eq_iff_eq_add] at hc
  by_cases h1 : c = a
  · have h2 : ¬ b = c := fun h => hab (h1.symm.trans h.symm)
    rw [if_pos h1, if_neg h2, h1] at hc
    rw [h1] at *
    simp only [LinearMap.zero_apply, sub_zero] at hc
    rw [hc]
    simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_apply, hab, if_false,
      sub_zero, Int.cast_add, Int.cast_one, add_smul, one_smul]
    abel
  · by_cases h2 : b = c
    · rw [if_neg h1, if_pos h2] at hc
      subst h2
      simp only [LinearMap.zero_apply, zero_sub] at hc
      rw [hc]
      simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_apply,
        Ne.symm hab, if_false, zero_sub, Int.cast_add, Int.cast_neg, Int.cast_one, add_smul,
        neg_smul, one_smul]
      abel
    · rw [if_neg h1, if_neg h2] at hc
      simp only [LinearMap.zero_apply, sub_zero, zero_add] at hc
      rw [hc]
      have h2' : c ≠ b := fun h => h2 h.symm
      simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply, h1, h2', if_false, sub_zero,
        add_zero]

private theorem E_pow_apply_mem_weightSp_ne_zero_of_highest [CharZero K] {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n}
    (hab : a ≠ b) {μ : Fin n → ℤ} {v : V} (hv : v ∈ weightSp E μ) (hv0 : v ≠ 0)
    (htop : E a b v = 0) (N : ℕ) (hN : (N : ℤ) = μ a - μ b) :
    (E b a ^ N) v ∈ weightSp E (μ + (N : ℤ) • rootW b a) ∧ (E b a ^ N) v ≠ 0 := by
  have hNK : (N : K) = (μ a : K) - (μ b : K) := by exact_mod_cast hN
  have hlow : ∀ k : ℕ, (E b a ^ k) v ∈ weightSp E (μ + (k : ℤ) • rootW b a) := by
    intro k
    induction k with
    | zero => simpa using hv
    | succ k ih =>
      have h := E_apply_mem_weightSp_add_rootW_of_ne hE (Ne.symm hab) ih
      have e : μ + ((k + 1 : ℕ) : ℤ) • rootW b a = μ + (k : ℤ) • rootW b a + rootW b a := by
        push_cast
        rw [add_smul, one_smul, add_assoc]
      rw [pow_succ', Module.End.mul_apply, e]
      exact h
  have hcomm : ∀ w : V, E a b (E b a w) = E b a (E a b w) + (E a a w - E b b w) := by
    intro w
    have h := LinearMap.congr_fun (hE.1 a b b a) w
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    exact sub_eq_iff_eq_add'.1 h
  have hdiag : ∀ k : ℕ, E a a ((E b a ^ k) v) - E b b ((E b a ^ k) v) =
      ((N : K) - 2 * k) • (E b a ^ k) v := by
    intro k
    have h := (mem_weightSp_iff E _ _).1 (hlow k)
    rw [h a, h b, ← sub_smul]
    congr 1
    simp only [rootW, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_apply,
      hab, Ne.symm hab, if_false, smul_eq_mul]
    push_cast
    rw [hNK]
    ring
  have hQ : ∀ k : ℕ, E a b ((E b a ^ (k + 1)) v) = (((k : K) + 1) * ((N : K) - k)) • (E b a ^ k) v := by
    intro k
    induction k with
    | zero =>
      have h0 := hdiag 0
      simp only [pow_zero, Module.End.one_apply, Nat.cast_zero, mul_zero, sub_zero] at h0
      simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero, one_mul]
      rw [hcomm, htop, map_zero, zero_add, h0]
    | succ k ih =>
      have fold : E b a ((E b a ^ k) v) = (E b a ^ (k + 1)) v := by
        rw [pow_succ', Module.End.mul_apply]
      rw [pow_succ' (E b a) (k + 1), Module.End.mul_apply, hcomm, ih, map_smul, fold, hdiag (k + 1),
        ← add_smul]
      congr 1
      push_cast
      ring
  have hne : ∀ k : ℕ, k ≤ N → (E b a ^ k) v ≠ 0 := by
    intro k
    induction k with
    | zero => intro _; simpa using hv0
    | succ k ih =>
      intro hk h
      apply ih (by omega)
      have hq := hQ k
      rw [h, map_zero] at hq
      have hc : ((k : K) + 1) * ((N : K) - k) ≠ 0 := by
        apply mul_ne_zero
        · exact_mod_cast Nat.succ_ne_zero k
        · exact sub_ne_zero.2 (by exact_mod_cast (show N ≠ k by omega))
      exact (smul_eq_zero.1 hq.symm).resolve_left hc
  exact ⟨hlow N, hne N le_rfl⟩

private theorem finite_set_of_nonzero_weightSp [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) :
    {μ : Fin n → ℤ | weightSp E μ ≠ ⊥}.Finite := by
  have hfin : ∀ c : Fin n, {z : ℤ | (E c c).HasEigenvalue (z : K)}.Finite := fun c =>
    (Module.End.finite_hasEigenvalue (E c c)).preimage Int.cast_injective.injOn
  refine (Set.Finite.pi (t := fun c => {z : ℤ | (E c c).HasEigenvalue (z : K)}) hfin).subset ?_
  intro μ hμ
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  rw [mem_weightSp_iff] at hx
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, true_implies]
  intro c
  exact Module.End.hasEigenvalue_of_hasEigenvector
    (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 (hx c), hx0⟩)

theorem root_string_through_weight [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) (ν : Fin n → ℤ)
    (hν : weightSp E ν ≠ ⊥) (a b : Fin n) (hab : a ≠ b) (hpos : 0 < ν a - ν b) :
    ∃ t N : ℕ, (N : ℤ) = ν a - ν b + 2 * t ∧ weightSp E (ν + (t : ℤ) • rootW a b) ≠ ⊥ ∧
      weightSp E (ν + (t : ℤ) • rootW a b + (N : ℤ) • rootW b a) ≠ ⊥ := by
  classical
  have hinj : Function.Injective (fun t : ℕ => ν + (t : ℤ) • rootW a b) := by
    intro t1 t2 h
    have h' := congr_fun h a
    simp [rootW, hab] at h'
    exact_mod_cast h'
  obtain ⟨T, hTdef⟩ : ∃ T : Set ℕ, T = {t : ℕ | weightSp E (ν + (t : ℤ) • rootW a b) ≠ ⊥} := ⟨_, rfl⟩
  have hT : T.Finite := by
    rw [hTdef]
    exact (finite_set_of_nonzero_weightSp E).preimage hinj.injOn
  have h0 : (0 : ℕ) ∈ T := by
    rw [hTdef]
    simpa using hν
  have ht : sSup T ∈ T := Nat.sSup_mem ⟨0, h0⟩ hT.bddAbove
  have ht1 : sSup T + 1 ∉ T := fun h => by
    have := le_csSup hT.bddAbove h
    omega
  have ht' : weightSp E (ν + ((sSup T : ℕ) : ℤ) • rootW a b) ≠ ⊥ := (Set.ext_iff.1 hTdef _).1 ht
  have ht1' : ¬ weightSp E (ν + ((sSup T + 1 : ℕ) : ℤ) • rootW a b) ≠ ⊥ :=
    fun h => ht1 ((Set.ext_iff.1 hTdef _).2 h)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ht'
  have htop : E a b v = 0 := by
    have h1 := E_apply_mem_weightSp_add_rootW_of_ne hE hab hv
    have e : ν + ((sSup T : ℕ) : ℤ) • rootW a b + rootW a b =
        ν + ((sSup T + 1 : ℕ) : ℤ) • rootW a b := by
      push_cast
      rw [add_smul, one_smul, add_assoc]
    rw [e] at h1
    have hbot : weightSp E (ν + ((sSup T + 1 : ℕ) : ℤ) • rootW a b) = ⊥ := by
      by_contra hne
      exact ht1' hne
    rw [hbot, Submodule.mem_bot] at h1
    exact h1
  have hμa : (ν + ((sSup T : ℕ) : ℤ) • rootW a b) a = ν a + sSup T := by
    simp [rootW, hab]
  have hμb : (ν + ((sSup T : ℕ) : ℤ) • rootW a b) b = ν b - sSup T := by
    simp [rootW, Ne.symm hab]
    ring
  have hnn : 0 ≤ ν a - ν b + 2 * ((sSup T : ℕ) : ℤ) := by omega
  refine ⟨sSup T, (ν a - ν b + 2 * ((sSup T : ℕ) : ℤ)).toNat, Int.toNat_of_nonneg hnn, ht', ?_⟩
  obtain ⟨hmem, hne⟩ := E_pow_apply_mem_weightSp_ne_zero_of_highest hE hab hv hv0 htop _
    (by rw [Int.toNat_of_nonneg hnn, hμa, hμb]; ring)
  intro hbot
  rw [hbot, Submodule.mem_bot] at hmem
  exact hne hmem

theorem root_differences_bddAbove_top [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) :
    BddAbove {k : ℕ | ∃ mu ∈ wtsOf E (⊤ : Submodule K V), ∃ nu ∈ wtsOf E (⊤ : Submodule K V), ∃ a b, a ≠ b ∧
      mu - nu = (k : ℤ) • rootW a b} := by
  classical
  have hW := finite_set_of_nonzero_weightSp E
  have hsub : {k : ℕ | ∃ mu ∈ wtsOf E (⊤ : Submodule K V), ∃ nu ∈ wtsOf E (⊤ : Submodule K V), ∃ a b,
      a ≠ b ∧ mu - nu = (k : ℤ) • rootW a b} ⊆
      (fun p : (Fin n → ℤ) × (Fin n → ℤ) × Fin n => (p.1 p.2.2 - p.2.1 p.2.2).toNat) ''
        ({μ : Fin n → ℤ | weightSp E μ ≠ ⊥} ×ˢ ({μ : Fin n → ℤ | weightSp E μ ≠ ⊥} ×ˢ Set.univ)) := by
    rintro k ⟨mu, hmu, nu, hnu, a, b, hab, h⟩
    have hmu' : weightSp E mu ≠ ⊥ := by simpa [wtsOf] using hmu
    have hnu' : weightSp E nu ≠ ⊥ := by simpa [wtsOf] using hnu
    refine ⟨(mu, nu, a), ⟨hmu', hnu', Set.mem_univ _⟩, ?_⟩
    have h' := congr_fun h a
    simp [rootW, hab] at h'
    simp [h']
  exact ((hW.prod (hW.prod Set.finite_univ)).image _).subset hsub |>.bddAbove

theorem weight_difference_le_ell_of_rep [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) (ν : Fin n → ℤ)
    (hν : weightSp E ν ≠ ⊥) (a b : Fin n) (hab : a ≠ b) (hpos : 0 < ν a - ν b) :
    ν a - ν b ≤ (ellOf E (⊤ : Submodule K V) : ℤ) := by
  obtain ⟨t, N, hN, h1, h2⟩ := root_string_through_weight hE ν hν a b hab hpos
  have hr : rootW b a = -rootW a b := by
    ext c
    simp only [rootW, Pi.sub_apply, Pi.neg_apply]
    ring
  have hmem : N ∈ {k : ℕ | ∃ mu ∈ wtsOf E (⊤ : Submodule K V), ∃ nu ∈ wtsOf E (⊤ : Submodule K V),
      ∃ a b, a ≠ b ∧ mu - nu = (k : ℤ) • rootW a b} := by
    refine ⟨_, by simpa [wtsOf] using h1, _, by simpa [wtsOf] using h2, a, b, hab, ?_⟩
    rw [hr]
    ext c
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
      Pi.natCast_apply]
    ring
  have hle : N ≤ ellOf E (⊤ : Submodule K V) := le_csSup (root_differences_bddAbove_top E) hmem
  have hle' := (Nat.cast_le (α := ℤ)).2 hle
  omega

end Formalism.MainNotions.G.GLWeightTheory
