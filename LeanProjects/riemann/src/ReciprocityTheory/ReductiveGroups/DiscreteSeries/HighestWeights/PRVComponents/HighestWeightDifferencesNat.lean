import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.UniqueA

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section SL2

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ M}

lemma lie_relation_raise_lower (hF : Formalism.REAL.KRel ε F) {a b : Fin n} (he : ε a = ε b) (y : M) :
    F a b (F b a y) = F b a (F a b y) + F a a y - F b b y := by
  have h := hF a b b a he he.symm
  rw [if_pos rfl, if_pos rfl] at h
  have h2 := congrArg (fun T : Module.End ℂ M => T y) h
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h2
  rw [sub_eq_iff_eq_add] at h2
  rw [h2]
  abel

lemma lie_relation_diag_a_lower (hF : Formalism.REAL.KRel ε F) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b) (y : M) :
    F a a (F b a y) = F b a (F a a y) - F b a y := by
  have h := hF a a b a rfl he.symm
  rw [if_neg hab, if_pos rfl, zero_sub] at h
  have h2 := congrArg (fun T : Module.End ℂ M => T y) h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply] at h2
  rw [sub_eq_iff_eq_add] at h2
  rw [h2]
  abel

lemma lie_relation_diag_b_lower (hF : Formalism.REAL.KRel ε F) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b) (y : M) :
    F b b (F b a y) = F b a (F b b y) + F b a y := by
  have h := hF b b b a rfl he.symm
  rw [if_pos rfl, if_neg hab, sub_zero] at h
  have h2 := congrArg (fun T : Module.End ℂ M => T y) h
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h2
  rw [sub_eq_iff_eq_add] at h2
  rw [h2]
  abel

theorem exists_nat_weight_sub_eq_of_highest_vector_in_stable (hF : Formalism.REAL.KRel ε F) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b)
    (S : Submodule ℂ M) [FiniteDimensional ℂ S] (hS : ∀ y ∈ S, F b a y ∈ S)
    {v : M} (hv : v ∈ S) (hv0 : v ≠ 0) {la lb : ℂ} (ha : F a a v = la • v) (hb : F b b v = lb • v)
    (h0 : F a b v = 0) : ∃ m : ℕ, la - lb = m := by
  classical
  let vk : ℕ → M := fun k => (F b a ^ k) v
  have hvk0 : vk 0 = v := by simp [vk]
  have hvk : ∀ k, vk (k + 1) = F b a (vk k) := fun k => by
    simp only [vk, pow_succ', Module.End.mul_apply]
  have hmem : ∀ k, vk k ∈ S := by
    intro k
    induction k with
    | zero => rw [hvk0]; exact hv
    | succ k ih => rw [hvk]; exact hS _ ih
  have hwa : ∀ k : ℕ, F a a (vk k) = (la - k) • vk k := by
    intro k
    induction k with
    | zero => rw [hvk0, ha]; simp
    | succ k ih =>
      rw [hvk, lie_relation_diag_a_lower hF hab he, ih, map_smul]
      push_cast
      module
  have hwb : ∀ k : ℕ, F b b (vk k) = (lb + k) • vk k := by
    intro k
    induction k with
    | zero => rw [hvk0, hb]; simp
    | succ k ih =>
      rw [hvk, lie_relation_diag_b_lower hF hab he, ih, map_smul]
      push_cast
      module
  have hE : ∀ k : ℕ, F a b (vk (k + 1)) = (((k : ℂ) + 1) * (la - lb - k)) • vk k := by
    intro k
    induction k with
    | zero =>
      rw [hvk, hvk0, lie_relation_raise_lower hF he, h0, map_zero, ha, hb]
      push_cast
      module
    | succ k ih =>
      rw [hvk (k + 1), lie_relation_raise_lower hF he, ih, map_smul, ← hvk, hwa, hwb]
      push_cast
      module
  have hex : ∃ k, vk k = 0 := by
    by_contra hcon
    push_neg at hcon
    have hli : LinearIndependent ℂ vk :=
      Module.End.eigenvectors_linearIndependent' (F a a) (fun k : ℕ => la - k)
        (by
          intro i j hij
          have h1 : (i : ℂ) = j := sub_right_inj.1 hij
          exact_mod_cast h1)
        vk (fun k => Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 (hwa k), hcon k⟩)
    let vs : ℕ → S := fun k => ⟨vk k, hmem k⟩
    have hls : LinearIndependent ℂ vs := LinearIndependent.of_comp S.subtype hli
    exact Module.Finite.not_linearIndependent_of_infinite vs hls
  have hk0 : vk (Nat.find hex) = 0 := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    rw [h, hvk0] at hk0
    exact hv0 hk0
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hvm : vk m ≠ 0 := Nat.find_min hex (by omega)
  have h1 := hE m
  rw [← hm, hk0, map_zero] at h1
  have hcoef : ((m : ℂ) + 1) * (la - lb - m) = 0 := by
    by_contra hne
    exact hvm ((smul_eq_zero.1 h1.symm).resolve_left hne)
  have hm1 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  refine ⟨m, ?_⟩
  have h2 := (mul_eq_zero.1 hcoef).resolve_left hm1
  linear_combination h2

theorem highest_weight_differences_nat (hF : Formalism.REAL.KRel ε F) (S : Submodule ℂ M) [FiniteDimensional ℂ S]
    (hS : IsKStableSub ε F S) {μ : Fin n → ℝ} {v : M} (hv : v ∈ S) (hv0 : v ≠ 0)
    (hw : IsKHWVec ε F μ v) : ∀ a b, a < b → ε a = ε b → ∃ m : ℕ, μ a - μ b = m := by
  intro a b hab he
  obtain ⟨m, hm⟩ := exists_nat_weight_sub_eq_of_highest_vector_in_stable hF (ne_of_lt hab) he S (fun y hy => hS b a he.symm y hy) hv hv0
    (hw.1 a) (hw.1 b) (hw.2 a b hab he)
  refine ⟨m, ?_⟩
  apply Complex.ofReal_injective
  push_cast
  exact hm

end SL2

theorem lowest_weight_differences_nat {ε : Fin n → Bool} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Fin n → Fin n → Matrix ι ι ℂ} (hG : Formalism.REAL.KRel ε G) {ν : Fin n → ℝ} {f : ι → ℂ} (hf0 : f ≠ 0)
    (hfw : ∀ a, G a a *ᵥ f = ((ν a : ℝ) : ℂ) • f) (hfl : ∀ a b, b < a → ε a = ε b → G a b *ᵥ f = 0) :
    ∀ a b, a < b → ε a = ε b → ∃ m : ℕ, ν b - ν a = m := by
  intro a b hab he
  have hR : Formalism.REAL.KRel ε (fun a b => Matrix.toLinAlgEquiv' (G a b)) :=
    uq_kRel_map ε G (Matrix.toLinAlgEquiv' : Matrix ι ι ℂ ≃ₐ[ℂ] _).toRingEquiv.toRingHom hG
  have happ : ∀ a b (x : ι → ℂ), Matrix.toLinAlgEquiv' (G a b) x = G a b *ᵥ x := fun a b x => rfl
  obtain ⟨m, hm⟩ := exists_nat_weight_sub_eq_of_highest_vector_in_stable hR (ne_of_lt hab).symm he.symm (⊤ : Submodule ℂ (ι → ℂ))
    (fun _ _ => Submodule.mem_top) Submodule.mem_top hf0 (la := ((ν b : ℝ) : ℂ)) (lb := ((ν a : ℝ) : ℂ))
    (by rw [happ]; exact hfw b) (by rw [happ]; exact hfw a) (by rw [happ]; exact hfl b a hab he.symm)
  refine ⟨m, ?_⟩
  apply Complex.ofReal_injective
  push_cast
  exact hm

theorem block_weights_integral {ε : Fin n → Bool} {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F) (S : Submodule ℂ M) [FiniteDimensional ℂ S]
    (hS : IsKStableSub ε F S) {Λ : Fin n → ℝ} {v : M} (hv : v ∈ S) (hv0 : v ≠ 0) (hw : IsKHWVec ε F Λ v)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Fin n → Fin n → Matrix ι ι ℂ} (hG : Formalism.REAL.KRel ε G) {ν : Fin n → ℝ} {f : ι → ℂ} (hf0 : f ≠ 0)
    (hfw : ∀ a, G a a *ᵥ f = ((ν a : ℝ) : ℂ) • f) (hfl : ∀ a b, b < a → ε a = ε b → G a b *ᵥ f = 0) :
    ∀ a b, ε a = ε b → ∃ z : ℤ, (Λ + ν) a - (Λ + ν) b = z := by
  have key : ∀ a b, a < b → ε a = ε b → ∃ z : ℤ, (Λ + ν) a - (Λ + ν) b = z := by
    intro a b hab he
    obtain ⟨m1, h1⟩ := highest_weight_differences_nat hF S hS hv hv0 hw a b hab he
    obtain ⟨m2, h2⟩ := lowest_weight_differences_nat hG hf0 hfw hfl a b hab he
    refine ⟨(m1 : ℤ) - m2, ?_⟩
    simp only [Pi.add_apply]
    push_cast
    linarith
  intro a b he
  rcases lt_trichotomy a b with h | h | h
  · exact key a b h he
  · subst h
    exact ⟨0, by simp⟩
  · obtain ⟨z, hz⟩ := key b a h he.symm
    exact ⟨-z, by push_cast; linarith⟩

end ReciprocityTheory.ChartRestriction.DS.HW
