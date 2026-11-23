import Formalism.SharpRestriction.GrowthBounds.RootWeights.IrreducibleStableContainsEqTop

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def weightHeightAscending (nu : Fin n → ℤ) : ℤ := ∑ c : Fin n, ((c : ℕ) : ℤ) * nu c

theorem weightHeightAscending_add_root (nu : Fin n → ℤ) (a b : Fin n) :
    weightHeightAscending (nu + rootW a b) = weightHeightAscending nu + (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) := by
  unfold weightHeightAscending rootW
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem irreducible_lowering_word_weight [NeZero n] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    {u : Module.End (KK O) V} (hu : u ∈ loweringOperatorMonoid E) :
    ∃ nu, u v ∈ weightSp E nu ∧ ((nu = lam ∧ u v = v) ∨ weightHeightAscending lam < weightHeightAscending nu) ∧
      nu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ nu (lastIdx n) := by
  have hE : IsGLRep E := hI.1
  have hv : v ∈ weightSp E lam := hI.2.2.1.2.1
  unfold loweringOperatorMonoid at hu
  induction hu using Submonoid.closure_induction_left with
  | one => exact ⟨lam, hv, Or.inl ⟨rfl, rfl⟩, le_rfl, le_rfl⟩
  | mul_left g hg w _ ih =>
    obtain ⟨a, b, hba, rfl⟩ := hg
    obtain ⟨nu, hnu, hor, h0, hl⟩ := ih
    refine ⟨nu + rootW a b, gl_rep_operator_weight_shift hE hnu a b, Or.inr ?_, ?_, ?_⟩
    · have hab : ((b : ℕ) : ℤ) < ((a : ℕ) : ℤ) := by exact_mod_cast hba
      rw [weightHeightAscending_add_root]
      rcases hor with ⟨rfl, -⟩ | h
      · linarith
      · linarith
    · have ha0 : a ≠ 0 := by
        intro h; rw [h] at hba; exact absurd hba (Fin.not_lt_zero _)
      have : (nu + rootW a b) 0 ≤ nu 0 := by
        simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_neg (Ne.symm ha0)]
        split_ifs <;> omega
      exact this.trans h0
    · have hbl : b ≠ lastIdx n := by
        intro h
        have : (a : ℕ) ≤ n - 1 := Nat.le_sub_one_of_lt a.isLt
        have hb : (b : ℕ) = n - 1 := by rw [h]; rfl
        have : (b : ℕ) < (a : ℕ) := hba
        omega
      have : nu (lastIdx n) ≤ (nu + rootW a b) (lastIdx n) := by
        simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_neg (Ne.symm hbl)]
        split_ifs <;> omega
      exact hl.trans this

theorem top_le_line_sup_higher_weights [NeZero n] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    (⊤ : Submodule (KK O) V) ≤ Submodule.span (KK O) {v} ⊔ ⨆ nu, ⨆ (_ : weightHeightAscending lam < weightHeightAscending nu), weightSp E nu := by
  rw [← irreducible_lowering_span_top hI, Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨nu, hnu, h1 | h1, -⟩ := irreducible_lowering_word_weight hI hu
  · rw [h1.2]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
  · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem nu (Submodule.mem_iSup_of_mem h1 hnu))

theorem top_le_end_bounded_weights [NeZero n] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    (⊤ : Submodule (KK O) V) ≤ ⨆ nu, ⨆ (_ : nu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ nu (lastIdx n)), weightSp E nu := by
  rw [← irreducible_lowering_span_top hI, Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨nu, hnu, -, h0, hl⟩ := irreducible_lowering_word_weight hI hu
  exact Submodule.mem_iSup_of_mem nu (Submodule.mem_iSup_of_mem ⟨h0, hl⟩ hnu)

theorem irreducible_weight_end_bounds [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu) (h0 : x ≠ 0) :
    nu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ nu (lastIdx n) := by
  by_contra hn
  exact h0 (weight_support_sum_eq_zero E (fun mu => mu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ mu (lastIdx n)) hx
    (top_le_end_bounded_weights hI Submodule.mem_top) hn)

theorem irreducible_highest_weight_line [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) {x : V} (hx : x ∈ weightSp E lam) : ∃ c : KK O, x = c • v := by
  have hx2 := top_le_line_sup_higher_weights hI (Submodule.mem_top (x := x))
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx2
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hv : v ∈ weightSp E lam := hI.2.2.1.2.1
  have hzw : z ∈ weightSp E lam := by
    have e : z = (c • v + z) - c • v := by abel
    rw [e]
    exact Submodule.sub_mem _ hx (Submodule.smul_mem _ c hv)
  have hz0 : z = 0 := weight_support_sum_eq_zero E (fun nu => weightHeightAscending lam < weightHeightAscending nu) hzw hz (lt_irrefl _)
  exact ⟨c, by rw [hz0, add_zero]⟩

theorem highest_line_isCompl_other_weights [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) : IsCompl (Submodule.span (KK O) {v}) (otherWts E lam) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx2
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact weight_support_sum_eq_zero E (fun mu => mu ∈ {mu | mu ≠ lam}) (Submodule.smul_mem _ c hI.2.2.1.2.1) hx2
      (fun h => h rfl)
  · rw [codisjoint_iff, eq_top_iff, ← hI.1.2.2, iSup_le_iff]
    intro mu x hx
    by_cases h : mu = lam
    · subst h
      obtain ⟨c, rfl⟩ := irreducible_highest_weight_line hI hx
      exact Submodule.mem_sup_left (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v))
    · apply Submodule.mem_sup_right
      show x ∈ ⨆ mu ∈ {mu | mu ≠ lam}, weightSp E mu
      exact Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem h hx)

theorem exists_highest_coordinate_functional [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) : ∃ xi : V →ₗ[KK O] KK O, xi v = 1 ∧ (∀ w ∈ otherWts E lam, xi w = 0) ∧
      ∀ x, x - xi x • v ∈ otherWts E lam := by
  have hc := highest_line_isCompl_other_weights hI
  have hv0 : v ≠ 0 := hI.2.2.1.1
  let P := Submodule.linearProjOfIsCompl _ _ hc
  let e := LinearEquiv.toSpanNonzeroSingleton (KK O) V v hv0
  refine ⟨e.symm.toLinearMap ∘ₗ P, ?_, ?_, ?_⟩
  · have h1 : P v = ⟨v, Submodule.mem_span_singleton_self v⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hc ⟨v, Submodule.mem_span_singleton_self v⟩
    show e.symm (P v) = 1
    rw [h1, LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  · intro w hw
    have h2 : P w = 0 := Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩
    show e.symm (P w) = 0
    rw [h2, map_zero]
  · intro x
    have h8 : ∀ s : KK O, ((e s : Submodule.span (KK O) {v}) : V) = s • v := fun s => by
      first
        | rfl
        | simp [e, LinearEquiv.toSpanNonzeroSingleton_apply]
    have h3 : (e.symm (P x)) • v = (P x : V) := by
      rw [← h8, LinearEquiv.apply_symm_apply]
    show x - (e.symm (P x)) • v ∈ otherWts E lam
    rw [h3]
    have hPP : P (P x : V) = P x := Submodule.linearProjOfIsCompl_apply_left hc (P x)
    have h5 : P (x - (P x : V)) = 0 := by
      rw [map_sub, hPP, sub_self]
    have h6 := LinearMap.mem_ker.mpr h5
    have h7 := Submodule.linearProjOfIsCompl_ker hc
    rw [SetLike.ext_iff] at h7
    exact (h7 _).mp h6

end hw

end Formalism.MainNotions.G.GLWeightTheory
