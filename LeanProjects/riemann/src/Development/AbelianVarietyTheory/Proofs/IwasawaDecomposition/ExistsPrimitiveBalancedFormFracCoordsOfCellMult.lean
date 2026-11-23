import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

namespace CentreChoice

variable {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X]

theorem exists_isPrim_smul {x : balForms bar X} (hx : x ≠ 0) :
    ∃ (g : ℕ) (v : balForms bar X), 0 < g ∧ x = g • v ∧ IsPrim bar v := by
  classical
  obtain ⟨a, b, hab⟩ : ∃ a b, (x : LinearMap.BilinForm ℤ X) a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (Subtype.ext (LinearMap.ext₂ h))
  let S : Set ℕ := {g | 0 < g ∧ ∃ v : balForms bar X, x = g • v}
  have hS1 : 1 ∈ S := ⟨one_pos, x, (one_smul _ _).symm⟩
  have hbd : ∀ g ∈ S, g ≤ ((x : LinearMap.BilinForm ℤ X) a b).natAbs := by
    rintro g ⟨hg, v, hv⟩
    have e : (x : LinearMap.BilinForm ℤ X) a b = (g : ℤ) * (v : LinearMap.BilinForm ℤ X) a b := by
      rw [hv]
      simp
    rw [e] at hab ⊢
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.2 (right_ne_zero_of_mul hab))
  have hB : BddAbove S := ⟨_, hbd⟩
  obtain ⟨hg, v, hv⟩ := Nat.sSup_mem ⟨1, hS1⟩ hB
  refine ⟨sSup S, v, hg, hv, fun j v' hj => ?_⟩
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hx
    rw [hv, hj, zero_smul, smul_zero]
  have hmem : sSup S * j ∈ S := ⟨Nat.mul_pos hg (Nat.pos_of_ne_zero hj0), v', by rw [hv, hj, mul_smul]⟩
  have h1 : sSup S * j ≤ sSup S * 1 := by simpa using le_csSup hB hmem
  have h2 := Nat.le_of_mul_le_mul_left h1 hg
  omega

theorem exists_isPrim_frac : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (M : ℕ) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → 2 ≤ M →
  ∃ (v : LinearMap.BilinForm ℤ X) (hv : v ∈ balForms bar X), IsPrim bar (⟨v, hv⟩ : balForms bar X) ∧ (∀ y, 0 ≤ v y y) ∧
    ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i < 1) ∧ toReal v = ∑ i, t i • toReal (δ i) := by
  intro O _ bar φ M X _ _ _ m δ hδ h2
  classical
  obtain ⟨hc, -, -, hM⟩ := hδ
  let δ' : Fin m → balForms bar X := fun i => ⟨δ i, hc.mem i⟩
  let P := Submodule.span ℤ (Set.range δ')
  have hcard : 1 < Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ P)) := by
    have : Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ P)) = M := hM
    omega
  have hfin : Finite (Submodule.torsion ℤ (balForms bar X ⧸ P)) := Nat.finite_of_card_ne_zero (by omega)
  haveI := Finite.one_lt_card_iff_nontrivial.1 hcard
  obtain ⟨t, ht⟩ := exists_ne (0 : Submodule.torsion ℤ (balForms bar X ⧸ P))
  obtain ⟨⟨a, ha⟩, hat⟩ := (Submodule.mem_torsion_iff _).1 t.2
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective P t.1
  have hxP : x ∉ P := fun h => ht (Subtype.ext (by rw [← hx]; exact (Submodule.Quotient.mk_eq_zero P).2 h))
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have h1 : a • x ∈ P := (Submodule.Quotient.mk_eq_zero P).1 (by
    rw [Submodule.Quotient.mk_smul, ← Submodule.mkQ_apply, hx]; exact hat)
  have hk : 0 < a.natAbs := Int.natAbs_pos.2 ha0
  have hkx : (a.natAbs : ℤ) • x ∈ P := by
    rcases Int.natAbs_eq a with h | h
    · rwa [h] at h1
    · rw [h, neg_smul] at h1
      exact P.neg_mem_iff.1 h1
  obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hkx
  set k : ℕ := a.natAbs with hkdef
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  let x' : balForms bar X := x - ∑ i, (c i / k) • δ' i
  have hsP : ∑ i, (c i / k) • δ' i ∈ P :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hx'0 : x' ≠ 0 := fun h => hxP (by
    have : x = x' + ∑ i, (c i / k) • δ' i := by simp [x']
    rw [this, h, zero_add]; exact hsP)
  have hkx' : (k : ℤ) • x' = ∑ i, (c i % k) • δ' i := by
    simp only [x', smul_sub, Finset.smul_sum, smul_smul, ← hc']
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul]
    congr 1
    have := Int.mul_ediv_add_emod (c i) k
    linarith
  obtain ⟨g, v, hg, hxv, hprim⟩ := exists_isPrim_smul hx'0
  have hr0 : ∀ i, 0 ≤ c i % k := fun i => Int.emod_nonneg _ hkZ.ne'
  have hr1 : ∀ i, c i % k < k := fun i => Int.emod_lt_of_pos _ hkZ
  have key : ∀ a b, ((k : ℤ) * g) * (v : LinearMap.BilinForm ℤ X) a b = ∑ i, (c i % k) * δ i a b := by
    intro a b
    have e := congrArg (fun z : balForms bar X => (z : LinearMap.BilinForm ℤ X) a b) hkx'
    simp only [hxv] at e
    simpa [Submodule.coe_sum, LinearMap.sum_apply, δ', mul_assoc] using e
  have hkg : (0 : ℤ) < (k : ℤ) * g := mul_pos hkZ (by exact_mod_cast hg)
  refine ⟨v, v.2, hprim, fun y => ?_, fun i => ((c i % k : ℤ) : ℝ) / ((k : ℝ) * g), fun i => ⟨?_, ?_⟩, ?_⟩
  · have hs : 0 ≤ ∑ i, (c i % k) * δ i y y :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hr0 i) (hc.nonneg i y)
    rw [← key] at hs
    exact nonneg_of_mul_nonneg_right hs hkg
  · have : (0 : ℝ) < (k : ℝ) * g := by exact_mod_cast hkg
    exact div_nonneg (by exact_mod_cast hr0 i) this.le
  · have : (0 : ℝ) < (k : ℝ) * g := by exact_mod_cast hkg
    rw [div_lt_one this]
    have : c i % k < (k : ℤ) * g := lt_of_lt_of_le (hr1 i) (le_mul_of_one_le_right hkZ.le (by exact_mod_cast hg))
    exact_mod_cast this
  · have hpos : (0 : ℝ) < (k : ℝ) * g := by exact_mod_cast hkg
    refine LinearMap.ext₂ fun a b => ?_
    have e : ((k : ℝ) * g) * ((v : LinearMap.BilinForm ℤ X) a b : ℝ) = ∑ i, ((c i % k : ℤ) : ℝ) * (δ i a b : ℝ) := by
      exact_mod_cast key a b
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_right_inj' hpos.ne', e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp

end CentreChoice

end GlobalTheory.PolFan
