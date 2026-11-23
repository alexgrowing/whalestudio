import Development.DiscreteGroups.GlobalIrreducibility.KUSStable

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem univ_supp (c : Fin n → k) : ∀ r ∉ (Finset.univ : Finset (Fin n)), c r = 0 :=
  fun r hr => absurd (Finset.mem_univ r) hr

theorem conj_S (j : ℕ) (hj : j < n) (x : GL (Fin n) k) (hx : TopLeft j (x : Matrix (Fin n) (Fin n) k))
    (hy : TopLeft j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (ξ : Fin n → k) {w : V}
    (hw : w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ (rowMul j ξ ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) :
    π x⁻¹ w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add]
  refine Submodule.add_mem_sup (KN_stable π ψ j _ hy.good (by rw [inv_inv]; exact hx.good) ha) ?_
  refine (Submodule.span_le.2 ?_ : KUS π ψ j Finset.univ (rowMul j ξ ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    ≤ (KUS π ψ j Finset.univ ξ).comap (π x⁻¹)) hb
  rintro _ ⟨c, -, v, rfl⟩
  refine Submodule.subset_span ⟨colMul j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c, univ_supp _, π x⁻¹ v, ?_⟩
  rw [map_sub, map_smul, conj_apply, inv_inv, conj_colU j hj x hx hy, dotj_colMul]

theorem ne_top_of_conj (j : ℕ) (hj : j < n) (x : GL (Fin n) k) (hx : TopLeft j (x : Matrix (Fin n) (Fin n) k))
    (hy : TopLeft j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (ξ : Fin n → k)
    (h : KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ ≠ ⊤) :
    KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ (rowMul j ξ ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) ≠ ⊤ := by
  intro htop
  apply h
  refine eq_top_iff.2 fun v _ => ?_
  have := conj_S π ψ j hj x hx hy ξ (w := π x v) (by rw [htop]; exact Submodule.mem_top)
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this

theorem KN_le (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) (η : Fin n → k) (hη : ∀ c, dotj j η c = c (i0 j hj hj1)) :
    KN π ψ j ≤ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ η := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, v, rfl⟩
  obtain ⟨h1, h2⟩ := peel_N j hj hj1 hg
  set c : Fin n → k := fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩ with hc
  set n' := colU j (-c) * g with hn'
  have hg' : g = colU j c * n' := by rw [hn', ← mul_assoc, ← colU_add, add_neg_cancel, colU_zero, one_mul]
  have hch : chM ψ j g = chM ψ (j + 1) n' * ((ψ (c (i0 j hj hj1)) : Circle) : ℂ) := by
    rw [chM, chM, h2, AddChar.map_add_eq_mul, Circle.coe_mul]; rfl
  have e : π g v - chM ψ j g • v = π (colU j c) (π n' v - chM ψ (j + 1) n' • v) +
      chM ψ (j + 1) n' • (π (colU j c) v - ((ψ (dotj j η c) : Circle) : ℂ) • v) := by
    rw [hη, hch, map_sub, map_smul, smul_sub, smul_smul]
    conv_lhs => rw [hg', map_mul, Module.End.mul_apply]
    abel
  show _ ∈ _
  rw [e]
  refine Submodule.add_mem_sup (KN_stable π ψ j _ (good_colU j c) (good_colU_inv j c)
    (Submodule.subset_span ⟨n', h1, v, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, univ_supp c, v, rfl⟩))

theorem twKer_le (j : ℕ) (hj : j < n) (h : ∑ i, ![j, n - j] i = n) (ξ : Fin n → k) (hz : ∀ i : Fin n, i.val < j → ξ i = 0) :
    twKer π (unipRad k (stdBlocks ![j, n - j] h)) 1 ≤ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨g, hg⟩, v, rfl⟩
  obtain ⟨h1, h2⟩ := peel_rad j hj h hg
  set c : Fin n → k := fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩ with hc
  set n' := colU j (-c) * g with hn'
  have hg' : g = colU j c * n' := by rw [hn', ← mul_assoc, ← colU_add, add_neg_cancel, colU_zero, one_mul]
  have hch : chM ψ (j + 1) n' = 1 := by rw [chM, h2, AddChar.map_zero_eq_one, Circle.coe_one]
  have hd : dotj j ξ c = 0 := Finset.sum_eq_zero fun i _ => by
    by_cases hi : i.val < j
    · rw [if_pos hi, hz i hi, zero_mul]
    · rw [if_neg hi]
  have e : π g v - (((1 : ↥(unipRad k (stdBlocks ![j, n - j] h)) →* ℂˣ) ⟨g, hg⟩ : ℂˣ) : ℂ) • v =
      π (colU j c) (π n' v - chM ψ (j + 1) n' • v) + (π (colU j c) v - ((ψ (dotj j ξ c) : Circle) : ℂ) • v) := by
    rw [hch, hd, AddChar.map_zero_eq_one, Circle.coe_one, MonoidHom.one_apply, Units.val_one, one_smul,
      map_sub]
    conv_lhs => rw [hg', map_mul, Module.End.mul_apply]
    abel
  show _ ∈ _
  rw [e]
  exact Submodule.add_mem_sup (KN_stable π ψ j _ (good_colU j c) (good_colU_inv j c)
    (Submodule.subset_span ⟨n', h1, v, rfl⟩)) (Submodule.subset_span ⟨c, univ_supp c, v, rfl⟩)

end DiscreteGroups.sglob.LConvGenR
