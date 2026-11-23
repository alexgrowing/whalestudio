import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChgPfTP

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.SmallDeriv

variable {O : Type} [CommRing O] {d : ℕ}

def yZero : Fin d ⊕ Fin d → MvPowerSeries (Fin d) O := Sum.elim (fun i => X i) (fun _ => 0)

theorem yZero_const : ∀ s, constantCoeff (yZero (O := O) (d := d) s) = 0 := by
  intro s; cases s <;> simp [yZero]

theorem hasSubst_yZero : HasSubst (yZero (O := O) (d := d)) :=
  hasSubst_of_constantCoeff_zero yZero_const

theorem constantCoeff_subst_of {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ O}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ O) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add, constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem constantCoeff_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ O) :
    constantCoeff (pderiv O i f) = coeff (Finsupp.single i 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]; simp

theorem subst_X_self {σ : Type} (f : MvPowerSeries σ O) : subst (fun i => (X i : MvPowerSeries σ O)) f = f := by
  rw [← map_algebraMap_eq_subst_X]
  simp [Algebra.algebraMap_self, map_id]

theorem pderiv_right_formalGroupLawCoboundaryOne (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (t : MvPowerSeries (Fin d) O) (j : Fin d) :
    pderiv O (Sum.inr j) (cob1 μ t) =
      (∑ s, subst μ (pderiv O s t) * pderiv O (Sum.inr j) (μ s)) - inR (pderiv O j t) := by
  classical
  have hl : ∀ s : Fin d, constantCoeff (X (Sum.inl s) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
    fun s => constantCoeff_X _
  have hr : ∀ s : Fin d, constantCoeff (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
    fun s => constantCoeff_X _
  unfold cob1 inL inR
  rw [map_sub, map_sub, ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst μ hμ,
    ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hl, ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hr]
  have e1 : ∑ s : Fin d, subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) (pderiv O s t) *
      pderiv O (Sum.inr j) (X (Sum.inl s)) = 0 :=
    Finset.sum_eq_zero fun s _ => by rw [pderiv_X_of_ne (by simp), mul_zero]
  have e2 : ∑ s : Fin d, subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) (pderiv O s t) *
      pderiv O (Sum.inr j) (X (Sum.inr s)) =
      subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) (pderiv O j t) := by
    rw [Finset.sum_eq_single j]
    · rw [pderiv_X_self, mul_one]
    · intro s _ hs; rw [pderiv_X_of_ne (by simpa using hs), mul_zero]
    · simp
  rw [e1, e2, sub_zero]

end GlobalTheory.Katz.SmallDeriv

namespace GlobalTheory.Katz.SmallDeriv

variable {O : Type} [CommRing O] {d : ℕ}

theorem yZero_subst (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : IsLaw μ) (g : MvPowerSeries (Fin d) O) :
    subst yZero (subst μ g) = g := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hμ.const) hasSubst_yZero]
  have : (fun s => subst (yZero (O := O) (d := d)) (μ s)) = fun i => X i := by
    have h := hμ.unit
    funext i
    have hi := congrFun h i
    simpa [op, at2, yZero] using hi
  rw [this, subst_X_self]

theorem yZero_inR (g : MvPowerSeries (Fin d) O) :
    subst yZero (inR g) = C (constantCoeff g) := by
  have hr : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
    hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _
  unfold inR
  rw [subst_comp_subst_apply hr hasSubst_yZero]
  have : (fun s => subst (yZero (O := O) (d := d)) (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) O)) = 0 := by
    funext s; rw [subst_X hasSubst_yZero]; rfl
  rw [this, subst_zero_eq_C_constantCoeff]
  simp [Algebra.algebraMap_self, map_id]

theorem linear_coeff_law (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : IsLaw μ) (s j : Fin d) :
    constantCoeff (pderiv O (Sum.inr j) (μ s)) = if s = j then 1 else 0 := by
  classical

  have hx : constantCoeff (pderiv O (Sum.inl j) (μ s)) = if s = j then 1 else 0 := by
    have h := congrFun hμ.unit s
    change subst yZero (μ s) = X s at h
    have h2 := congrArg (fun f => constantCoeff (pderiv O j f)) h
    rw [ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ yZero_const, map_sum] at h2
    simp only [map_mul, constantCoeff_subst_of yZero_const] at h2
    simp only [Fintype.sum_sum_type, yZero,
      Sum.elim_inl, Sum.elim_inr, map_zero, mul_zero, Finset.sum_const_zero, add_zero, pderiv_X, map_sum, map_mul] at h2
    simp only [Pi.single_apply, apply_ite, map_one, map_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    split_ifs at h2 ⊢ <;> exact h2
  have hsw : ∀ k : Fin d ⊕ Fin d, constantCoeff ((Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O))
      (fun i => X (Sum.inl i))) k) = 0 := by
    intro k; cases k <;> simp
  have h := hμ.comm s
  unfold swap at2 at h
  have h2 := congrArg (fun f => constantCoeff (pderiv O (Sum.inr j) f)) h
  rw [ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hsw, map_sum] at h2
  simp only [map_mul, constantCoeff_subst_of hsw] at h2
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, pderiv_X, Pi.single_apply, Sum.inr.injEq,
    reduceCtorEq, if_false, map_zero, mul_zero, Finset.sum_const_zero, add_zero, apply_ite, map_one, mul_ite,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  rw [← h2, hx]

end GlobalTheory.Katz.SmallDeriv

namespace GlobalTheory.Katz.SmallDeriv

theorem isLocalRing_of_integers {C : Type} [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] (hv : v.Integers O) : IsLocalRing O := by
  haveI : Nontrivial O := (algebraMap O C).domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_contra h
  push_neg at h
  have h1 : v (algebraMap O C a) < 1 :=
    lt_of_le_of_ne (hv.map_le_one a) (fun e => h.1 (hv.isUnit_of_one' e))
  have h2 : v (algebraMap O C (1 - a)) < 1 :=
    lt_of_le_of_ne (hv.map_le_one _) (fun e => h.2 (hv.isUnit_of_one' e))
  have h3 := v.map_add (algebraMap O C a) (algebraMap O C (1 - a))
  have h4 : algebraMap O C a + algebraMap O C (1 - a) = 1 := by rw [← map_add]; simp
  rw [h4, v.map_one] at h3
  exact lt_irrefl _ (lt_of_le_of_lt h3 (max_lt h1 h2))

end GlobalTheory.Katz.SmallDeriv

open GlobalTheory.Katz.SmallDeriv in

theorem GlobalTheory.Katz.not_isUnit_coeff_of_coboundary_small : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ t : MvPowerSeries (Fin d) O, (∀ i, ¬IsUnit (lin t i)) → (∀ α : Fin d ⊕ Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α (cob1 μ t))) → ∀ α : Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α t) := by
  intro p hpr C _ _ _ v O _ _ hpO _ _ hv d μ hμ t hlin hcob α ⟨i, hi⟩
  classical
  haveI : IsLocalRing O := isLocalRing_of_integers v O hv
  let π := IsLocalRing.residue O
  have hmem : ∀ a : O, π a = 0 ↔ ¬IsUnit a := by
    intro a
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hp0 : (p : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast π, hmem]; exact hpO.out

  have hG : ∀ j, map π (pderiv O (Sum.inr j) (cob1 μ t)) = 0 := by
    intro j; ext n
    rw [coeff_map, coeff_pderiv, map_mul, coeff_zero]
    by_cases hn : p ∣ n (Sum.inr j) + 1
    · obtain ⟨m, hm⟩ := hn
      have e : π ((n (Sum.inr j) : O) + 1) = 0 := by
        have : ((n (Sum.inr j) : O) + 1) = ((n (Sum.inr j) + 1 : ℕ) : O) := by push_cast; ring
        rw [this, hm, Nat.cast_mul, map_mul, map_natCast, hp0, zero_mul]
      rw [e, mul_zero]
    · have := hcob (n + Finsupp.single (Sum.inr j) 1) ⟨Sum.inr j, by simpa using hn⟩
      rw [(hmem _).2 this, zero_mul]
  let N : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) (IsLocalRing.ResidueField O)) :=
    Matrix.of fun s j => map π (subst yZero (pderiv O (Sum.inr j) (μ s)))
  let w : Fin d → MvPowerSeries (Fin d) (IsLocalRing.ResidueField O) := fun s => map π (pderiv O s t)
  have hvec : Matrix.vecMul w N = 0 := by
    funext j
    have e := congrArg (fun F => map π (subst yZero F)) (pderiv_right_formalGroupLawCoboundaryOne μ hμ.const t j)
    rw [map_subst hasSubst_yZero, hG j, ← coe_substAlgHom (hasSubst_yZero.map π), map_zero,
      ← coe_substAlgHom hasSubst_yZero, map_sub, map_sum] at e
    simp only [map_mul, coe_substAlgHom, yZero_subst μ hμ, yZero_inR, constantCoeff_pderiv, map_sub, map_sum,
      map_C] at e
    have hl : π (coeff (Finsupp.single j 1) t) = 0 := (hmem _).2 (hlin j)
    rw [hl, map_zero, sub_zero] at e
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, N, w, Matrix.of_apply]
    exact e.symm
  have hN0 : (constantCoeff : MvPowerSeries (Fin d) (IsLocalRing.ResidueField O) →+* _).mapMatrix N = 1 := by
    ext s j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, N, Matrix.of_apply, constantCoeff_map,
      constantCoeff_subst_of yZero_const, linear_coeff_law μ hμ, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit N.det := by
    rw [isUnit_iff_constantCoeff, RingHom.map_det, hN0, Matrix.det_one]
    exact isUnit_one
  have hw : w i = 0 := by
    have h1 := congrArg (fun u => Matrix.vecMul u N.adjugate) hvec
    simp only [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.zero_vecMul] at h1
    have h2 := congrFun h1 i
    simp only [Matrix.vecMul, dotProduct, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] at h2
    exact (hdet.mul_right_eq_zero).1 (by rw [mul_comm]; exact h2)
  have hαi : 1 ≤ α i := Nat.pos_of_ne_zero (fun h => hi (h ▸ dvd_zero p))
  have hsub : α - Finsupp.single i 1 + Finsupp.single i 1 = α :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hαi)
  have hc := congrArg (coeff (α - Finsupp.single i 1)) hw
  simp only [w] at hc
  rw [coeff_map, coeff_pderiv, coeff_zero, hsub, map_mul] at hc
  have hcast : (((α - Finsupp.single i 1 : Fin d →₀ ℕ) i : ℕ) : O) + 1 = ((α i : ℕ) : O) := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hαi]
  rw [hcast, map_natCast] at hc
  have hne : ((α i : ℕ) : IsLocalRing.ResidueField O) ≠ 0 := by
    obtain ⟨u, u', h⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hpr.out).2 hi)
    have h' := congrArg (Int.cast : ℤ → IsLocalRing.ResidueField O) h
    push_cast at h'
    rw [hp0] at h'
    intro h0; rw [h0] at h'; simp at h'
  exact (hmem _).1 ((mul_eq_zero.1 hc).resolve_right hne)
