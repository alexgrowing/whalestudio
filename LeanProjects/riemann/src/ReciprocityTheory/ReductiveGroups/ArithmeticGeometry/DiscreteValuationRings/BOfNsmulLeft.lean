import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GsScalJFK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

section Basic

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem vge_of_zero {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))}
    (h : ∀ j, s.f j = 0) (r : ℚ) : VGe D F v k α s r := by
  unfold VGe
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun j => ?_⟩
  rw [h j, Fin.sum_univ_zero]

end Basic

theorem n4 : ValuationBoundAtZero := by
  intro V _ _ _ ϖ hϖ D Q _ F _ _ v hv m _ R' β s hsupp hnu w hw q hq
  classical
  obtain ⟨x, hx, hsum⟩ := hw
  have hxq : ∀ α, ((q : ℚ) : WithTop ℚ) ≤ v (x α) := by
    intro α
    by_cases h : ∃ z, α = β + R' • z
    · obtain ⟨z, rfl⟩ := h
      have h1 := GC.valuation_ge_at_zero hϖ hv (hnu (β + R' • z)) (hx _)
      refine le_trans (WithTop.coe_le_coe.2 ?_) h1
      rw [zero_add]; exact hq z
    · push Not at h
      exact GC.valuation_ge_at_zero hϖ hv (vge_of_zero (v := v) (hsupp α h) q) (hx α)
  obtain ⟨S, hS⟩ := hsum q
  have h1 := hS S le_rfl
  have h2 : ((q : ℚ) : WithTop ℚ) ≤ v (∑ α ∈ S, x α) := AddValuation.map_le_sum v fun α _ => hxq α
  have h3 := AddValuation.map_le_add v h1 h2
  rwa [sub_add_cancel] at h3

section Q

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ}

theorem bOf_zero_left (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (b : D.toPre.X) : bOf D.toPre Q 0 b = 0 := by
  simp only [bOf, zero_add, QForm.Q_zero hϖ D hQ]; ring

theorem bOf_nsmul_left (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (n : ℕ) (a b : D.toPre.X) :
    bOf D.toPre Q (n • a) b = n * bOf D.toPre Q a b := by
  induction n with
  | zero => simp [bOf_zero_left hϖ hQ]
  | succ n ih => rw [succ_nsmul, QForm.bOf_add_left hϖ D hQ, ih]; push_cast; ring

theorem Q_nsmul (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (n : ℕ) (a : D.toPre.X) : Q (n • a) = n ^ 2 * Q a := by
  induction n with
  | zero => simp [QForm.Q_zero hϖ D hQ]
  | succ n ih =>
    have h2 := QForm.two_Q_eq hϖ D hQ a
    have hb := bOf_nsmul_left hϖ hQ n a a
    have e : Q (n • a + a) = Q (n • a) + Q a + bOf D.toPre Q (n • a) a := by simp only [bOf]; ring
    rw [succ_nsmul, e, ih, hb, ← h2]; push_cast; ring

theorem q_shift (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (α m : D.toPre.X) (k : ℕ) :
    Q (α + k • m) = Q α + k * (k * Q m + bOf D.toPre Q m α) := by
  have e1 : Q (α + k • m) = Q α + Q (k • m) + bOf D.toPre Q α (k • m) := by simp only [bOf]; ring
  rw [e1, QForm.bOf_comm D α (k • m), bOf_nsmul_left hϖ hQ, Q_nsmul hϖ hQ]; ring

end Q

theorem n1a : ValuationMinRepresentatives := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ v hv k hk S hS s r
  refine ⟨fun h α _ => h α, fun h χ => ?_⟩
  obtain ⟨α, hα, m0, rfl⟩ := hS χ
  have H := SectionScalarValuation.fe_move hϖ hQ hv k m0 α s (h α hα)
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have e : r + (Q α : ℚ) / k + ((k * Q m0 + bOf D.toPre Q m0 α : ℤ) : ℚ) = r + (Q (α + k • m0) : ℚ) / k := by
    rw [q_shift hϖ hQ α m0 k]; push_cast; field_simp; ring
  rwa [e] at H

theorem exists_val_eq {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {r : ℚ} (hr : 0 < r) : ∃ ζ : F, ζ ≠ 0 ∧ v ζ = ((r : ℚ) : WithTop ℚ) := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ ^ r.num)) r.den_pos
  have hv1 : v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ ^ r.num)) =
      ((r.num : ℚ) : WithTop ℚ) := hv _ _ ⟨1, by simp⟩
  have hpow : v (ζ ^ r.den) = r.den • v ζ := AddValuation.map_pow v ζ r.den
  rw [hζ, hv1] at hpow
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero r.den_nz
  have hne : v ζ ≠ ⊤ := by
    intro h
    rw [h, hk, succ_nsmul, WithTop.add_top] at hpow
    exact WithTop.coe_ne_top hpow
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hx, ← WithTop.coe_nsmul, WithTop.coe_eq_coe, nsmul_eq_mul] at hpow
  have hq : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  have hxr : x = r := by
    have h2 : x = (r.num : ℚ) / (r.den : ℚ) := eq_div_of_mul_eq hq (by rw [mul_comm]; exact hpow.symm)
    rw [h2, Rat.num_div_den]
  exact ⟨ζ, fun h0 => hne (by rw [h0, AddValuation.map_zero]), by rw [← hx, hxr]⟩

theorem n1c : PositiveValuationMaximalIdeal := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k hk s hs0
  constructor
  · rintro ⟨r, hr, hs⟩
    obtain ⟨ζ, hζ0, hvζ⟩ := exists_val_eq hv hr
    refine ⟨ζ, ζ⁻¹ • s, by rw [hvζ]; exact_mod_cast hr, ?_,
      (isSmul_iff ζ (ζ⁻¹ • s) s).2 (by rw [smul_smul, mul_inv_cancel₀ hζ0, one_smul])⟩
    have h := NuGe.smul Q (q := -r) (by rw [AddValuation.map_inv, hvζ]; rfl) ((isSmul_iff _ _ _).2 rfl) hs
    rwa [add_neg_cancel] at h
  · rintro ⟨ζ, s', hvζ, hs', hsm⟩
    obtain ⟨q, hq, hqle⟩ : ∃ q : ℚ, 0 < q ∧ ((q : ℚ) : WithTop ℚ) ≤ v ζ := by
      cases h : v ζ with
      | top => exact ⟨1, one_pos, le_top⟩
      | coe y => rw [h] at hvζ; exact ⟨y, by exact_mod_cast hvζ, le_rfl⟩
    exact ⟨0 + q, by linarith, NuGe.smul Q hqle hsm hs'⟩

end ReciprocityTheory.ChartRestriction.G.DVR
