import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

section

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem constBF_mul (ζ a : F) (W : (DegPre.BF D.toPre F).left.Opens) :
    DegPre.constBF D.toPre F (ζ * a) W =
      DegPre.constBF D.toPre F ζ W * DegPre.constBF D.toPre F a W := by
  simp only [DegPre.constBF, map_mul]

theorem VGe.mono {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {r r' : ℚ}
    (h : VGe D F v k α s r) (hr : r' ≤ r) : VGe D F v k α s r' := by
  obtain ⟨n, a, σ, σF, h1, h2, h3⟩ := h
  exact ⟨n, a, σ, σF, h1, fun i => le_trans (by exact_mod_cast hr) (h2 i), h3⟩

theorem VGe.add {k : ℕ} {α : D.toPre.X}
    {s s' s'' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {r : ℚ}
    (h : VGe D F v k α s r) (h' : VGe D F v k α s' r) (hadd : ∀ j, s''.f j = s.f j + s'.f j) :
    VGe D F v k α s'' r := by
  unfold VGe at h h' ⊢
  obtain ⟨n, a, σ, σF, hσ, ha, hs⟩ := h
  obtain ⟨m, b, τ, τF, hτ, hb, hs'⟩ := h'
  refine ⟨n + m, Fin.append a b, Fin.append σ τ, Fin.append σF τF, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]
      exact hσ i
    · simp only [Fin.append_right]
      exact hτ i
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]
      exact ha i
    · simp only [Fin.append_right]
      exact hb i
  · intro j
    rw [hadd j, hs j, hs' j, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem VGe.smul {k : ℕ} {α : D.toPre.X}
    {s s' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {r q : ℚ}
    {ζ : F} (h : VGe D F v k α s r) (hq : ((q : ℚ) : WithTop ℚ) ≤ v ζ)
    (hs : ∀ j, s'.f j = DegPre.constBF D.toPre F ζ _ * s.f j) : VGe D F v k α s' (r + q) := by
  obtain ⟨n, a, σ, σF, h1, h2, h3⟩ := h
  refine ⟨n, fun i => ζ * a i, σ, σF, h1, fun i => ?_, fun j => ?_⟩
  · rw [AddValuation.map_mul, WithTop.coe_add, add_comm (v ζ)]
    exact add_le_add (h2 i) hq
  · rw [hs, h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [constBF_mul]; exact (_root_.mul_assoc _ _ _).symm

variable (Q : D.toPre.X → ℤ)

theorem NuGe.mono {k : ℕ} {s : Fam D.toPre F k} {r r' : ℚ} (h : NuGe D Q F v k s r) (hr : r' ≤ r) :
    NuGe D Q F v k s r' :=
  fun χ => (h χ).mono (by linarith)

theorem NuGe.add {k : ℕ} {s s' s'' : Fam D.toPre F k} {r : ℚ} (hadd : FamIsAdd D F s s' s'')
    (h : NuGe D Q F v k s r) (h' : NuGe D Q F v k s' r) : NuGe D Q F v k s'' r :=
  fun χ => (h χ).add (h' χ) (hadd χ)

theorem NuGe.smul {k : ℕ} {s s' : Fam D.toPre F k} {r q : ℚ} {ζ : F}
    (hq : ((q : ℚ) : WithTop ℚ) ≤ v ζ) (hs : Fam.IsSmul D.toPre F ζ s s') (h : NuGe D Q F v k s r) :
    NuGe D Q F v k s' (r + q) := by
  intro χ
  have := (h χ).smul hq (hs χ)
  exact this.mono (by linarith)

end

theorem n1e : GermIntegrality := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ v k s hs χ
  have hQ0 : (0 : ℚ) ≤ Q χ := by
    by_cases hχ : χ = 0
    · subst hχ; rw [Q_zero hϖ D hQ]; simp
    · have := Q_pos hϖ D hQ hχ; exact_mod_cast (by omega : (0 : ℤ) ≤ Q χ)
  exact (hs χ).mono (by have : (0 : ℚ) ≤ (Q χ : ℚ) / k := div_nonneg hQ0 (Nat.cast_nonneg k); linarith)

end ReciprocityTheory.ChartRestriction.G.DVR
