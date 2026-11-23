import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.KrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical Pointwise

theorem UpperTheory.V.Ws.str_residue_le_cocycles_vanishing_on_inertia_kernel :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (T : Tower D) (w : ℤ × ℤ), (T.fr ∅).Str (residue c.O) w ≤ cocOff (charRep (T.rbU w)) (ineOff T.F Ω 1 ∩ T.Kr) := by
  intro Ω _ _ _ l _ c D hG T w z hz
  rw [Fr.Str, Submodule.mem_inf] at hz
  obtain ⟨⟨hlc, hcoc, hN, -⟩, n, hn⟩ := hz
  have hK := residualKernel_properties D hG T
  refine ⟨hlc, ?_, ?_⟩
  · intro g h
    rw [hcoc]
    simp [charRep, Tower.rbU]
  · rintro g ⟨⟨A, -, hgA⟩, hgK⟩
    have hrb : D.rbar (resQ T.F g) = 1 := hK.2.2.2.2.1 g hgK
    have hrt : residue c.O ((T.fr ∅).rt w g : c.O) = 1 := by
      have := congrArg Units.val (hK.2.2.2.2.2.1 w g hrb)
      simpa [Tower.rbU] using this
    by_cases hA : A.valuation (l : Ω) < 1
    · obtain ⟨v, ⟨σ, hσ⟩, -⟩ := T.cover A hA
      have hσA : σ⁻¹ • A = T.pl v := by
        ext x
        rw [ValuationSubring.mem_inv_pointwise_smul_iff]
        exact hσ x
      have hgA' : g • A = A := MulAction.mem_stabilizer_iff.1 hgA.1
      have hdec : σ⁻¹ * g * σ ∈ (T.fr ∅).Gv v := by
        show (σ⁻¹ * g * σ) • T.pl v = T.pl v
        rw [← hσA, mul_smul, mul_smul, smul_inv_smul, hgA']
      have hconj : (T.fr ∅).rt w (σ⁻¹ * g * σ) = (T.fr ∅).rt w g := by
        rw [map_mul, map_mul, map_inv, mul_comm ((T.fr ∅).rt w σ)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
      have hz0 : z (σ⁻¹ * g * σ) = 0 := by
        rw [hn v _ hdec, hconj, hrt, one_mul, sub_self]
      have hz1 : z 1 = 0 := by
        have := hcoc 1 1
        simpa using this
      have e1 := hcoc (σ⁻¹ * g) σ
      have e2 := hcoc σ⁻¹ g
      have e3 := hcoc σ⁻¹ σ
      rw [inv_mul_cancel, hz1] at e3
      have hmul : residue c.O ((T.fr ∅).rt w (σ⁻¹ * g) : c.O) = residue c.O ((T.fr ∅).rt w σ⁻¹ : c.O) := by
        rw [map_mul, Units.val_mul, map_mul, hrt, mul_one]
      rw [hmul, e2, hz0] at e1
      have hu : IsUnit (residue c.O ((T.fr ∅).rt w σ⁻¹ : c.O)) := ((T.fr ∅).rt w σ⁻¹).isUnit.map _
      have key : residue c.O ((T.fr ∅).rt w σ⁻¹ : c.O) * z g = 0 := by
        linear_combination e3 - e1
      exact (mul_eq_zero.1 key).resolve_left hu.ne_zero
    · refine hN g ?_
      refine ⟨A, ?_, hgA, hrb⟩
      intro p hp
      rw [Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · exact hA
      · simp at hp
