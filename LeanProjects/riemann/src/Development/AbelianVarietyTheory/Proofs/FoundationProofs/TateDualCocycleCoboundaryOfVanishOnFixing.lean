import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKerRepCyclotomicNeOneNormalFormStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem h1dual_of_vanish_fix : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep (dual1 W)),
    (∀ g ∈ N0g W, z g = 0) → z ∈ ReciprocityTheory.Gal.B1 (Loc.colRep (dual1 W)) := by
  intro l _ Ω _ _ _ e S A W hW z hz hN
  obtain ⟨a, haK, hae⟩ := GlobalTheory.T.exists_ker_rep_cyclotomic_ne_one_normalForm l Ω e S A W hW
  have hWa : W a = 1 := haK
  have hdual : ∀ v : Fin 2 → Qbar l, Loc.colRep (dual1 W) a v = eps l a • v := by
    intro v
    show Matrix.toLin' ((dual1 W a : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) v = _
    rw [dual1, UpperTheory.V.Af.tw_val, hWa]
    simp [dt, hWa, eps, Matrix.toLin'_apply]
  have hcomm : ∀ g, z (a * g) = z (g * a) := by
    intro g
    have hn : (g * a)⁻¹ * (a * g) ∈ N0g W := by
      refine ⟨?_, ?_⟩
      · show cycBar ℚ Ω l ((g * a)⁻¹ * (a * g)) = 1
        simp [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc]
      · show W ((g * a)⁻¹ * (a * g)) = 1
        simp [map_mul, map_inv, hWa]
    have h1 : a * g = (g * a) * ((g * a)⁻¹ * (a * g)) := by group
    rw [h1, hz.2, hN _ hn, map_zero, add_zero]
  have hne : eps l a - 1 ≠ 0 := sub_ne_zero.mpr hae
  rw [mem_coboundaries1]
  refine ⟨(eps l a - 1)⁻¹ • z a, fun g => ?_⟩
  have key := hcomm g
  rw [hz.2, hz.2, hdual] at key

  have : (eps l a - 1) • z g = Loc.colRep (dual1 W) g (z a) - z a := by
    rw [sub_smul, one_smul]; rw [← sub_eq_zero] at key ⊢; rw [← key]; abel
  rw [map_smul, ← smul_sub, ← this, smul_smul, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.Ord2
