import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationSubringPullbackIntegralElementsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOverPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgebraicNumberCongrModPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgClosureAutomorphismRestrictingLocalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalAutFixingTowerParamOfStabilizesStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue

theorem isAlgZp_map_of_algebraic : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl] (j : Ω →+* Ωl) (x : Ω), IsAlgZp p (j x) := by
  intro Ω _ _ _ p _ Ωl _ _ j x
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have hz : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 hx
  obtain ⟨P, hP, hPx⟩ := hz
  refine ⟨P.map (Int.castRingHom ℤ_[p]), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hP
  · rw [Polynomial.map_map, Polynomial.aeval_def, Polynomial.eval₂_map]
    have e1 : (algebraMap (O0 p) Ωl).comp ((algebraMap ℤ_[p] (O0 p)).comp (Int.castRingHom ℤ_[p])) = j.comp (algebraMap ℤ Ω) := RingHom.ext_int _ _
    rw [e1, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hPx, map_zero]

theorem zt_prim_and_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (l n : ℕ), 0 < l → IsPrimitiveRoot (zt ε l n) (l ^ n) ∧ zt ε l (n + 1) ^ l = zt ε l n := by
  intro Ω _ _ _ ε l n hl
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hkey : ∀ m : ℕ, ε (zt ε l m) = Complex.exp (2 * Real.pi * Complex.I / ((l ^ m : ℕ) : ℂ)) := by
    intro m
    have hN : l ^ m ≠ 0 := pow_ne_zero _ hl.ne'
    have hw : Complex.exp (2 * Real.pi * Complex.I * (((1 / (l : ℚ) ^ m : ℚ)) : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I / ((l ^ m : ℕ) : ℂ)) := by
      congr 1; push_cast; ring
    haveI : NeZero ((l ^ m : ℕ) : Ω) := ⟨by exact_mod_cast hN⟩
    haveI : NeZero (l ^ m) := ⟨hN⟩
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hz' : IsPrimitiveRoot (ε z) (l ^ m) := hz.map_of_injective ε.injective
    have hp := Complex.isPrimitiveRoot_exp (l ^ m) hN
    obtain ⟨i, -, hi⟩ := hz'.eq_pow_of_pow_eq_one hp.pow_eq_one
    have hex : ∃ y, ε y = Complex.exp (2 * Real.pi * Complex.I * (((1 / (l : ℚ) ^ m : ℚ)) : ℂ)) :=
      ⟨z ^ i, by rw [map_pow, hi, hw]⟩
    show ε (Function.invFun ε _) = _
    rw [Function.invFun_eq hex, hw]
  refine ⟨?_, ?_⟩
  · rw [← IsPrimitiveRoot.map_iff_of_injective (f := ε) ε.injective, hkey]
    exact Complex.isPrimitiveRoot_exp _ (pow_ne_zero _ hl.ne')
  · apply ε.injective
    rw [map_pow, hkey, hkey, ← Complex.exp_nat_mul]
    congr 1
    have : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    push_cast
    field_simp
    ring

theorem exists_cusp_embedding : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ∃ (Ωl : Type) (_ : Field Ωl) (_ : Algebra (O0 p) Ωl), IsClo p Ωl ∧ ∃ (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl), IsCusp ε A T j := by
  intro Ω _ _ _ ε X _ p _ _ A hA
  let Ωl := AlgebraicClosure (FractionRing (O0 p))
  have hcl : IsClo p Ωl := GlobalTheory.K5.Basic.isClo_algebraicClosure p
  haveI : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hcl
  haveI : IsAlgClosed Ωl := hcl.clo
  let j0 : Ω →+* Ωl := (IsAlgClosed.lift : Ω →ₐ[ℚ] Ωl).toRingHom
  obtain ⟨B, hBp, hB⟩ := GlobalTheory.T.exists_valuationSubring_pullback_integral_elements p Ωl hcl j0
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_algEquiv_map_valuationSubring_over_prime p A B hA hBp
  let j : Ω →+* Ωl := j0.comp σ.toRingEquiv.toRingHom
  have hint : ∀ x, x ∈ A ↔ IsInt p (j x) := fun x => (hσ x).symm.trans (hB _)
  have hl : 0 < p := (Fact.out : p.Prime).pos
  let T0 := (GlobalTheory.K5.Basic.nonempty_tower hcl).some
  let T : GlobalTheory.K5.Tower p Ωl :=
    { ζ := fun n => j (zt ε p n), qq := T0.qq,
      prim := fun n => (zt_prim_and_pow ε p n hl).1.map_of_injective j.injective,
      ζpow := fun n => by simp only [← map_pow, (zt_prim_and_pow ε p n hl).2],
      q0 := T0.q0, qpow := T0.qpow }
  refine ⟨Ωl, inferInstance, inferInstance, hcl, T, j, ?_⟩
  exact { int := hint, alg := isAlgZp_map_of_algebraic p Ωl j, root := fun n => rfl,
          dense := GlobalTheory.T.exists_algebraicNumber_congr_mod_prime_pow p A Ωl hcl j hint, down := GlobalTheory.T.exists_algClosure_automorphism_restricting_local p A Ωl hcl j hint,
          up := fun n s hs => GlobalTheory.T.exists_local_aut_fixing_tower_param_of_stabilizes p A Ωl hcl j hint T n s hs }

end GlobalTheory.Glue
