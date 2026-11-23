import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.BarFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem chi_rev {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (pr : Bool) (i : Fin 4) : chi D pr i * chi D pr i.rev = D.th := by
  cases pr <;> fin_cases i
  · exact mul_one _
  · exact mul_comm _ _
  · rfl
  · exact one_mul _
  · rfl
  · exact one_mul _
  · exact mul_one _
  · exact mul_comm _ _

theorem UpperTheory.V.Ws.Lk.cbFacts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (X : OCh T c' h), D.Good → (∀ i, IsOpen ((X.cb i).ker : Set (G T.L Ω))) ∧ (∀ i A, Raw.Away D.S A → Ine (F := T.L) A ≤ (X.cb i).ker) ∧ ∀ σ ∉ T.K.fixingSubgroup, ∀ g g' : G T.L Ω, resQ T.L g' = σ * resQ T.L g * σ⁻¹ → ∀ i : Fin 4, (X.cb i g' * X.cb i.rev g : ResidueField c'.O) * residue c'.O (chiO T.L Ω l c'.O g) ^ 3 = 1 := by
  intro Ω _ _ _ l _ c D T c' h X hD
  obtain ⟨hop, -, hun⟩ := Lk.barFacts hD
  refine ⟨fun i => ?_, fun i A hA g hg => ?_, fun σ hσ g g' hgg i => ?_⟩
  · have hq : Continuous (resQ T.L) := UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.L Ω
    haveI := (P1.coefRes c).2.2.1 c' h
    have h1 : IsOpen {g : G T.L Ω | Ideal.Quotient.mk (maximalIdeal c'.O ^ 1) (X.κ g : c'.O) = 1} :=
      (X.κ_cont 1).isOpen_fiber 1
    have h2 := (hop (lab T.pr i)).preimage hq
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((h1.inter h2).mem_nhds ⟨?_, ?_⟩) ?_)
    · show Ideal.Quotient.mk _ (X.κ 1 : c'.O) = 1
      rw [map_one, Units.val_one, map_one]
    · show residue c.O (D.ps (lab T.pr i) (resQ T.L 1) : c.O) = 1
      rw [map_one, map_one, Units.val_one, map_one]
    · rintro g ⟨a, b⟩
      have a1 : (X.κ g : c'.O) - 1 ∈ maximalIdeal c'.O ^ 1 := Ideal.Quotient.eq.1 (a.trans (map_one _).symm)
      rw [pow_one] at a1
      have a2 : residue c'.O (X.κ g : c'.O) = residue c'.O 1 := Ideal.Quotient.eq.2 a1
      have b1 : residue c.O (chi D T.pr i (resQ T.L g) : c.O) = 1 := b
      have b2 : residue c'.O (inc h (chi D T.pr i (resQ T.L g) : c.O)) = 1 := by
        rw [← ResidueField.map_residue, b1, map_one]
      refine Units.ext ?_
      rw [OCh.cb_val, map_mul, a2, b2, map_one, one_mul, Units.val_one]
  · have a : X.κ g = 1 := X.unr A hA hg
    have b : chi D T.pr i (resQ T.L g) = 1 := (hun A hA (resQ T.L g) ⟨hg.1, hg.2⟩).1 _
    refine Units.ext ?_
    rw [OCh.cb_val, a, b, Units.val_one, Units.val_one, map_one, one_mul, map_one, Units.val_one]
  · have a := (X.conj σ hσ g g' hgg).1
    have b : chi D T.pr i (resQ T.L g') = chi D T.pr i (resQ T.L g) := by
      rw [hgg, map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
    have e : D.th (resQ T.L g) = chi D T.pr i (resQ T.L g) * chi D T.pr i.rev (resQ T.L g) :=
      (DFunLike.congr_fun (chi_rev D T.pr i) _).symm
    rw [e, Units.val_mul, map_mul] at a
    rw [OCh.cb_val, OCh.cb_val, b, ← map_pow, ← map_mul, ← map_mul, ← map_one (residue c'.O), ← a]
    congr 1
    ring
