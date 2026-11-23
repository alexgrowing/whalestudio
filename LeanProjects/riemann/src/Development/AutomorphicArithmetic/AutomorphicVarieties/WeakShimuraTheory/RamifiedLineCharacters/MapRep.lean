import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.unrS :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → ∀ A : ValuationSubring Ω, Raw.Away D.S A → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1 := by
  intro Ω _ _ _ l _ c D T hG A hA g hg
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hine⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hG
  have hq : resQ T.F g ∈ Ine (F := ℚ) A := hg
  have hps : ∀ i, D.ps i (resQ T.F g) = 1 := fun i => hine i A hA hq
  have hd : diagRep D.ps (resQ T.F g) = 1 := by
    unfold UpperTheory.V.GradeZeroInterpolatingElement.diagRep
    simp [hps]
    funext i
    have h : D.ps i (AlgEquiv.restrictScalars ℚ g) = 1 := hps i
    rw [h]
    rfl
  unfold UpperTheory.V.GradeZeroInterpolatingElement.Raw.rbar UpperTheory.V.GradeZeroInterpolatingElement.Raw.r0
  ext i j
  rw [mapRep_apply, hd]
  simp [Matrix.one_apply]
