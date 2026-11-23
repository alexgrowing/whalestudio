import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G E Ω →* (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)).comp
        (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cyc_cont :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycBar F Ω l) : UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G F Ω → (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous
      (((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)).comp PadicInt.Coe.ringHom :
        ℤ_[l] →* UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l) : ℤ_[l] → UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
