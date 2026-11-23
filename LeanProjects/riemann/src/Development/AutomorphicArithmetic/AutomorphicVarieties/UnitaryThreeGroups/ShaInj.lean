import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ShaInjGen

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

abbrev UpperTheory.V.U3.CocVal {O : Type} [CommRing O] (a : O) : Type := Matrix (Fin 3) (Fin 3) (O ⧸ Ideal.span {a})

private theorem shaInj_loc {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) :
    D.ι.range ∈ shaFam ℚ Ω (l * N) ∧ ∃ s', IsUnit ((D.Ψ (D.ι s') : c.O) ^ 2 - 1) := by
  obtain ⟨A, hA, hD, hIn, -⟩ := dat_loc D
  obtain ⟨s, hs, hsu⟩ := ((dat_facts D).2.2.2.2.2.2.2.2.2.2 A hA).2
  rw [← hIn] at hs
  obtain ⟨s', -, hs'⟩ := Subgroup.mem_map.1 hs
  refine ⟨?_, s', by rw [hs']; exact hsu⟩
  rw [hD]
  exact Chr.shaFam_mono (dvd_mul_right l N) (Or.inl ⟨A, hA, rfl⟩)

private theorem shaInj_away {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) :
    ∀ g ∈ D.Kill, ∃ D' ∈ shaFam ℚ Ω (l * N), g ∈ D' := by
  rintro g ⟨A', -, hg', -⟩
  exact ⟨_, Or.inr ⟨A', rfl⟩, hg'⟩

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.U3.sha_inj :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (g₁ : G ℚ Ω), D.Marked g₁ → ∀ b : c.O, b ≠ 0 → ∃ a : c.O, a ≠ 0 ∧
      ∃ γ : Submodule.torsionBy c.O (ShaU (Chr.rho l e (Chr.dirG ℚ Ω ψ)) (l * N) ⊤) b →+ (G ℚ Ω → CocVal a),
        Function.Injective γ ∧ ∀ x, γ x ∈ shaCoc D.η D.Ψ D.Kill D.ι D.cc g₁ a := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D g₁ hM b hb
  exact ⟨b, hb, sha_inj_gen (O := c.O) e (l * N) (Chr.dirG ℚ Ω ψ) D.η D.Kill D.ι D.cc g₁ b hb hM
    (dat_facts D).2.2.2.2.2.2.1 (dat_facts D).2.2.2.2.2.1 (shaInj_away D) (shaInj_loc D).1 _
    (shaInj_loc D).2.choose_spec⟩
