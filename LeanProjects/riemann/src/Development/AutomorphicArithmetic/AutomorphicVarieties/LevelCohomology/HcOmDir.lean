import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

theorem UpperTheory.V.X.omDir :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ ω : DirichletCharacter c.O l, ω ^ (l - 1) = 1 ∧ IsOmT c (Chr.dirG ℚ Ω ω) := by
  intro Ω _ _ _ l hl c
  obtain ⟨⟨w, hw, -⟩, h⟩ := omT Ω l c
  have hk := (h w hw).2.1
  have hs : Function.Surjective (Chr.cls ℚ Ω l) := (Chr.clsOnto Ω l).1
  let f : (ZMod l)ˣ →* c.Oˣ := (Chr.cls ℚ Ω l).liftOfSurjective hs ⟨w, hk.ge⟩
  have hf : f.comp (Chr.cls ℚ Ω l) = w := MonoidHom.ext fun σ => MonoidHom.liftOfRightInverse_comp_apply _ _
    (Function.rightInverse_surjInv hs) ⟨w, hk.ge⟩ σ
  refine ⟨MulChar.ofUnitHom f, ?_, ?_⟩
  · rw [← ZMod.card_units l]
    exact MulChar.pow_card_eq_one _
  · have e : Chr.dirG ℚ Ω (MulChar.ofUnitHom f : DirichletCharacter c.O l) = w := by
      rw [← hf, Chr.dirG]
      simp
    rw [e]
    exact hw
