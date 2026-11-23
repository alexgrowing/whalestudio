import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ThickFrames

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Z.Kato.Joint

theorem htLaw_congr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {c : Coef l}
    {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} {j : Ω →+* Qbar l} {m₀ c₀ : ℕ}
    {R R' : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l} (h : HTLawCsOfCoef A c Z j m₀ c₀ R)
    (hR : ∀ m, 1 ≤ m → ∀ ψ z, R m ψ z = R' m ψ z) : HTLawCsOfCoef A c Z j (max m₀ 1) c₀ R' := by
  obtain ⟨ζ, hζ, hm⟩ := h
  refine ⟨ζ, hζ, fun m hm1 => ?_⟩
  obtain ⟨ι, x, P, o, hP, hψ⟩ := hm m (le_trans (le_max_left _ _) hm1)
  refine ⟨ι, x, P, o, hP, fun ψ hprim => ?_⟩
  rw [← hR m (le_trans (le_max_right _ _) hm1)]
  exact hψ ψ hprim

end UpperTheory.V.Z.Kato.Joint

end
