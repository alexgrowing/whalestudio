import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.ConjCusp
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

noncomputable section

namespace UpperTheory.V.Af.Gk

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

private def conjRep (π : TR.CuspSub E a) : TR.CuspSub E a where
  V := π.V.map (conjFn E a).toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact conjCusp E a φ (π.cusp φ hφ)
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable o φ hφ, (act_conjFn o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := conjFn E a)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap (conjFn E a).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (conjFn E a).injective h2]) fun o φ hφ => by
      have h1 := hs o _ hφ
      change act _ (conjFn E a φ) ∈ W at h1
      rw [act_conjFn] at h1
      exact h1
    have e := Submodule.map_comap_eq_of_surjective (f := (conjFn E a).toLinearMap) (conjFn E a).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

end UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.conjSub :
    UpperTheory.V.Af.Gk.ConjSub := by
  intro F _ _ _ a π
  exact ⟨conjRep π, (conjFn F a).submoduleMap π.V, fun o φ => Subtype.ext (act_conjFn o φ.1).symm⟩
