import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Vanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GVanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.KapRam
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.kappaZero : UpperTheory.V.Z.Sym.Loc.KappaZero := by
  intro O K _ _ _ _ _ Δ τ L c d m h hno
  by_cases hτ : τ ∈ (algebraMap O K).range
  · have hodd : ¬ EvenVal O (2 + τ) := fun he => by
      have := (hsLaw O K Δ L).2.1 Δ (2 + τ) L.even he
      unfold hs at this
      split_ifs at this with h'
      · obtain ⟨a, b, e⟩ := h'
        exact hno ⟨⟨a, b⟩, by rw [← e, QuadraticAlgebra.norm_def]; ring⟩
      · norm_num at this
    refine ⟨(kapRam O K Δ τ L c d m h hτ hodd).2, fun j hj χ z hz => gOdd O K Δ τ L j χ z h.reg hj ?_⟩
    have hn : QuadraticAlgebra.norm (1 + ω : Etau K τ) = 2 + τ := by
      simp [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]; ring
    rwa [hz, hn]
  · have h1 : ∀ t : Kˣ, lcount O c d ((t : K) • m) = 0 := fun t => by
      by_contra h'
      exact hτ (vanish O K Δ τ L c d _ (datSmul K Δ τ c d m h t) h').1
    refine ⟨by simp [kapSum, h1], fun j hj χ z hz => ?_⟩
    by_contra h'
    exact hτ (gVanish O K Δ τ L j hj χ z (.inr hz) h')
