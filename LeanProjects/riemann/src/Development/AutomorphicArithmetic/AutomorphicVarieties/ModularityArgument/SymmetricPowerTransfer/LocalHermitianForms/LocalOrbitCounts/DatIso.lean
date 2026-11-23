import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.datIso : UpperTheory.V.Z.Sym.Loc.DatIso := by
  intro O K _ _ _ Δ τ c d m y
  constructor
  · unfold lcount
    letI := torAct Δ τ
    refine wTrans _ _ _ (Cint O τ) _ _ (fun S S' => S = ⇑(mulE O y) '' S') ?_ ?_ ?_ ?_ ?_ ?_
    · intro t S
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd ((isFix_tor (O := O) c d m t S).mp h1) h2
      · exact absurd ((isFix_tor (O := O) c d m t S).mpr h3) h1
      · rfl
    · intro t S
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd ((isFix_tor (O := O) c _ _ t S).mp h1) h2
      · exact absurd ((isFix_tor (O := O) c _ _ t S).mpr h3) h1
      · rfl
    · intro t S S' h
      show tor Δ t '' S = ⇑(mulE O y) '' (tor Δ t '' S')
      subst h
      rw [Set.image_image, Set.image_image]
      congr 1
      funext x
      refine Prod.ext rfl ?_
      change ofE Δ (quo t) * ((y : EL Δ τ) * x.2) = (y : EL Δ τ) * (ofE Δ (quo t) * x.2)
      ring
    · intro S S' h
      subst h
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd ((isFix_mulE (O := O) c d m y S').mp h1) h2
      · exact absurd ((isFix_mulE (O := O) c d m y S').mpr h3) h1
      · rfl
    · intro S _
      refine ⟨(mulE O y).symm '' S, ?_, fun S' h => ?_⟩
      · show S = ⇑(mulE O y) '' ((mulE O y).symm '' S)
        rw [Set.image_image]
        simp
      · subst h
        rw [Set.image_image]
        simp
    · intro S' _
      exact ⟨⇑(mulE O y) '' S', rfl, fun S h => h⟩
  · intro h
    obtain ⟨hreg, hc, hd, hmu, hms, hmsig⟩ := h
    have e1 : (↑y : EL Δ τ) * ↑y⁻¹ = 1 := Units.mul_inv y
    have e2 : sigL (↑y⁻¹ : EL Δ τ) * sigL ↑y = 1 := by
      rw [← sigL_mul, Units.inv_mul, sigL_one]
    have e3 : star (sigL (↑y : EL Δ τ)) * star (sigL ↑y⁻¹) = 1 := by
      rw [← star_mul, e2, star_one]
    refine ⟨hreg, hc, ?_, ?_, ?_, ?_⟩
    · simp only [sigL_mul, sigL_sigL]
      linear_combination hd + (d * sigL d) * (sigL (↑y⁻¹ : EL Δ τ) * sigL ↑y) * e1 + (d * sigL d) * e2
    · exact (hmu.mul y.isUnit).mul ⟨⟨_, _, e3, by rw [mul_comm, e3]⟩, rfl⟩
    · simp only [sigL_mul, sigL_star, sigL_sigL, star_mul, star_star, hms]
      ring
    · simp only [sigL_mul, sigL_star, sigL_sigL, star_mul, star_star, hmsig]
      linear_combination (-(m * d * star (sigL d) * sigL ↑y * star (↑y : EL Δ τ)) * (star (sigL (↑y : EL Δ τ)) * star (sigL ↑y⁻¹))) * e1 + (-(m * d * star (sigL d) * sigL ↑y * star (↑y : EL Δ τ))) * e3
