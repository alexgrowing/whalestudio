import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport

open NumberField IsDedekindDomain ValuativeRel PositivityTheory.Rg.Tf.Loc GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo
open scoped TensorProduct

theorem UpperTheory.V.Z.Tf.Orb.placeUniq :
    UpperTheory.V.Z.Tf.Orb.PlaceUniq := by
  intro F E _ _ _ _ _ _ hp v hs
  obtain ⟨w, hw⟩ := not_forall.1 hs
  have hd : ∀ w' : PlacesOver E v, Module.finrank (v.adicCompletion F) (w'.1.adicCompletion E) =
      Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) := fun w' => by
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (E ≃ₐ[F] E) w w'
    exact (galEquiv v σ w.1 w'.1 (by rw [← hσ]; rfl)).toLinearEquiv.finrank_eq.symm
  have h := sum_finrank_eq E v
  rw [Finset.sum_congr rfl fun w' _ => hd w', Finset.sum_const, smul_eq_mul, Finset.card_univ] at h
  rcases (Nat.prime_mul_iff.1 (h ▸ hp)) with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact absurd (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1).2 hw
  · obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.1 h1
    exact ⟨u, hu⟩
