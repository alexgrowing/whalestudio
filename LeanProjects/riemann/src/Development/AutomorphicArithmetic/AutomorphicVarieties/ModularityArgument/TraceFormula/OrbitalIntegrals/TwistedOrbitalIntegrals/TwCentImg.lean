import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport

open PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.twCentImg :
    UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.TwCentImg := by
  intro hC k E _ _ _ _ _ σ hσ n δ γ hγ hN
  have hp : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  have hsep : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := by
    have : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (γ : Matrix (Fin n) (Fin n) k).map (algebraMap k E) := rfl
    rw [this, Matrix.charpoly_map]
    exact hγ.map
  have hfix : ∀ y : GL (Fin n) k, sigmaGL σ (incl y : GL (Fin n) E) = incl y := fun y => by
    ext i j
    exact σ.commutes _
  have hcomm : ∀ a b : GL (Fin n) E, a * incl γ = incl γ * a → b * incl γ = incl γ * b → a * b = b * a := fun a b ha hb =>
    Units.ext (hC E n _ a.val b.val hsep (congrArg Units.val ha) (congrArg Units.val hb))
  have hδ : δ * incl γ = incl γ * δ := by
    have h := map_twNorm_of_pow_eq_one (sigmaGL σ) hp δ
    change sigmaGL σ (normGL σ δ) = δ⁻¹ * normGL σ δ * δ at h
    rw [hN, hfix] at h
    calc δ * incl γ = δ * (δ⁻¹ * incl γ * δ) := by rw [← h]
      _ = incl γ * δ := by group
  refine ⟨by rw [IsTwRegSemisimple, hN]; exact hsep, Subgroup.ext fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have h1 : x * incl γ = incl γ * x := hN ▸ twCent_commute_twNorm _ hp δ hx
    have h2 : x⁻¹ * δ * sigmaGL σ x = δ := hx
    have h3 : sigmaGL σ x = x := by
      calc sigmaGL σ x = δ⁻¹ * x * (x⁻¹ * δ * sigmaGL σ x) := by group
        _ = δ⁻¹ * (x * δ) := by rw [h2, mul_assoc]
        _ = x := by rw [hcomm x δ h1 hδ]; group
    have h4 : ∀ i j, ∃ c, algebraMap k E c = (x : Matrix (Fin n) (Fin n) E) i j := fun i j => by
      have hs : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) ((x : Matrix (Fin n) (Fin n) E) i j) :=
        congrArg (fun y : GL (Fin n) E => (y : Matrix (Fin n) (Fin n) E) i j) h3
      have := (IsGalois.mem_bot_iff_fixed ((x : Matrix (Fin n) (Fin n) E) i j)).mpr fun τ =>
        (Subgroup.zpowers_le.mpr hs) (hσ τ)
      rwa [IntermediateField.mem_bot] at this
    choose M hM using h4
    have e : (algebraMap k E).mapMatrix (Matrix.of M) = (x : Matrix (Fin n) (Fin n) E) := by
      ext i j
      exact hM i j
    have hd : (Matrix.of M).det ≠ 0 := fun h0 => by
      have h1 := RingHom.map_det (algebraMap k E) (Matrix.of M)
      rw [h0, map_zero, e] at h1
      exact (Matrix.GeneralLinearGroup.det x).ne_zero h1.symm
    have e' : incl (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd) = x := Units.ext e
    refine ⟨_, Subgroup.mem_centralizer_singleton_iff.2 ?_, e'⟩
    have hinj : Function.Injective (incl : GL (Fin n) k → GL (Fin n) E) := fun a b h => by
      ext i j
      exact (algebraMap k E).injective (congrArg (fun y : GL (Fin n) E => (y : Matrix (Fin n) (Fin n) E) i j) h)
    apply hinj
    rw [map_mul, map_mul, e', h1]
  · rintro ⟨t, ht, rfl⟩
    have h1 : (incl t : GL (Fin n) E) * incl γ = incl γ * incl t := by
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 ht]
    rw [mem_twCent, hfix, mul_assoc, ← hcomm _ δ h1 hδ]
    group
