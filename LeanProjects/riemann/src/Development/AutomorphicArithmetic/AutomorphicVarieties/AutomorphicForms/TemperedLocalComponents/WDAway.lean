import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

private theorem UpperTheory.V.Af.isOpen_fixMu {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {M : ℕ}
    (hM : 1 ≤ M) : IsOpen {s : G F Ω | ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ} := by
  classical
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots (show 0 < M from hM)] using hζ
  have e : {s : G F Ω | ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ} =
      ⋂ ζ ∈ {ζ : Ω | ζ ^ M = 1}, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) ζ : Set (Ω ≃ₐ[F] Ω)) := by
    ext s
    simp [MulAction.mem_stabilizer_iff]
  rw [e]
  exact hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral ζ

theorem UpperTheory.V.Af.wdAway :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.WDAway := by
  intro _ F Ω _ _ _ _ _ l _ ι n M hM r _ w hl A h χ hχ hd x hx
  obtain ⟨g, hg⟩ := hd
  let r' : G F Ω →* GL (Fin n) (Qbar l) := (MulAut.conj g).toMonoidHom.comp r
  have hr' : ∀ s, r' s = g * r s * g⁻¹ := fun s => rfl
  have hx' : IsWDOf ι r' x := hx.of_conj hl g fun s => by rw [hr', inv_mul_cancel_right]
  obtain ⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩ := hx'
  have hs : IsSmooth (r'.comp (Weil h).subtype) := by
    refine .of_open ((UpperTheory.V.Af.isOpen_fixMu (F := F) (Ω := Ω) hM).preimage continuous_subtype_val)
      (fun ζ _ => rfl) fun σ hσ => Units.ext ?_
    change (r' σ : Matrix (Fin n) (Fin n) (Qbar l)) = 1
    rw [hr', hg σ σ.2]
    simp [fun i => hχ i σ hσ]
  obtain rfl : N = 0 := hN.unique ht ((isMonodromy_zero_iff (h := h)).mpr hs)
  refine ⟨fun i => (Units.map ι.toRingHom.toMonoidHom).comp (χ i), a, fun i s hs => ?_, rfl, ?_, fun s => ?_⟩
  · simp [hχ i s hs]
  · rw [ha.1, map_zero]
  · rw [IsFrobSS.ρ_ineIncl (ρ := hN.rep hl ht hφ ι) ha (hN.isSmooth_rep hl ht _ ι), hN.rep_apply, wdMat_zero, coe_ineIncl, hr',
      hg s s.2, toEndC_apply, Matrix.diagonal_map (map_zero ι)]
    rfl
