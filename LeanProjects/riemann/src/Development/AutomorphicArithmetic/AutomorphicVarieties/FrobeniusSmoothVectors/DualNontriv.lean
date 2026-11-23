import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem dual_nontriv (K V : Type) [Field K] [AddCommGroup V] [Module K V] [Nontrivial V] :
    Nontrivial (Module.Dual K V) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hv ((Module.forall_dual_apply_eq_zero_iff K v).mp fun φ => by
    rw [Subsingleton.elim φ 0]
    rfl)

theorem UpperTheory.V.Fr.st_loc :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] [Nontrivial M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v → ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → (∀ g ∈ Dec (F := ℚ) A, cycMod ℚ Ω l 1 g = 1) → ∀ ρ : Representation (ZMod (l ^ 1)) (Dec (F := ℚ) A) M, (∀ g m, ρ g m = m) → Nat.card (H0 ρ) < Nat.card (H1 ρ) := by
  intro hFin hTate hEuler Ω _ _ _ l hl M _ _ _ _ _ _ A v hv hlv hcyc ρ htriv
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact hl.out⟩
  have hcont : ReciprocityTheory.Gal.ContAction ρ := by
    show Continuous fun p : Dec (F := ℚ) A × M => ρ p.1 p.2
    simp only [htriv]
    exact continuous_snd
  have hF := hFin ℚ Ω l 1 M A ρ v one_pos hv hcont
  have hE := (hEuler ℚ Ω l 1 M A ρ v one_pos hv hcont).2 hlv
  obtain ⟨⟨e⟩, -, -, -, hbij⟩ := hTate ℚ Ω l 1 M A ρ v one_pos hv hcont
  haveI : Finite (H2 ρ) := hF.2.2.1
  haveI : Finite (H0 ρ) := hF.1
  have hinv : ∀ φ : TDual (ZMod (l ^ 1)) M,
      φ ∈ H0 ((twDual ((cycMod ℚ Ω l 1).comp (Dec (F := ℚ) A).subtype) ρ).comp (MonoidHom.id _)) := by
    intro φ g
    apply TDual.ext
    intro m
    simp [twDual, hcyc g.1 g.2]
    show φ (ρ g⁻¹ m) = φ m
    rw [htriv]
  haveI : Nontrivial (TDual (ZMod (l ^ 1)) M) := dual_nontriv (ZMod (l ^ 1)) M
  obtain ⟨φ0, hφ0⟩ := exists_ne (0 : TDual (ZMod (l ^ 1)) M)
  set X := H0 ((twDual ((cycMod ℚ Ω l 1).comp (Dec (F := ℚ) A).subtype) ρ).comp (MonoidHom.id _))
  have hx0 : (⟨φ0, hinv φ0⟩ : X) ≠ 0 := fun h => hφ0 (congrArg Subtype.val h)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual (ZMod (l ^ 1)) X, f ⟨φ0, hinv φ0⟩ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 ((Module.forall_dual_apply_eq_zero_iff (ZMod (l ^ 1)) _).mp h)
  let ψ : X →ₗ[ZMod (l ^ 1)] H2 ((charRep ((cycMod ℚ Ω l 1).comp (Dec (F := ℚ) A).subtype)).comp
      (MonoidHom.id _)) := e.symm.toLinearMap ∘ₗ f
  have hψ : ψ ≠ 0 := by
    intro h
    have h1 : ψ ⟨φ0, hinv φ0⟩ = 0 := by rw [h]; rfl
    exact hf (e.symm.map_eq_zero_iff.mp h1)
  obtain ⟨y, hy⟩ := hbij.2 ψ
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hψ (by rw [← hy, map_zero])
  haveI : Nontrivial (H2 ρ) := ⟨⟨y, 0, hy0⟩⟩
  rw [hE]
  exact lt_mul_of_one_lt_right (Nat.card_pos) Finite.one_lt_card
