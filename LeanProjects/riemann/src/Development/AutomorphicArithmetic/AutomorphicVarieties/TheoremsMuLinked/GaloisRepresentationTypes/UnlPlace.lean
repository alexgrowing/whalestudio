import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.AutP
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LevBasis

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th

private theorem unl_place {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {p : ℕ} (hp : p.Prime)
    {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    IsPlaceOver A w := by
  intro x
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, (k : 𝓞 ℚ) = x :=
    ⟨Rat.ringOfIntegersEquiv x, by
      rw [← map_intCast Rat.ringOfIntegersEquiv.symm, Int.cast_id, RingEquiv.symm_apply_apply]⟩
  have hc : ∀ k : ℤ, algebraMap ℚ Ω ((k : 𝓞 ℚ) : ℚ) = (k : Ω) := fun k => by simp
  have hv1 : ∀ k : ℤ, A.valuation (k : Ω) ≤ 1 := by
    intro k
    have := A.valuation_le_one (k : A)
    simpa using this
  have hA' : A.valuation ((p : ℤ) : Ω) < 1 := by simpa using hA
  have hw' : ((p : ℤ) : 𝓞 ℚ) ∈ w.asIdeal := by simpa using hw
  rw [hc]
  by_cases hk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    constructor
    · intro _
      rw [Int.cast_mul]
      exact w.asIdeal.mul_mem_right _ hw'
    · intro _
      rw [Int.cast_mul, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le' hA' (hv1 m)
  · have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    obtain ⟨a, b, hab⟩ := (hpr.irreducible.coprime_iff_not_dvd).mpr hk
    constructor
    · intro hlt
      exfalso
      have h1 : A.valuation ((a : Ω) * ((p : ℤ) : Ω)) < 1 := by
        rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hv1 a) zero_le' hA'
      have h2 : A.valuation ((b : Ω) * (k : Ω)) < 1 := by
        rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hv1 b) zero_le' hlt
      have h3 := A.valuation.map_add_lt h1 h2
      rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_add, hab, Int.cast_one, map_one] at h3
      exact lt_irrefl _ h3
    · intro hmem
      exfalso
      apply w.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have : ((a * p + b * k : ℤ) : 𝓞 ℚ) ∈ w.asIdeal := by
        rw [Int.cast_add, Int.cast_mul, Int.cast_mul]
        exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw') (w.asIdeal.mul_mem_left _ hmem)
      rwa [hab, Int.cast_one] at this

theorem UpperTheory.V.Th.spUnl :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.ψ → Af.KillsMu N D.ξ → Af.KillsMu N D.om → ∀ r, D.EPt r → Unl l N ![(D.e : ℤ) + 1, D.e, 1, 0] r.toHomUnits := by
  intro Ω _ _ _ l _ c D hG N hN hψ hξ hom r hr
  obtain ⟨R, iR, iA, iC, ρ, y, hpt, rfl⟩ := hr
  let r' : ↥(D.Gp l) →* GradeZeroInterpolatingElement.M4 (PadicAlgCl l) := (mapRep (↑y) ρ.hom).comp (D.Gp l).subtype
  have hon : Loc.PtOn D D.condL r' := ⟨R, iR, iA, iC, D.loc ρ l, y, hpt.atL, rfl⟩
  obtain ⟨h, κ, hfl, hine, -, -, -, hdist⟩ := Loc.spPtL D hG r' hon
  have hcyc : ∀ g : G ℚ Ω, ((cycBar ℚ Ω l g : (Qbar l)ˣ) : Qbar l) = (((chiO ℚ Ω l c.O g : (↥c.O)ˣ) : ↥c.O) : PadicAlgCl l) := by
    intro g
    show algebraMap ℚ_[l] (PadicAlgCl l) ((cycZ ℚ Ω l g : ℤ_[l]) : ℚ_[l]) = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l])
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    rfl
  have hinv : ∀ u : (↥c.O)ˣ, (((u⁻¹ : (↥c.O)ˣ) : ↥c.O) : PadicAlgCl l) = ((u : ↥c.O) : PadicAlgCl l)⁻¹ := by
    intro u
    apply eq_inv_of_mul_eq_one_left
    rw [← Subalgebra.coe_mul, Units.inv_mul]
    rfl
  have hne : ∀ u : (↥c.O)ˣ, ((u : ↥c.O) : PadicAlgCl l) ≠ 0 := by
    intro u h0
    have h1 : ((u : ↥c.O) : PadicAlgCl l) * (((u⁻¹ : (↥c.O)ˣ) : ↥c.O) : PadicAlgCl l) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv]
      rfl
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  let ι : (↥c.O)ˣ →* (Qbar l)ˣ := Units.map (MonoidHomClass.toMonoidHom c.O.val)
  intro w hw
  refine ⟨D.pl l, unl_place Fact.out (hG.pl_over l Fact.out) hw, κ, ?_, ?_⟩
  · refine ⟨![ι.comp (D.om⁻¹ * D.ξ * D.ψ), ι.comp D.ψ, ι.comp (D.om⁻¹ * D.ξ), 1], ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> intro s hs <;>
        simp [ι, hom s hs, hξ s hs, hψ s hs]
    · refine ⟨h⁻¹, fun s => ?_⟩
      simp only [inv_inv, Units.val_mul, MonoidHom.coe_toHomUnits]
      exact hfl s
    · intro i s hs
      apply Units.ext
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, hine i s hs, hcyc]
      fin_cases i <;>
        simp [ι, Raw.ps, Raw.th, Raw.al, Raw.Psi, Chr.Psi, hinv] <;>
        (try rw [zpow_add₀ (hne _), zpow_one, zpow_natCast]) <;> ring
  · intro i j heq
    by_cases hij : i = j
    · subst hij
      apply hG.decompSigma_ord
      have h1 : cycBar ℚ Ω l (D.s0 : G ℚ Ω) = 1 := by
        have e1 := congrArg (fun f => f D.s0) heq
        simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at e1
        exact (mul_eq_left.mp e1.symm)
      have h2 : cycZ ℚ Ω l (D.s0 : G ℚ Ω) = 1 := by
        apply Units.ext
        have e2 := congrArg Units.val h1
        have e3 : algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l (D.s0 : G ℚ Ω) : ℤ_[l]) : ℚ_[l]) = algebraMap ℚ_[l] (Qbar l) 1 := by
          rw [map_one]
          exact e2
        have e4 := (algebraMap ℚ_[l] (Qbar l)).injective e3
        exact PadicInt.ext e4
      rw [h2]
      exact IsOfFinOrder.one
    · have hmem : D.sg l ∈ D.Gp l := ((UpperTheory.V.GradeZeroInterpolatingElement.facts D hG).2.1 l (Finset.mem_insert_self _ _)).1
      obtain ⟨g, -, hg⟩ := hdist i j hij ⊤ (by simp) ⟨⟨D.sg l, hmem⟩, trivial, rfl⟩
      apply hg
      rw [heq, MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply, hcyc]
      rfl
