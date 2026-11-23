import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.V00
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

private theorem open_toZMod (l : ℕ) [Fact l.Prime] : IsOpen {x : ℤ_[l] | PadicInt.toZMod x = 1} := by
  have hS : {x : ℤ_[l] | PadicInt.toZMod x = 1} = {x | ‖x - 1‖ < 1} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod,
      RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
  rw [hS]
  exact isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const

theorem UpperTheory.frame_criterion_decomposition_groups :
    UpperTheory.V.Pr.ExistsPrimeSplitInKernelWithNontrivialCyclotomic := by
  unfold UpperTheory.V.Pr.ExistsPrimeSplitInKernelWithNontrivialCyclotomic
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k hK g hg hc M' hM'
  let ρ : G (W.Lp L) Ω →* Φ.Γ := k.p.comp (toUpl Ω L)
  have hemb : Continuous (galEmb ℚ (W.Lp L) Ω) := (galEmbTop ℚ (W.Lp L) Ω).1.continuous
  have hρ : Continuous ρ := by
    have hto : Continuous (toUpl Ω L) := continuous_induced_rng.2 hemb
    exact k.p_cont.comp hto
  let U1 : Subgroup (G (W.Lp L) Ω) := Φ.Ψ.ker.comap ρ
  let U2 : Subgroup (G (W.Lp L) Ω) :=
    ((Units.map (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toMonoidHom).comp (cycZ (W.Lp L) Ω l)).ker
  let U3 : Subgroup (G (W.Lp L) Ω) := (η.comp (galEmb ℚ (W.Lp L) Ω)).ker
  have hU2 : ∀ τ, τ ∈ U2 ↔ PadicInt.toZMod (cycZ (W.Lp L) Ω l τ : ℤ_[l]) = 1 := by
    intro τ
    simp [U2, MonoidHom.mem_ker, Units.ext_iff]
  have hfix : ∀ τ : G (W.Lp L) Ω, τ ∈ galOf (W.Lp L) L Ω ↔ τ ∈ U3 := by
    intro τ
    change _ ↔ η (galEmb ℚ (W.Lp L) Ω τ) = 1
    rw [← k.mem_range_resP τ, mem_galOf]
    constructor
    · intro hτ
      exact ⟨AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun x => hτ x), AlgEquiv.ext fun y => rfl⟩
    · rintro ⟨t, rfl⟩ x
      exact t.commutes x
  have hO1 : IsOpen (U1 : Set (G (W.Lp L) Ω)) := hK.preimage hρ
  have hO2 : IsOpen (U2 : Set (G (W.Lp L) Ω)) := by
    have hset : (U2 : Set (G (W.Lp L) Ω)) =
        (fun τ => (cycZ (W.Lp L) Ω l τ : ℤ_[l])) ⁻¹' {x : ℤ_[l] | PadicInt.toZMod x = 1} := by
      ext τ
      exact hU2 τ
    rw [hset]
    exact (open_toZMod l).preimage (Units.continuous_val.comp (continuous_cycZ (W.Lp L) Ω l))
  have hO3 : IsOpen (U3 : Set (G (W.Lp L) Ω)) := by
    have hset : (U3 : Set (G (W.Lp L) Ω)) = galOf (W.Lp L) L Ω := by
      ext τ
      exact (hfix τ).symm
    rw [hset]
    exact (galEmbTop (W.Lp L) L Ω).2.1
  haveI hN1 : U1.Normal := (Φ.Ψ.normal_ker).comap ρ
  let U : Subgroup (G (W.Lp L) Ω) := U1 ⊓ U2 ⊓ U3
  haveI : U.Normal := inferInstance
  have hOU : IsOpen (U : Set (G (W.Lp L) Ω)) := (hO1.inter hO2).inter hO3
  let g' : G (W.Lp L) Ω := W.resP L Ω g
  obtain ⟨w, A, p, σ', -, hp, hpM, -, hpw, hnorm, -, hA, hIne, hFrob, hσU⟩ :=
    Loc.v00 U hOU g' ∅ M' hM'
  have hg'1 : g' ∈ U1 := hg
  have hg'3 : g' ∈ U3 := (k.mem_range_resP g').1 ⟨g, rfl⟩
  have hσeq : σ' = g' * (σ'⁻¹ * g')⁻¹ := by group
  have hσ1 : σ' ∈ U1 := by
    rw [hσeq]
    exact U1.mul_mem hg'1 (U1.inv_mem hσU.1.1)
  have hσ3 : σ' ∈ U3 := by
    rw [hσeq]
    exact U3.mul_mem hg'3 (U3.inv_mem hσU.2)
  have hσ2 : σ' ∉ U2 := by
    intro h
    have h2 := U2.mul_mem h hσU.1.2
    rw [mul_inv_cancel_left] at h2
    exact hc ((hU2 g').1 h2)
  let H : Subgroup (G (W.Lp L) Ω) := U1 ⊓ U3
  have hOH : IsOpen (H : Set (G (W.Lp L) Ω)) := hO1.inter hO3
  have hIH : Ine A ≤ H := fun τ hτ => ⟨(hIne hτ).1.1, (hIne hτ).2⟩
  have hFrob' : IsFrob A (normV w) σ' := by
    rw [hnorm]
    exact hFrob
  have hDec : (Dec A : Subgroup (G (W.Lp L) Ω)) ≤ H :=
    Kum.decGen (W.Lp L) Ω A w σ' H hA hFrob' hOH hIH ⟨hσ1, hσ3⟩
  refine ⟨w, A, p, hp, hpM, hnorm, hpw, hA, ?_, ?_, ?_⟩
  · intro τ hτ
    exact (k.mem_range_resP τ).2 (hDec hτ).2
  · intro t ht
    have ht' : W.resP L Ω t ∈ (Dec A : Subgroup (G (W.Lp L) Ω)) := ht
    exact (hDec ht').1
  · obtain ⟨t, ht⟩ := (k.mem_range_resP σ').2 hσ3
    refine ⟨t, ?_, ?_⟩
    · change W.resP L Ω t ∈ (Dec A : Subgroup (G (W.Lp L) Ω))
      rw [ht]
      exact hFrob.1
    · change PadicInt.toZMod (cycZ (W.Lp L) Ω l (W.resP L Ω t) : ℤ_[l]) ≠ 1
      rw [ht]
      exact fun h => hσ2 ((hU2 σ').2 h)
