import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalGenDefs
import ReciprocityTheory.GaloisValuations.GlobalA
import GroundTheory.GlobalFields.CompletionAtPlace.Inertia
import GroundTheory.LocalFields.UnramifiedGalois

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion ValuativeRel

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem natCast_card_pow_sub_one_notMem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (hn : n ≠ 0) :
    ((Nat.card 𝓀[v.adicCompletion F] ^ n - 1 : ℕ) : 𝓞 F) ∉ v.asIdeal := by
  intro h
  have h1 := (GroundTheory.Global.ringOfIntegersToInteger_mem_maximalIdeal_iff v _).2 h
  rw [map_natCast] at h1
  apply GroundTheory.LocalField.natCast_card_pow_sub_one_ne_zero (K := v.adicCompletion F) hn
  rw [← map_natCast (IsLocalRing.residue 𝒪[v.adicCompletion F])]
  exact (IsLocalRing.residue_eq_zero_iff _).2 h1

theorem valuation_le_one_of_pow_eq_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ}
    (hm : m ≠ 0) {x : Ω} (hx : x ^ m = 1) : A.valuation x ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have : A.valuation x ^ m = 1 := by rw [← Valuation.map_pow, hx, Valuation.map_one]
  exact (one_lt_pow₀ h hm).ne' this

set_option maxHeartbeats 1000000 in
theorem exists_chi' (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (v : HeightOneSpectrum (𝓞 Kf.1)) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : IsPlaceOver A v)
    (N : ℕ+)
    (ι : AlgebraicClosure ℚ →ₐ[Kf.1] AlgebraicClosure (v.adicCompletion Kf.1))
    (ev : (AlgebraicClosure (v.adicCompletion Kf.1) ≃ₐ[v.adicCompletion Kf.1]
        AlgebraicClosure (v.adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A)
    (hev : ∀ σ x, ι (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ι x)) :
    ∃ χ : Dec (F := Kf.1) A → ZMod (N : ℕ),
      (∀ g h, χ (g * h) = χ g + χ h) ∧
      (∀ g : Dec (F := Kf.1) A, (g : G Kf.1 (AlgebraicClosure ℚ)) ∈ Ine (F := Kf.1) A → χ g = 0) ∧
      (∀ g : Dec (F := Kf.1) A, IsFrob (F := Kf.1) A (normV v) (g : G Kf.1 (AlgebraicClosure ℚ)) →
        χ g = 1) ∧
      Continuous χ ∧
      ∀ σ, χ (ev σ) = urChar (v.adicCompletion Kf.1) (AlgebraicClosure (v.adicCompletion Kf.1)) N σ := by

  classical
  have hm0 : (Nat.card 𝓀[v.adicCompletion Kf.1] ^ (N : ℕ) - 1) ≠ 0 := by
    have := GroundTheory.LocalField.one_lt_card_residueField_pow (K := v.adicCompletion Kf.1) N.ne_zero
    omega
  haveI : NeZero (Nat.card 𝓀[v.adicCompletion Kf.1] ^ (N : ℕ) - 1) := ⟨hm0⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (Nat.card 𝓀[v.adicCompletion Kf.1] ^ (N : ℕ) - 1)
  have hιξ : IsPrimitiveRoot (ι ξ) (Nat.card 𝓀[v.adicCompletion Kf.1] ^ (N : ℕ) - 1) := hξ.map_of_injective ι.toRingHom.injective
  have hmA : ¬ A.valuation (((Nat.card 𝓀[v.adicCompletion Kf.1] ^ (N : ℕ) - 1) : ℕ) : AlgebraicClosure ℚ) < 1 := by
    intro h
    apply natCast_card_pow_sub_one_notMem Kf.1 v N.ne_zero
    refine (hA _).1 ?_
    simpa using h
  let χ : Dec (F := Kf.1) A → ZMod (N : ℕ) := fun g =>
    urChar (v.adicCompletion Kf.1) (AlgebraicClosure (v.adicCompletion Kf.1)) N (ev.symm g)
  have hχ : ∀ g, χ g = unramifiedCoord (v.adicCompletion Kf.1) (ev.symm g) N := fun g => rfl
  have hχev : ∀ σ, χ (ev σ) =
      urChar (v.adicCompletion Kf.1) (AlgebraicClosure (v.adicCompletion Kf.1)) N σ := fun σ => by
    show urChar _ _ N (ev.symm (ev σ)) = _
    rw [MulEquiv.symm_apply_apply]
  clear_value χ
  have key : ∀ (g : Dec (F := Kf.1) A) (a : ℕ),
      (a : ZMod (N : ℕ)) = χ g ↔ (g : G Kf.1 (AlgebraicClosure ℚ)) ξ = ξ ^ Nat.card 𝓀[v.adicCompletion Kf.1] ^ a := by
    intro g a
    rw [hχ, natCast_eq_unramifiedCoord_iff hιξ (ev.symm g) a, ← hev (ev.symm g) ξ,
      MulEquiv.apply_symm_apply, ← map_pow]
    exact ι.toRingHom.injective.eq_iff
  refine ⟨χ, fun g h => ?_, fun g hg => ?_, fun g hg => ?_, ?_, fun σ => ?_⟩
  · rw [hχ, hχ, hχ, map_mul, unramifiedCoord_mul]
  · have hgx := hg.2 ξ (valuation_le_one_of_pow_eq_one A hm0 hξ.pow_eq_one)
    have e : (g : G Kf.1 (AlgebraicClosure ℚ)) ξ = ξ :=
      eq_of_pow_eq_one A hmA (by rw [← map_pow, hξ.pow_eq_one, map_one]) hξ.pow_eq_one hgx
    have := (key g 0).2 (by rw [pow_zero, pow_one]; exact e)
    rw [← this, Nat.cast_zero]
  · have hgx := hg.2 ξ (valuation_le_one_of_pow_eq_one A hm0 hξ.pow_eq_one)
    have hN : normV v = Nat.card 𝓀[v.adicCompletion Kf.1] := (natCard_residueField_integer v).symm
    rw [hN] at hgx
    have e : (g : G Kf.1 (AlgebraicClosure ℚ)) ξ = ξ ^ Nat.card 𝓀[v.adicCompletion Kf.1] :=
      eq_of_pow_eq_one A hmA (by rw [← map_pow, hξ.pow_eq_one, map_one])
        (by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]) hgx
    have := (key g 1).2 (by rw [pow_one]; exact e)
    rw [← this, Nat.cast_one]
  · refine continuous_def.2 fun s _ => ?_
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨Subtype.val ⁻¹' {τ : G Kf.1 (AlgebraicClosure ℚ) | τ ξ = (g : G Kf.1 (AlgebraicClosure ℚ)) ξ},
      fun g' hg' => ?_, continuous_subtype_val.isOpen_preimage _
        (isOpen_setOf_apply (F := Kf.1) ξ (fun y => y = (g : G Kf.1 (AlgebraicClosure ℚ)) ξ)), rfl⟩
    have h1 := (key g (χ g).val).1 (ZMod.natCast_zmod_val _)
    have h2 : (((χ g).val : ℕ) : ZMod (N : ℕ)) = χ g' := (key g' (χ g).val).2 (by
      rw [show (g' : G Kf.1 (AlgebraicClosure ℚ)) ξ = (g : G Kf.1 (AlgebraicClosure ℚ)) ξ from hg', h1])
    rw [ZMod.natCast_zmod_val] at h2
    show χ g' ∈ s
    rw [← h2]; exact hg
  · exact hχev σ

end PositivityTheory.Lit1.PTN
