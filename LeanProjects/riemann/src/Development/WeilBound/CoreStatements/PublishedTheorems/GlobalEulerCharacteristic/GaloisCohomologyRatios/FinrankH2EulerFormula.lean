import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.PoitouTateH2Nat
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.FinrankInvariantsTrivialTprod

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]
  (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ)
  (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
  (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m)
  (hΓ : Nat.Coprime (Nat.card (L.1 ≃ₐ[K.1] L.1)) ℓ)

theorem finrank_H2_euler_formula [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    (hK : ℓ ≠ 2 ∨ IsTotallyComplex L.1) [Finite (ModN (AA hL 1) ℓ)] :
    (Module.finrank (ZMod ℓ) (cohomology M 2) : ℤ) =
      dMod hL (dN hL hζ M hM hΓ) 1 + dPlaces (S := S) (dN hL hζ M hM hΓ) - (dN hL hζ M hM hΓ).one := by
  classical
  haveI : Fintype S := Fintype.ofFinite S
  have ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) :=
    fun v => IsAlgClosed.lift
  have h1 := poitou_tate_H2_int hL hζ M hM hΓ hℓS hcop hK ιs
  have h2 := local_dual_invariants_sum hL hζ M hM hΓ hℓS ιs
  have h3 := global_dual_invariants_finrank hL hζ M hM hΓ hℓS
  linarith

end PositivityTheory.Lit1.GEN.X
