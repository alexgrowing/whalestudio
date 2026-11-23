import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.Places
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.FiniteCohomologyTwoInt
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.OddOrTcBasePf
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.InvariantsEqOfPointwise
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]
  (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ)
  (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
  (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m)
  (hΓ : Nat.Coprime (Nat.card (L.1 ≃ₐ[K.1] L.1)) ℓ)

theorem dMod_one_eq [Finite (ModN (AA hL 1) ℓ)] :
    dMod hL (dN hL hζ M hM hΓ) 1 =
      Module.finrank (ZMod ℓ) ((gsH1SUnitsModRep ℓ hL).tprod
        (quotientRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (homRep (gsRootsZMod S ℓ) M)
          (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM))).invariants := by
  exact dMod_one_eq_pf hL hζ M hM hΓ

set_option maxHeartbeats 800000 in

theorem poitou_tate_H2_nat [Fintype S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hKK : Odd ℓ ∨ IsTotallyComplex K.1)
    (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :
    Module.finrank (ZMod ℓ) (cohomology M 2) +
        Module.finrank (ZMod ℓ) (dualRep (gsRootsZMod S ℓ) M).ρ.invariants =
      Module.finrank (ZMod ℓ) (shaSubmodule (gsFinFamily S ιs) M 2) +
        ∑ v : S, Module.finrank (ZMod ℓ) (Representation.invariants
          ((dualRep (gsRootsZMod S ℓ) M).ρ.comp (gsFinFamily S ιs v).toMonoidHom)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hS' : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := fun v hv => by
    by_contra h
    exact hℓS v h hv
  haveI : Finite M := finite_of_moduleFinite M
  have hPT := natCard_gs_cohomology_two_mul S ιs hS' hKK (gsBaseCase S ιs hS' hKK) (intRep M) (nsmul_intRep M)
  apply Nat.pow_right_injective hℓ.two_le
  simp only [pow_add]
  calc ℓ ^ Module.finrank (ZMod ℓ) (cohomology M 2) *
        ℓ ^ Module.finrank (ZMod ℓ) (dualRep (gsRootsZMod S ℓ) M).ρ.invariants
      = Nat.card (cohomology (intRep M) 2) * Nat.card (cohomology (dualRep (gsRoots S ℓ) (intRep M)) 0) := by
        rw [card_H2_integral_module M hℓS, card_H0_dual_module M]
    _ = Nat.card (ptSha (gsFinFamily S ιs) (intRep M) 2) *
        ∏ v : S, Nat.card (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom
          (dualRep (gsRoots S ℓ) (intRep M))) 0) := hPT
    _ = ℓ ^ Module.finrank (ZMod ℓ) (shaSubmodule (gsFinFamily S ιs) M 2) *
        ∏ v : S, ℓ ^ Module.finrank (ZMod ℓ) (Representation.invariants
          ((dualRep (gsRootsZMod S ℓ) M).ρ.comp (gsFinFamily S ιs v).toMonoidHom)) :=
        congrArg₂ (· * ·) (card_sha_int M hℓS ιs) (Finset.prod_congr rfl fun v _ => card_H0_dual_local M ιs v)
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum]

set_option maxHeartbeats 800000 in

theorem poitou_tate_H2_int [Fintype S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    (hK : ℓ ≠ 2 ∨ IsTotallyComplex L.1) [Finite (ModN (AA hL 1) ℓ)]
    (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :
    (Module.finrank (ZMod ℓ) (cohomology M 2) : ℤ) +
        Module.finrank (ZMod ℓ) (dualRep (gsRootsZMod S ℓ) M).ρ.invariants =
      dMod hL (dN hL hζ M hM hΓ) 1 +
        ∑ v : S, (Module.finrank (ZMod ℓ) (Representation.invariants
          ((dualRep (gsRootsZMod S ℓ) M).ρ.comp (gsFinFamily S ιs v).toMonoidHom)) : ℤ) := by
  have hℓ : ℓ.Prime := Fact.out
  have hKK : Odd ℓ ∨ IsTotallyComplex K.1 := odd_or_tc_base_pf hL hcop hK
  have hKL : Odd ℓ ∨ IsTotallyComplex L.1 := hK.imp_left fun h => hℓ.odd_of_ne_two h
  have hn := poitou_tate_H2_nat M hℓS hKK ιs
  have hsha := finrank_shaSubmodule_two_eq_finrank_invariants ℓ hL ιs hℓS hKL hcop (roots_trivial hL hζ) M hM
  have e1 := dMod_one_eq hL hζ M hM hΓ
  have hz := congrArg (Nat.cast : ℕ → ℤ) hn
  have hz2 := congrArg (Nat.cast : ℕ → ℤ) hsha
  simp only [Nat.cast_add, Nat.cast_sum] at hz
  rw [e1]
  linarith

end PositivityTheory.Lit1.GEN.X
