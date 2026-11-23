import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsScfEmbeddingDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.TriFrame

theorem exists_local_scf_embedding : ∀ (p : ℕ), p.Prime → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K], (p : R) ∈ maximalIdeal R → Cardinal.mk R ≤ Cardinal.continuum → ∃ (C : SCF p) (θ : K →+* ↥C.S), (∀ a, ‖θ (algebraMap R K a)‖ ≤ 1) ∧ ∀ a ∈ maximalIdeal R, ‖θ (algebraMap R K a)‖ < 1 := by
  intro p hp R K _ _ _ _ _ _ _ _ hR hc
  have : Algebra.EssFiniteType R K := .of_isLocalization K (nonZeroDivisors R)
  have hnf : ¬ IsField R := by
    intro hf
    rw [isField_iff_maximalIdeal_eq.1 hf, Ideal.mem_bot] at hR
    have h : (p : K) = 0 := by rw [← map_natCast (algebraMap R K), hR, map_zero]
    exact hp.ne_zero (Nat.cast_eq_zero.1 h)
  obtain ⟨V, hV, hd⟩ := exists_discreteValuationSubring_dominating_of_essFiniteType (L := K) hnf
  obtain ⟨h₁, h₂⟩ := (localSubring_range_le_valuationSubring_iff _ V).1 hd
  have hpV : (p : V) ∈ maximalIdeal V := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    simpa using h₂ _ hR
  obtain ⟨C, φ, φi, hφ⟩ := GlobalTheory.ShFam.Pad.Pull.exists_scf_embedding_dvd p V hp hpV
    ((Cardinal.mk_subtype_le _).trans ((IsLocalization.cardinalMk_le (nonZeroDivisors R)).trans hc))
  let θ : K →+* ↥C.S := IsFractionRing.lift (A := V) (g := (intO ↥C.S).subtype.comp φ)
    ((intO ↥C.S).subtype_injective.comp φi)
  have hθ (v : V) : θ v = φ v := IsFractionRing.lift_algebraMap _ v
  refine ⟨C, θ, fun a => ?_, fun a ha => ?_⟩
  · exact (congrArg norm (hθ ⟨_, h₁ a⟩)).le.trans (φ ⟨_, h₁ a⟩).2
  · refine (congrArg norm (hθ ⟨_, h₁ a⟩)).trans_lt (lt_of_not_ge fun hge => ?_)
    have hd := hφ 1 ⟨_, h₁ a⟩ (by simpa using hge)
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, h₁ a⟩)).mp (h₂ a ha) (isUnit_of_dvd_one hd)

end GlobalTheory.TriFrame
