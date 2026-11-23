import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EAComm

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.ChainParts

noncomputable section

namespace GlobalTheory.ChainParts

theorem dvd_of_isRootOfP_pow_succ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
    [CharZero O] [CharP (ResidueField O) p] {B : Vert.Model O} (hB : GlobalTheory.IsNormalScheme B.X) (g γ : Γ(B.X, ⊤)) (m : ℕ)
    (hg : IsRootOfP p g p) (hγ : IsRootOfP p γ (p ^ (m + 1))) : ∃ c : Γ(B.X, ⊤), g = γ ^ p ^ m * c := by
  haveI := hB
  obtain ⟨u, hu⟩ := hg
  obtain ⟨v, hv⟩ := hγ
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hdvd : (γ ^ p ^ m) ^ p ∣ g ^ p := by
    refine ⟨(u * v⁻¹ : Γ(B.X, ⊤)ˣ), ?_⟩
    rw [← pow_mul, ← pow_succ, hv, hu]
    simp only [Units.val_mul]
    linear_combination (-((u : Γ(B.X, ⊤)) * (p : Γ(B.X, ⊤)))) * v.mul_inv
  obtain ⟨c, hc⟩ := (IsIntegrallyClosed.pow_dvd_pow_iff hp0).mp hdvd
  exact ⟨c, hc⟩

end GlobalTheory.ChainParts

end
