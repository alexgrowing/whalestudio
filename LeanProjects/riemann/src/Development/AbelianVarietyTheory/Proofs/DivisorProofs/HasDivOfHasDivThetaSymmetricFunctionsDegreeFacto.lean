import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowDivMemOfEsymmPowDivMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEsymmPowDivMemOfIsLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem hasDiv_of_hasDiv_symTup : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (N : ℕ)
    (c : Fin N → Ω), Geo.Tor.IsNormalScheme M.Z → M.HasDiv (symTup c) → M.HasDiv c := by
  intro k Ω _ _ _ M N c hn hd z
  obtain ⟨j, he, hdiv⟩ := hd z
  haveI := RatModel.isIntegrallyClosed_O hn z
  set D := N.factorial with hD
  set e := symTup c j with he'
  have hD1 : 1 ≤ D := Nat.factorial_pos N

  haveI : IsFractionRing (M.O z).toSubring Ω := inferInstanceAs (IsFractionRing (M.O z) Ω)
  haveI : IsIntegrallyClosed (M.O z).toSubring := inferInstanceAs (IsIntegrallyClosed (M.O z))
  haveI hcl : IsIntegrallyClosedIn (M.O z).toSubring Ω :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn Ω).1 inferInstance
  have h1 : ∀ a, c a ^ D / e ∈ M.O z := by
    intro a
    have hmem : c a ^ D / e ∈ ⨅ V : {V : ValuationSubring Ω // (M.O z).toSubring ≤ V.toSubring}, V.1.toSubring := by
      refine Subring.mem_iInf.2 fun V => ?_
      refine pow_div_mem_of_esymm_pow_div_mem Ω V.1 (Fin N) c D e he (fun i hi1 hi2 => ?_) a
      simp only [Fintype.card_fin] at hi2
      refine ⟨Nat.dvd_factorial hi1 hi2, V.2 ?_⟩
      have := hdiv ⟨i - 1, by omega⟩
      simp only [symTup, Nat.sub_add_cancel hi1] at this
      exact this
    rw [← Subring.eq_iInf_of_isIntegrallyClosedIn] at hmem
    exact hmem
  haveI : IsLocalRing (M.O z).toSubring := inferInstanceAs (IsLocalRing (M.O z))
  obtain ⟨a, ha, hea⟩ := exists_esymm_pow_div_mem_of_isLocalRing Ω (M.O z).toSubring (Fin N) c D ((j : ℕ) + 1) e hD1
    (by omega) (Nat.dvd_factorial (by omega) (by omega)) he rfl h1
  refine ⟨a, ha, fun b => ?_⟩
  have hpow : (c b / c a) ^ D ∈ M.O z := by
    have : (c b / c a) ^ D = (c b ^ D / e) * (e / c a ^ D) := by
      rw [div_pow, div_mul_div_cancel₀ he]
    rw [this]
    exact mul_mem (h1 b) hea
  have hint : IsIntegral (M.O z) (c b / c a) :=
    IsIntegral.of_pow (by omega) (isIntegral_algebraMap (R := M.O z) (x := ⟨_, hpow⟩))
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact hy ▸ y.2

end GlobalTheory.UMin
