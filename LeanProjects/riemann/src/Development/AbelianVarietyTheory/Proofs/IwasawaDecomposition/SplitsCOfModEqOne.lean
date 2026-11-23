import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

open Classical in

theorem splitsC_of_modEq_one : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime →
    p ≡ 1 [MOD H.QS * H.q * H.d] → SplitsC H.E p := by
  intro R H p hp h
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  have hpos : 0 < H.QS * H.q * H.d := Nat.pos_of_ne_zero H.condN_ne_zero
  have hlt : 1 < H.QS * H.q * H.d :=
    lt_of_lt_of_le (by omega : 1 < H.d) (Nat.le_of_dvd hpos (dvd_mul_left _ _))
  refine (GlobalTheory.HostSplit.split_of_one_mod R H p hp ?_).1
  rw [h]
  exact Nat.mod_eq_of_lt hlt

end GlobalTheory.Mem.Chr
