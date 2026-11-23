import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SplitQuadraticAlgebraOrder
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_stabilizer_character_trivial : ∀ (F : Type) [Field F] [CharZero F] [Invertible (2 : F)] (E : Type) [CommRing E] [Algebra F E] (c : E →ₐ[F] E) (ξ : E) (β ν : Type) [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] (J : Matrix β β E) (Cy : Matrix β ν E), IsQuad c ξ → IsHerm c J → IsLagr c J Cy → ∀ lam : UG c J →* ℂˣ, (∀ (p : UG c J) (t : GL ν E), ((p : GL β E) : Matrix β β E) * Cy = Cy * (t : Matrix ν ν E) → lam p = 1) → lam = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelChar.char_trivial | exact GlobalTheory.CompanionTheory.SiegelChar.char_trivial | (intros; apply GlobalTheory.CompanionTheory.SiegelChar.char_trivial <;> assumption)
