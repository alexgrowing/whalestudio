import Mathlib
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegrallyClosedOverring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGeneric

theorem exists_th_ne_zero : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] [CharZero K] (yK : S.R →+* K), ∃ a : S.Gam, yK ⟨S.th a, S.th_mem a⟩ ≠ 0 := by
  intro hL hL₂ o Ω _ _ _ S ρ K _ _ yK
  obtain ⟨c, -, h⟩ := GlobalTheory.ZH.GoodOut.exists_th_notMem hL hL₂ ρ ⟨RingHom.ker yK, RingHom.ker_isPrime yK⟩ 0
  exact ⟨0 + c, fun e => h (RingHom.mem_ker.2 e)⟩

end GlobalTheory.ThetaGeneric
