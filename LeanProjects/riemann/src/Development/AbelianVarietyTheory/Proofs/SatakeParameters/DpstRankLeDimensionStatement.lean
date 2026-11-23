import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstRankLeDimension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dpst_rank_le_dimension : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL], (∀ (W : Type) [AddCommGroup W] [Module LL W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] LL W] [FiniteDimensional ℚ_[l] W] (ρW : Representation LL ↥(GK K) W), Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρW) ≤ finrank ℚ_[l] W) → ∀ {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V] [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V'] {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {f : V →ₗ[LL] V'} (hf : ∀ g v, f (ρ g v) = ρ' g (f v)), IsPst P ρ → f ≠ 0 → ∃ x : ↥(Dpst P ρ), GlobalTheory.Pst.DpstMap.dmap P hf x ≠ 0 := by
  first | exact @GlobalTheory.Pst.DmapNonzero.exists_dmap_ne_zero | exact GlobalTheory.Pst.DmapNonzero.exists_dmap_ne_zero | (intros; apply GlobalTheory.Pst.DmapNonzero.exists_dmap_ne_zero <;> assumption)
