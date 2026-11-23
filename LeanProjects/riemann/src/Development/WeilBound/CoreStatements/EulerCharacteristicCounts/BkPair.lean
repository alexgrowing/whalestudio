import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasisStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ActQIsLocallyConstant
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.DualQOfTopInj
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GrowthGaloisInvariantsModPrimePowerLattice
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

set_option maxHeartbeats 2000000 in
theorem pairO : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 ((D.loc l).PD K) LA LA' P → ∀ ϖ : O, Irreducible ϖ → ∀ r : ℕ, ∃ B : (↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) →ₗ[O] (↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ r}), (∀ (x : ↥LA.T) (y : ↥LA'.T) (p : O), P x y = algebraMap O LL p → B (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Ideal.Quotient.mk _ p) ∧ (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) := by
  intro D l _ K LL _ _ _ O _ _ hG A A' LA LA' P hd ϖ hϖ r
  have hG0 : ∃ hO : IsDomain O, @IsDiscreteValuationRing O _ hO ∧ IsFractionRing O LL := hG.1
  have hO : IsDomain O := hG0.choose
  have hF : IsFractionRing O LL := hG0.choose_spec.2
  have h1 : ∀ y, y ∈ LA'.T ↔ ∀ x ∈ LA.T, ∃ a : O, P x y = algebraMap O LL a := hd.2
  have h2 : ∀ x, x ∈ LA.T ↔ ∀ y ∈ LA'.T, ∃ a : O, P.flip y x = algebraMap O LL a :=
    ((GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hG A LA ϖ hϖ).2.2.2.2 A' LA' P hd).2
  simp only [LinearMap.flip_apply] at h2
  exact GlobalTheory.CompanionTheory.LocDual.Q.pairing_exists LL O A.V A'.V LA.T LA'.T P ϖ hϖ.ne_zero r h1 h2

theorem cardQ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ r : ℕ, Finite (↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) ∧ Nat.card (↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) = Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank LL A.V) := by
  intro l _ K LL _ _ _ O _ _ hG A LA ϖ hϖ r
  obtain ⟨⟨hO, hD, hF⟩, -⟩ := id hG
  have := hO
  have := hD
  have := hF
  have hq := (GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hG ϖ hϖ).2.1
  refine ⟨(GlobalTheory.CompanionTheory.LocDual.Q.finite_quot O A.V LA.T ϖ r hq LA.fg).2, ?_⟩
  have : Module.Finite O ↥LA.T := Module.Finite.iff_fg.mpr LA.fg
  have := LA.free
  rw [GlobalTheory.CompanionTheory.GrowthOfInvariants.card_quot_free (Module.finBasis O ↥LA.T).equivFun,
    GlobalTheory.CompanionTheory.GrowthOfInvariants.card_quot_pow ϖ hϖ.ne_zero, GlobalTheory.H1fGeneratorBoundAlt.finrank_lattice LA, pow_mul]

theorem locconst : ∀ (_D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (m : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), IsLocallyConstant fun g => actQ LA _ hI g m := by
  intro D l _ K LL _ _ _ O _ _ hG A LA ϖ hϖ r hI m
  exact GlobalTheory.CompanionTheory.LocDual.Q.act_locConst D l K LL O hG A LA ϖ hϖ r hI m

end PositivityTheory.LocalTateOrthogonality.Bk
