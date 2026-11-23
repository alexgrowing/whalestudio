import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InclWFrobIter

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Decompl

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem ioE_fixed_of_resΓ_eq_one (hO : Function.Injective (algebraMap O LL)) (g : G)
    (hg : W.resΓ g = 1) (e : W.EE) : gR g (E.ioE e) = E.ioE e := by
  rw [← GlobalTheory.TorsionBoundCompare.ioE_γ E hO g e, hg, map_one]
  rfl

theorem ioE_letπ : E.ioE (algebraMap (LetA O n) W.EE letπ) = inclR πA := by
  rw [E.ioE_ext, E.io_π]

theorem ioE_bounded_pole {p : ℕ} (hp : PD.p = p) (e : W.EE) :
    ∃ c : ℕ, Near (inclR : RA →+* RW) p (inclR πA) 0 (inclR πA ^ c * E.ioE e) := by
  obtain ⟨a, m, h⟩ := W.EE_dense e 1
  rw [pow_one, Ideal.mem_span_singleton, hp] at h
  obtain ⟨r, hr⟩ := h
  have h1 := congrArg E.ioE hr
  rw [map_sub, map_mul, map_mul, map_natCast, map_pow, map_pow, ioE_letπ, E.ioE_ext] at h1
  refine ⟨m, E.io a, E.ioE r, ?_⟩
  rw [pow_zero, one_mul, ← h1]
  change _ = inclR (E.io a) + _
  ring

end Generic

theorem ioE_compat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ e, E.tie.ioE (W.φE e) = φRW LL (E.tie.ioE e)) ∧ (∀ g : ↥(GK K), W.resΓ g = 1 → ∀ e, AI.gRW LL (g : GQ l) (E.tie.ioE e) = E.tie.ioE e) ∧ E.tie.ioE (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE letπ) = piR AI LL s ∧ (∀ e, ∃ c : ℕ, NearPi AI LL s 0 (piR AI LL s ^ c * E.tie.ioE e)) := by
  intro l _ P AI K s LL h W E
  have hO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  exact ⟨fun e => GlobalTheory.TorsionBoundCompare.ioE_φ E.tie hO e,
    fun g hg e => ioE_fixed_of_resΓ_eq_one E.tie hO g hg e, ioE_letπ E.tie,
    fun e => ioE_bounded_pole E.tie (P.PD_p K) e⟩

end GlobalTheory.Decompl
