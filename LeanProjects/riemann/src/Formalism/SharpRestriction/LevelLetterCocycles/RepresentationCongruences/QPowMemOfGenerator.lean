import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsUnitOfResidueConstNeZero
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.PpLeHLD

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem q_pow_mem_of_generator [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    {T : LocLat G Qp LL O} (hT : IsCrys PD T.ρ) (i : ZMod n) (Bq : ℕ) (g : LetA O n) (hg : g ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k})
    (x : W.DD T) (hx : InFP W T i 1 1 x) (hgx : ∃ k : ℕ, InFP W T i 1 (qA W ^ Bq) (lA W ^ k • g • x)) :
    InFP W T i 1 (qA W ^ Bq) x := by

  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T hT hO hinj
  obtain ⟨-, N, a, ha, b, hb, hN⟩ := l_pow_mem_levels_q_pow_ideal Br Bq hg
  obtain ⟨k, z, hz, hkz⟩ := hgx
  have hx1 : x ∈ Pp W T i 1 := by
    obtain ⟨y, hy, hxy⟩ := hx
    rw [hxy, one_smul]
    exact hy
  have hlx : lA W ^ k • x ∈ Pp W T i 1 := by
    rw [show lA W ^ k = ((PD.p ^ k : ℕ) : LetA O n) by simp [lA], Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hx1 _
  have hqPi : qA W ^ Bq ∈ PiPs W := by
    apply Submonoid.pow_mem
    unfold PiPs
    exact Submonoid.subset_closure (Set.mem_insert_of_mem _ ⟨0, by simp [ps]⟩)
  have h1 : InFP W T i 1 1 ((1 : LetA O n) • x) := by
    rw [one_smul]
    exact hx

  have key : lA W ^ (k + N) • x = qA W ^ Bq • (a • z + b • (lA W ^ k • x)) := by
    calc lA W ^ (k + N) • x = (a * g + b * qA W ^ Bq) • (lA W ^ k • x) := by
          rw [← hN, smul_smul, ← pow_add, Nat.add_comm k N]
      _ = a • (lA W ^ k • g • x) + b • (qA W ^ Bq • (lA W ^ k • x)) := by
          rw [add_smul, mul_smul, mul_smul, smul_comm g (lA W ^ k) x]
      _ = qA W ^ Bq • (a • z + b • (lA W ^ k • x)) := by
          rw [hkz, smul_add, smul_comm a, smul_comm b]
  have hmem : a • z + b • (lA W ^ k • x) ∈ Pp W T i 1 :=
    add_mem (DYB.Pp_smul W T i ha hz) (DYB.Pp_smul W T i hb hlx)
  exact hSatP hcase T i 1 (qA W ^ Bq) 1 hT hqPi (one_mem _) x h1
    ⟨k + N, by unfold InFP; exact ⟨_, hmem, key⟩⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
