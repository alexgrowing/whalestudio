import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
import Formalism.FrobeniusOrbits.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.HermitianLattices.StatementLat
import Formalism.HarderNarasimhan.Statement
import Formalism.FrobeniusOrbits.HostThickExists
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.LocalRingCardinality.DataRows
import Formalism.SatakeDualWeyl.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.HarderNarasimhan.StatementPl
import Formalism.HermitianLattices.StatementMass
import Formalism.LocalRingCardinality.DataArith
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.LatticeSlopes.Statement
import Formalism.FockGram.StatementHerm
import Formalism.ThetaLiftIndependence.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
import Formalism.LocalRingCardinality.DataKernels
import Formalism.HermitianLattices.StatementMaj
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit

private lemma den_coprime_of_mul_eq {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (M : Submodule (NumberField.RingOfIntegers K) V) (h : Submodule.span K (M : Set V) = ⊤) (x : V) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : NumberField.RingOfIntegers K) • x ∈ M := by
  have cast : ∀ (r : NumberField.RingOfIntegers K) (v : V),
      r • v = (algebraMap (NumberField.RingOfIntegers K) K r) • v :=
    fun r v => (algebraMap_smul K r v).symm
  have hx : x ∈ Submodule.span K (M : Set V) := h ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 := M.smul_mem (b : NumberField.RingOfIntegers K) hay
    have h2 := M.smul_mem (a : NumberField.RingOfIntegers K) hbz
    rw [smul_smul] at h1 h2
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rwa [Int.cast_mul, mul_comm]
    · rwa [Int.cast_mul]
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨m, hm, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).2
      (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
    obtain ⟨w, hw⟩ : ∃ w : NumberField.RingOfIntegers K,
        algebraMap (NumberField.RingOfIntegers K) K w = m • c := ⟨⟨_, hint⟩, rfl⟩
    refine ⟨m * a, mul_ne_zero hm ha, ?_⟩
    have h1 := M.smul_mem w hay
    have e : ((m * a : ℤ) : NumberField.RingOfIntegers K) • c • y =
        w • (a : NumberField.RingOfIntegers K) • y := by
      rw [cast, cast w, cast (a : NumberField.RingOfIntegers K), hw, smul_smul, smul_smul]
      congr 1
      simp only [map_mul, map_intCast, Int.cast_mul, zsmul_eq_mul]
      ring
    rwa [e]

theorem UpperTheory.Reformulated.B.ExistsBaseFieldIntegerDenominator.exists_den :
    ∀ {D : Formalism.BasicNotions.D7}
    {Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Formalism.MainNotions.S.VS D).V},
    Submodule.IsLattice D.host.E Λ →
      ∀ (x : (Formalism.MainNotions.S.VS D).V),
        ∃ (d : NumberField.RingOfIntegers ↥D.host.F),
          d ≠ (0 : NumberField.RingOfIntegers ↥D.host.F) ∧
            (Algebra.algebraMap (NumberField.RingOfIntegers ↥D.host.F) (NumberField.RingOfIntegers D.host.E) :
                    NumberField.RingOfIntegers ↥D.host.F → NumberField.RingOfIntegers D.host.E)
                  d •
                x ∈
              Λ := by
  intro D Λ hΛ x
  obtain ⟨n, hn, h⟩ := den_coprime_of_mul_eq Λ hΛ.span_eq_top x
  refine ⟨(n : NumberField.RingOfIntegers ↥D.host.F), Int.cast_ne_zero.2 hn, ?_⟩
  rwa [map_intCast]
