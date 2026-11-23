import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelIndexMeasure

theorem measure_eq_relIndex_smul : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J J₀ : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n))
  (K K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ μ₀ : Measure (GA D V)), ι.range = GfC V → J ≤ J₀ → J.relIndex J₀ ≠ 0 →
  IsOpenCompactLevel V K → IsOpenCompactLevel V K₀ → (∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J) → (∀ x, Lev.finE V (ι x) ∈ K₀ ↔ x ∈ J₀) →
  Lev.IsMeasLevDef V K μ → Lev.IsMeasLevDef V K₀ μ₀ → μ = (J.relIndex J₀ : ENNReal) • μ₀ := by
  intro D V n ι J J₀ K K₀ μ μ₀ hι hJ hJi hK hK₀ hJK hJK₀ hμ hμ₀
  obtain ⟨hLC, hSC, hT2, hB, hTG, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB; haveI := hTG
  haveI : μ.IsHaarMeasure := hμ.1
  haveI : μ₀.IsHaarMeasure := hμ₀.1

  have hfin : ∀ g : GA D V, ∃ x, Lev.finE V (ι x) = Lev.finE V g := by
    intro g
    obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g)
    have hk : k ∈ ι.range := by
      rw [hι]
      exact MonoidHom.mem_ker.2 k1
    obtain ⟨x, rfl⟩ := hk
    refine ⟨x, ?_⟩
    show Formalism.UG.bc (Lev.swapAE D) (finHom V (ι x)) = Formalism.UG.bc (Lev.swapAE D) (finHom V g)
    rw [k2]
  have hHH : K.comap (Lev.finE V) ≤ K₀.comap (Lev.finE V) := by
    intro g hg
    obtain ⟨x, hx⟩ := hfin g
    change Lev.finE V g ∈ K at hg
    show Lev.finE V g ∈ K₀
    rw [← hx] at hg ⊢
    exact (hJK₀ x).2 (hJ ((hJK x).1 hg))
  have e1 : J = K.comap ((Lev.finE V).comp ι) := by
    ext x
    exact (hJK x).symm
  have e2 : (J₀.map ι).map (Lev.finE V) = (K₀.comap (Lev.finE V)).map (Lev.finE V) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨ι x, (hJK₀ x).2 hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨x, hx⟩ := hfin g
      refine ⟨ι x, ⟨x, (hJK₀ x).1 ?_, rfl⟩, hx⟩
      rw [hx]
      exact hg
  have hidx : (K.comap (Lev.finE V)).relIndex (K₀.comap (Lev.finE V)) = J.relIndex J₀ := by
    rw [e1, Subgroup.relIndex_comap, Subgroup.relIndex_comap, ← Subgroup.map_map, e2]
  haveI : ((K.comap (Lev.finE V)).subgroupOf (K₀.comap (Lev.finE V))).FiniteIndex := ⟨hidx.trans_ne hJi⟩
  have hm := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ hHH hK.1.measurableSet μ
  rw [hidx, GlobalTheory.Mass.Levels.measure_comap_finE hμ, mul_one] at hm
  have h0 : μ₀ (K₀.comap (Lev.finE V)) = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ₀
  have heq := Measure.isMulLeftInvariant_eq_smul μ μ₀
  have hc : ((Measure.haarScalarFactor μ μ₀ : NNReal) : ENNReal) = (J.relIndex J₀ : ENNReal) := by
    have := congrArg (fun m : Measure (GA D V) => m ((K₀.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))) heq
    simp only [Measure.smul_apply, h0, ← hm] at this
    rw [this, ENNReal.smul_def, smul_eq_mul, mul_one]
  ext s hs
  rw [heq, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, hc]

end GlobalTheory.LevelIndexMeasure
