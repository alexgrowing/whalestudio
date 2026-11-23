import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.GJReg

theorem kInd_mem_SB_and_gjZ_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (s : ℂ), IsUnram ν →
    kInd k n ∈ SB (Matrix (Fin n) (Fin n) k) ∧ gjZ ν s (kInd k n) = 1 := by
  intro k _ _ _ _ _ _ n ν s hν
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hS : {X : Matrix (Fin n) (Fin n) k | ∃ g ∈ KO k (Fin n), g.val = X} = Units.val '' (KO k (Fin n) : Set _) := by
    ext X; simp [eq_comm]
  have hrange : IsOpen (Set.range (fun g : GL (Fin n) k => g.val)) := by
    have : Set.range (fun g : GL (Fin n) k => g.val) = {X : Matrix (Fin n) (Fin n) k | X.det ≠ 0} := by
      ext X
      simp only [Set.mem_range, Set.mem_setOf_eq]
      constructor
      · rintro ⟨g, rfl⟩; exact g.det_ne_zero
      · intro h; exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero X h, rfl⟩
    rw [this]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  have hoe : Topology.IsOpenEmbedding (fun g : GL (Fin n) k => g.val) :=
    ⟨isEmbedding_val_GL, hrange⟩
  have hc : IsCompact (Units.val '' (KO k (Fin n) : Set (GL (Fin n) k))) :=
    isCompact_KO.image Units.continuous_val
  have ho : IsOpen (Units.val '' (KO k (Fin n) : Set (GL (Fin n) k))) := hoe.isOpenMap _ isOpen_KO
  refine ⟨?_, ?_⟩
  · unfold kInd
    rw [hS]
    have hK : IsClopen (Units.val '' (KO k (Fin n) : Set (GL (Fin n) k))) := ⟨hc.isClosed, ho⟩
    exact ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant,
      HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  · unfold gjZ
    have hf : (fun g : GL (Fin n) k => kInd k n g.val * (ν (gdet g) : ℂ) * apow (gdet g) s) =
        (KO k (Fin n) : Set (GL (Fin n) k)).indicator (fun _ => (1 : ℂ)) := by
      funext g
      by_cases hg : g ∈ KO k (Fin n)
      · have h1 : kInd k n g.val = 1 := Set.indicator_of_mem (show g.val ∈ {X : Matrix (Fin n) (Fin n) k | ∃ g ∈ KO k (Fin n), g.val = X} from ⟨g, hg, rfl⟩) _
        have h2 := chiS_of_mem_KO hν s hg
        unfold chiS at h2
        rw [Set.indicator_of_mem (show g ∈ (KO k (Fin n) : Set (GL (Fin n) k)) from hg), h1, one_mul, h2]
      · have h1 : kInd k n g.val = 0 := by
          refine Set.indicator_of_notMem ?_ _
          rintro ⟨h, hh, he⟩
          exact hg (by rwa [show h = g from Units.ext he] at hh)
        rw [Set.indicator_of_notMem (show g ∉ (KO k (Fin n) : Set (GL (Fin n) k)) from hg), h1]
        simp
    rw [hf, integral_indicator_const _ isOpen_KO.measurableSet, measureReal_def,
      haarVol_self isOpen_KO le_rfl]
    simp

end GlobalTheory.GJReg
