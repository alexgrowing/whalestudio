import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealQuotientVolumeGrowthOfScalarHypotheses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMeasLevW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPublished
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop

open MeasureTheory Formalism.L2.Theta
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MassFullLevel

theorem levW_le {D : D7} {Tu : Type} (Cl : LevCh D Tu) (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) :=
  fun _ hx => ⟨hx.1, Subgroup.mem_top _⟩

theorem relIndex_ne_zero {D : D7} {Tu : Type} (Cl : LevCh D Tu) (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P).relIndex (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) ≠ 0 := by
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full _ _ _) = parLev D.sp.cm (Wc D i).gram (Cl.βW i) (Cl.datWp i P) := by
    have e : Cl.datWp i (LevelP.full _ _ _) = { Cl.datWp i P with P := LevelP.full (Cl.datWp i P).Pg (Cl.datWp i P).r ℂ } := by
      simp only [LevCh.datWp, Formalism.IndefR.Lev.datY, if_true]
    rw [← GlobalTheory.CovTop.LevelIndex.lev_full, ← e]
  exact (GlobalTheory.CovTop.LevelIndex.relIndex_lev_le D.sp.cm (Wc D i).gram (Cl.βW i) (Cl.datWp i P) _ hB).1

theorem mass_le_of_full : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P) μ 𝓕 → ∃ μ' : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i)), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) μ' 𝓕 ∧ μ' 𝓕 ≤ μ 𝓕 := by
  intro D Tu Cl t0 _ i P μ 𝓕 hμ
  obtain ⟨ν, hν⟩ := GlobalTheory.LevelMeasure.exists_isMeasLev D (Wc D i) (Cl.βW i) (Cl.datWp i (LevelP.full Cl.Pg D.R.r ℂ))
    (D.sp.W_sig ((i : ℕ) + 1))
  have hne := relIndex_ne_zero Cl i P
  have hmeas : MeasurableSet {g : GA D (Wc D i) | Formalism.IndefR.Lev.finE (Wc D i) g ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P} := by
    haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
    exact (GlobalTheory.ParahoricCompact.isOpen_comap_lev (Wc D i) (Cl.βW i) (Cl.datWp i P)).measurableSet
  have e := GlobalTheory.ChainTw.VolScale.scale (Wc D i) (fun _ m => Formalism.IndefR.Lev.IsMinf m) (fun _ _ h => h.1) _ _ μ ν
    (levW_le Cl i P) Formalism.L2.DIV.lev_le_UA hne hmeas hμ.1 hν
  set n : ℝ≥0∞ := ((GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P).relIndex (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) : ℝ≥0∞)
    with hn
  have hn0 : n ≠ 0 := by rw [hn]; exact_mod_cast hne
  have hnt : n ≠ ⊤ := ENNReal.natCast_ne_top _
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
  have eν : ν = n⁻¹ • μ := by
    rw [e, smul_smul, ENNReal.inv_mul_cancel hn0 hnt, one_smul]
  refine ⟨ν, ⟨hν, ?_⟩, ?_⟩
  · rw [eν]; exact hμ.2.mono Measure.smul_absolutelyContinuous
  · rw [e, Measure.smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left bot_le hn1

end GlobalTheory.MassFullLevel
