import Mathlib
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.SaturatedDuality
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.SaturatedPerpDuality

open NumberField

noncomputable section

namespace GlobalTheory.StepDualityCompare

open Formalism.MainNotions.S GlobalTheory.Count

theorem totallyComplex (I : AutInst) : IsTotallyComplex I.E := I.cm.cmUnram.1

theorem frm_det (I : AutInst) (x : I.GA) (w : InfinitePlace I.E) : IsUnit (frm I x w).det := by
  have hP : IsUnit (I.P (w.comap (algebraMap I.F I.E))).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit _)
  have hU : IsUnit (uMat (x.1 (w.comap (algebraMap I.F I.E)))).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  have hM : IsUnit (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))).det := by
    rw [Matrix.det_mul]
    exact hP.mul hU
  unfold frm
  split_ifs
  · exact hM
  · have e : ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))).map
        (starRingEnd ℂ)).det = starRingEnd ℂ
        (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))).det :=
      (RingHom.map_det _ _).symm
    rw [e]
    exact hM.map _

theorem least_pos (I : AutInst) (x : I.GA) (hfg : (lamX I x).FG) (h0 : lamX I x ≠ ⊥) : 0 < least I x := by
  have := totallyComplex I
  obtain ⟨-, -, -, h4, -⟩ := Formalism.HN.sizeMu I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) (frm_det I x)
    (lamX I x) hfg h0
  unfold least
  rw [h4]
  exact Real.exp_pos _

private theorem fg_of_le_lamX (I : AutInst) (x : I.GA) (hfg : (lamX I x).FG)
    {S : Submodule (𝓞 I.E) (Fin I.n → I.E)} (h : S ≤ lamX I x) : S.FG := by
  have : IsNoetherian (𝓞 I.E) (lamX I x) := isNoetherian_of_fg_of_noetherian _ hfg
  have : IsNoetherian (𝓞 I.E) S := isNoetherian_of_le h
  exact Module.Finite.iff_fg.mp inferInstance

theorem htQ_pos (I : AutInst) (x : I.GA) (hfg : (lamX I x).FG) (S S' : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn I x S) (hS' : S' ≤ lamX I x) (h : S ≤ S') :
    0 < Formalism.HN.htQ (bas I) (frm I x) S' S := by
  have := totallyComplex I
  obtain ⟨κ, _, _, b'', X'', hX'', -, hq⟩ := Formalism.HN.quotRealize I.E (Fin I.n → I.E) (Fin I.n) (bas I)
    (frm I x) (frm_det I x) (lamX I x) S hfg hS
  rw [(hq S' h hS').1]
  exact (Formalism.HN.plLat I.E _ κ b'' X'' hX'' _ ((fg_of_le_lamX I x hfg hS').map _)).2.2

theorem lamX_ne_bot (I : AutInst) (x : I.GA) (hn : 1 ≤ I.n)
    (h : ∀ S : Submodule (𝓞 I.E) (Fin I.n → I.E), GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn I x S →
      Formalism.HN.rkK (perpIn I x S) + Formalism.HN.rkK S = I.n) : lamX I x ≠ ⊥ := by
  intro hb
  have hsat : GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn I x ⊥ := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn Formalism.HN.IsSat Formalism.F.IsSaturated
    rw [hb]
    exact ⟨le_rfl, le_rfl, fun y hy _ => hy⟩
  have hz : Formalism.HN.rkK (⊥ : Submodule (𝓞 I.E) (Fin I.n → I.E)) = 0 := by
    unfold Formalism.HN.rkK
    rw [Submodule.bot_coe, Submodule.span_singleton_eq_bot.mpr rfl]
    simp
  have h1 := h ⊥ hsat
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.perpIn_bot, hb, hz] at h1
  omega

end GlobalTheory.StepDualityCompare
