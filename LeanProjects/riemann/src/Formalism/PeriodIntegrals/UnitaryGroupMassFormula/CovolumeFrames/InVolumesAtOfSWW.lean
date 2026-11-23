import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcWeil
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepFrameStd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd

noncomputable section

namespace MassDataVolumesW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Volumes
  Formalism.L2.SG.Measures Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory
open scoped TensorProduct

section GenW

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}
  {J : Matrix (Fin M) (Fin M) E}

theorem covol_eq_covolBy_w (hV : Formalism.L2.SG.Pf.NcWeil.VolStabW F E σ M J) (hJ : IsHermND σ J) {a : ℕ}
    (ha : 1 ≤ a) (haM : 2 * a < M) (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j)
    (hdet : (gramE σ J X0).det ≠ 0) {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    {μ : Measure (HA (AF F) σ J)} (hμ : IsHaarH F E σ M J μ)
    {νX : Measure (Fin a → Fin M → AF F ⊗[F] E)} (hν : IsOmT F E σ M J ψ (gramE σ J X0) hT νX)
    {μ' : Measure (stabT (AF F) σ J X0)} (hμ' : μ'.IsHaarMeasure)
    (hc : IsCompatT F E σ M J X0 μ μ' νX) :
    covol μ' = covolBy (G := HA (AF F) σ J) (HFinIn (AF F) σ J) μ := by
  have hA := hV hJ a ha haM X0 hT hdet
  unfold Formalism.L2.SG.Volumes.VolStabAt AllSome at hA
  have hB := (((hA.2 ψ hψ).2 μ hμ).2 νX hν).2 μ' ⟨hμ', hc⟩
  obtain ⟨G, hG⟩ := hB.1
  obtain ⟨G', hG'⟩ := (hB.2 G hG).1
  have hex : ∃ 𝓕 : Set (HA (AF F) σ J), IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ := ⟨G, hG⟩
  have hr : ratIn F E σ M J (stabT (AF F) σ J X0) = ratOf (K := stabT (AF F) σ J X0) := by
    ext x
    show x ∈ ((HFinIn (AF F) σ J) ⊓ stabT (AF F) σ J X0).subgroupOf (stabT (AF F) σ J X0) ↔
      x ∈ (HFinIn (AF F) σ J).comap (stabT (AF F) σ J X0).subtype
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  have hex' : ∃ 𝓕 : Set (stabT (AF F) σ J X0),
      IsFundamentalDomain (ratOf (K := stabT (AF F) σ J X0)) 𝓕 μ' := ⟨G', by rw [← hr]; exact hG'⟩
  simp only [covol, covolBy, dif_pos hex, dif_pos hex']
  split_ifs with h
  · exact congrArg ENNReal.toReal ((hB.2 h.choose h.choose_spec).2 hex'.choose
      (by rw [hr]; exact hex'.choose_spec))
  · exact (h ⟨G, hG⟩).elim

end GenW

theorem stepSizeW : ∀ {D : D7} (X : HidaSetting D), 4 * D.R.rS + 5 ≤ X.B.I.n := by
  intro D X
  rw [X.n_eq]
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

def SWXW : Prop := ∀ {D : D7} (X : HidaSetting D),
  Formalism.MainNotions.UnusedSlot34.SWa1 X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ∧
    Formalism.L2.SG.Pf.NcWeil.SWc1W X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J

theorem inVolumesAt_of_w
    (hV : ∀ {D : D7} (X : HidaSetting D),
      Formalism.L2.SG.Pf.NcWeil.VolStabW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J)
    (hG : StepGramH) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InVolumesAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A
  intro _hX ψ hψ hT1 νH hνH hcH hT1' νH' hνH' hcH' hTB νB hdet hνB hcB hN hN'
  have hs := stepSizeW X
  have hn := X.measG_norm
  have eB := covol_eq_covolBy_w (hV X) (stepHerm X) (a := 2 * D.R.rS + 2) (by omega) (by omega) X0 hTB
    hdet hψ hn.1 hνB (hn.2.2.2.2.1 X0) hcB
  have eH := covol_eq_covolBy_w (hV X) (stepHerm X) (a := D.R.rS + 1 + D.R.rS) (by omega) (by omega) _
    hT1 (hG X u hT1) hψ hn.1 hνH (X.measW_norm u).1 hcH
  have eH' := covol_eq_covolBy_w (hV X) (stepHerm X) (a := D.R.rS + 1 + D.R.rS) (by omega) (by omega) _
    hT1' (hG X u' hT1') hψ hn.1 hνH' (X.measW_norm u').1 hcH'
  refine ⟨?_, hN, hN'⟩
  show covol (X.measG.μB X0) * covolBy (G := HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)
      (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) X.measG.μG =
    covol (X.measW u).μH * covol (X.measW u').μH
  rw [eB]
  exact (congrArg₂ (· * ·) eH eH').symm

end MassDataVolumesW
