import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormTransp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecomp
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds

noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace Formalism.L2.SG.Pf.FormRelPf

def ofPts {K : Type} {i : ℕ} (s : Σ c : Composition (i + 1), (Fin c.length → K)) : List (K × ℕ) :=
  List.ofFn fun a => (s.2 a, s.1.blocksFun a)

theorem ofPts_toPts {K : Type} [Zero K] {i : ℕ} (p : Point K (i + 1)) : ofPts (toPts p) = p.1 := by
  apply List.ext_get
  · simp [ofPts, toPts, Composition.length]
  · intro n h1 h2
    simp [ofPts, toPts, Composition.blocksFun]

theorem toPts_injective {K : Type} [Zero K] {i : ℕ} :
    Function.Injective (toPts : Point K (i + 1) → Σ c : Composition (i + 1), (Fin c.length → K)) := by
  intro p q h
  apply Subtype.ext
  rw [← ofPts_toPts p, ← ofPts_toPts q, h]

end Formalism.L2.SG.Pf.FormRelPf

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.FormRel Formalism.L2.SG.Pf.FormRelPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem formRelC_of (hRD : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.Pf.RowForm.RealDecompC X Y u u')
    (hRC : Formalism.L2.SG.Pf.RelCharC) : FormRelC := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ ν hν t ht hv => ?_⟩
  have hG : t.G ≠ 0 := Formalism.L2.SG.Pf.RowForm.realDecomp_G_ne X Y u u' t ht
  have hrel : t.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := Formalism.L2.SG.TermOp.Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t hr
    show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨hpt, hall⟩ := hRD D X Y u u' t hrel hG
  refine ⟨⟨_, rfl, hpt⟩, fun w hw hwr => ?_⟩
  have hw' : w = Formalism.L2.SG.PairVal.ptOf t.toTerm := toPts_injective hw
  subst hw'
  have hγ := Formalism.L2.SG.Pf.RowForm.isPtRep_gamW X u u' hwr
  obtain ⟨g, hg, g', hg', hdec⟩ := hall _ hγ
  obtain ⟨c, hc⟩ := formTransp_any (X := X) (Y := Y) (u := u) (u' := u') (νq := ν) hν.2 hRC t hrel hwr g hg g' hg'
    hdec
  have := FiniteDimensional.complete ℂ (X.Vpi u)
  have := FiniteDimensional.complete ℂ (X.Vpi u')
  refine ⟨(c : ℂ) * (X.psiInfU u g * conj (X.psiInfU u' g')),
    ((Formalism.L2.SG.RealObj.InfCut.piIso X u g hg).toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u),
    ((Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg').symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u'), ?_⟩
  rw [hc, hdec, Formalism.L2.SG.Pf.RowForm.ClassFrameNormal.oo_map_mulLeft _ _ _ _ g g' (X.psiInfU u g) (X.psiInfU u' g')
    (Formalism.L2.SG.RealObj.InfCut.piIso X u g hg) (Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg')
    (fun x => (X.Wu_spec u).1 g hg x) (fun x => (X.Wu_spec u').1 g' hg' x), ← Complex.coe_smul, smul_smul]

end Formalism.L2.SG.Pf
