import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EvalConvGroupAlg
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
open Formalism.BasicNotions Formalism.L2.SG.RowDict Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting MeasureTheory
open scoped Classical

noncomputable section

namespace GlobalTheory.Mem.GoodExpand

theorem eg_eq_step {D : D7} (X : HidaSetting D) {red : X.B.I.Gf → G0g D.nd} (hr : IsRedHom X red) :
    eg X = fun x => if x ∈ X.B.I.Kset then D.ntypes.e0.coeff (red x) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0 := by
  funext x
  unfold eg
  by_cases hx : x ∈ X.B.I.Kset
  · have hex : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ := ⟨hx, red x, hr.1 x hx⟩
    rw [dif_pos hex, if_pos hx,
      Formalism.L2.SG.Pf.rowDictEgWellDef_holds X x _ _ (Classical.choose_spec hex.2) (hr.1 x hx)]
  · rw [dif_neg (fun h => hx h.1), if_neg hx]

theorem rg_expand : ∀ (D : D7) (X : HidaSetting D) (G : GoodOp X) [Fintype (G0g D.nd)] (red : X.B.I.Gf → G0g D.nd) (s : G0g D.nd → X.B.I.Gf), IsRedHom X red → (∀ γ, s γ ∈ X.B.I.Kset ∧ red (s γ) = γ) → ∀ φ : L2X X, (∀ k ∈ X.B.I.Kg X.B.g, X.B.R (1, k) φ = φ) → G.Rg φ = ∑ γ, D.ntypes.e0.coeff γ • X.B.R (1, s γ) φ := by
  intro D X G _ red s hr hs φ hφ
  have hT := G.Rg_spec
  rw [eg_eq_step X hr] at hT
  refine GlobalTheory.Mem.SRe.ConvStep.top_expand X hr s hs (fun γ => D.ntypes.e0.coeff γ) G.Rg hT φ ?_
  intro k hk
  have hsk := (hs (red k)).1
  have hk' : (s (red k))⁻¹ * k ∈ X.B.I.Kg X.B.g :=
    (GlobalTheory.Mem.SRe.ConvStep.fibre_iff X hr hsk k).1 ⟨hk, ((hs (red k)).2).symm⟩
  have hmul := (GlobalTheory.RightRegFund.rightReg_unitary_continuous X.B).2.1
  have e : ((1, k) : X.B.I.GA) = (1, s (red k)) * (1, (s (red k))⁻¹ * k) := by
    ext
    · simp
    · simp
  rw [e, hmul]
  show X.B.R (1, s (red k)) (X.B.R (1, (s (red k))⁻¹ * k) φ) = _
  rw [hφ _ hk']

end GlobalTheory.Mem.GoodExpand
