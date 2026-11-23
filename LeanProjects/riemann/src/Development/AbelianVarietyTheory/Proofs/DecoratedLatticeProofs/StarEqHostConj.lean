import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.I0M
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RankOneLine

theorem star_eq_hostConj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

def negLine (D : D7) : HSp D :=
  Formalism.BasicNotions.Examples₂.stdSpace Formalism.BasicNotions.Examples₂.star_isIntegral 1 (fun _ => true) 0 1

theorem negLine_rank (D : D7) : (negLine D).rank = 1 := rfl

theorem negLine_gram (D : D7) : ∀ i j, (negLine D).gram i j = -1 := by
  show ∀ i j : Fin 1, (Formalism.BasicNotions.Examples₂.stdSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral 1
    (fun _ => true) 0 1).gram i j = -1
  intro i j
  rw [Formalism.BasicNotions.Examples₂.stdSpace_gram_apply, Subsingleton.elim i j]
  simp [Formalism.BasicNotions.Examples₂.sgn]

theorem exists_line (D : D7) (X : HidaSetting D) (u : D.what₂.Word) :
    ∃ (L : HSp D) (s : D.host.E), s ≠ 0 ∧ L.rank = 1 ∧ (VS D).hT (X.zu u) (X.zu u) ≠ 0 ∧
      ∀ i j, L.gram i j = star s * s * (VS D).hT (X.zu u) (X.zu u) := by
  obtain ⟨π, -, hπ, -⟩ := D.T_norm u
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have hπ0 : ((π : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h; apply hT0; rw [← hπ, h, zero_mul]
  have hc0 : D.host.conj (π : D.host.E) ≠ 0 := by
    intro h; apply hT0; rw [← hπ, h, mul_zero]
  refine ⟨negLine D, ((π : 𝓞 D.host.E) : D.host.E)⁻¹, inv_ne_zero hπ0, rfl, ?_, fun i j => ?_⟩
  · rw [X.zu_norm]; exact neg_ne_zero.2 hT0
  · rw [negLine_gram, X.zu_norm, star_inv₀, star_eq_hostConj, ← hπ]
    field_simp <;> ring

end GlobalTheory.RankOneLine
