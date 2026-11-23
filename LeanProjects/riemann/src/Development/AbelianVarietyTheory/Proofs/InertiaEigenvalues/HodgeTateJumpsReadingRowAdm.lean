import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducesWAndExistsEmb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalTwistDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmDecompIffDecompStatement

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.AdmReadBridge

set_option maxHeartbeats 1000000 in

theorem main : ∀ D : D7, AdmissibleParameterJ.AdmRead D := by
  intro D i r hr w hw C τ
  have hτ : ∀ x : D.host.E, AdmissibleParameterJ.gEmb C τ x =
      ((τ (Br.cEw D.nbr i w hw x) : ↥C.LL.1) : Om (D.nd.l i)) := fun x => rfl
  have emb := GlobalTheory.LocalEmbedding.inducesW_and_exists_emb D i w hw C.LL τ (AdmissibleParameterJ.gEmb C τ) hτ
  refine ⟨emb.1, emb.2, ?_⟩
  intro x dr dχ c hc
  have hχ : ∀ g, ((PairedCharacterCondition.chiGL i g : GL (Fin 1) (D.nd.O i)) : Matrix (Fin 1) (Fin 1) (D.nd.O i)) 0 0 =
      ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i) := by
    intro g
    simp [PairedCharacterCondition.chiGL]
  have tw := GlobalTheory.TwistRead.twist_dual_mult D i w hw (D.locT _) C.LL C.le τ (AdmissibleParameterJ.gEmb C τ) hτ r x
    (PairedCharacterCondition.chiGL i) c ((hr x).1) hχ dr dχ hc
  have jm : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (a : ℤ),
      (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a ↔
        multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a ≠ 0) := by
    intro k M a
    exact (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i))
      (D.locT _) (D.nbr i w hw).Kw C.LL (Fin k → ↥C.LL.1) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a).2.2
  refine ⟨fun a => ⟨(tw.2.2 a).1, ?_⟩, fun M _ a => jm M a, ?_⟩
  · have h := (tw.2.2 a).2
    rw [show c - a - 1 = c - 1 - a by ring] at h
    exact h
  · intro ρπ _ hd a
    have hd' := (GlobalTheory.T.admDecomp_iff_decomp D i r ρπ x).1 hd
    have hw' := ((GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρπ x hd').2 tw.1).2.2 τ a
    exact ⟨hw'.1, hw'.2, jm _ a, jm _ a⟩

end GlobalTheory.AdmReadBridge
