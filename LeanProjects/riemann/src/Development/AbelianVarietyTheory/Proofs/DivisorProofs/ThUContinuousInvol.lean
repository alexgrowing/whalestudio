import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSrcMemOrb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

theorem continuous_prjG (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (T : Finset (Pl E)) :
    Continuous (prjG E n T) := by
  have hc : Continuous (prjM E n T) := by
    show Continuous fun M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) =>
      idem E T • M + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))
    exact (continuous_id.const_smul (idem E T)).add
      (continuous_const (y := (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))))
  exact Continuous.units_map (prjM E n T) hc

theorem thU_continuous_invol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : Pl E),
    Continuous (GlobalTheory.EulerTw.thU E n u) ∧ ∀ g, GlobalTheory.EulerTw.thU E n u (GlobalTheory.EulerTw.thU E n u g) = g := by
  intro E _ _ _ n u
  refine ⟨?_, fun g => Subtype.ext ?_⟩
  · have hT : Continuous (thF E n) := GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)
    exact (((continuous_prjG E n (orb E u)).comp hT).comp continuous_subtype_val).subtype_mk _
  · rw [Comm.thU_val, Comm.thU_val, Comm.thF_thF]

end GlobalTheory.EulerTw
