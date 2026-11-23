import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCsdOfCharOfRes
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem inf_mu_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ),
    IsMu μ e → ∀ k : Eˣ, ((μ.inf k : ℂˣ) : ℂ) = ∏ v : InfinitePlace E, (v.embedding (k : E) / (‖v.embedding (k : E)‖ : ℂ)) ^ e v := by
  intro E _ _ _ μ e hμ k
  have h1 : μ.inf k = chiInf μ (Units.map (GlobalTheory.CuspRep.pInf E).toMonoidHom (Neutral.B1.diagUnits E k)) := by
    rw [chiInf, MonoidHom.comp_apply, GlobalTheory.CuspRep.NormTriv.infId_pInf]
    change μ.1 (Formalism.L2.Host.infDiag k) = _
    rw [Formalism.L2.Host.infDiag, MonoidHom.finsetProd_apply]
    rfl
  rw [h1, hμ.2.2.2.2]
  refine Finset.prod_congr rfl fun v _ => ?_
  have : (Units.map (GlobalTheory.CuspRep.pInf E).toMonoidHom (Neutral.B1.diagUnits E k)).1 v = v.embedding (k : E) :=
    GlobalTheory.CuspRep.pInf_algebraMap (k : E) v
  rw [this]

end GlobalTheory.BCT
