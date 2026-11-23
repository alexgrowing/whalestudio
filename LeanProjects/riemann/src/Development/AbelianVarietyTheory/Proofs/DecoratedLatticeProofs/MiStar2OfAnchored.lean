import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

namespace GlobalTheory.MiTop

theorem miStar2_of_anchored : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ) (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ), OpsUnit X V U → Anchored X eV sEE V U c → UnitAt X c → X.MIstar2 eV sEE := by
  intro K _ _ _ Bs A X fc eV sEE V U c hOp hAn hUn
  choose p b hp hb hid using hAn
  refine ⟨⟨V, fun u => p u / (b u * c u Bs.μ0), U, fun u t => c u t / c u Bs.μ0⟩, ?_, ?_, ?_⟩
  · refine ⟨hOp.1, hOp.2, ⟨fun u t => div_ne_zero (hUn.1 u t) (hUn.1 u Bs.μ0), fun u w k hk => hUn.2 u w k hk⟩,
      fun u => div_self (hUn.1 u Bs.μ0)⟩
  · intro u t φ F
    have h := hid u t φ F
    have hc := hUn.1 u Bs.μ0
    have hbu := hb u
    dsimp only
    field_simp
    linear_combination h
  · intro u
    exact div_ne_zero (hp u) (mul_ne_zero (hb u) (hUn.1 u Bs.μ0))

end GlobalTheory.MiTop
