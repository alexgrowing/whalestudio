import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviBlockExponent

theorem pairChar_mul_twist (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (b' : Fin 2 → ℕ) (d : ℕ) (h : b' 0 + b' 1 = d) (μ : Fin 2 → kˣ →* ℂˣ) (ν : kˣ →* ℂˣ) :
    (GlobalTheory.SmGL.detChar (Fin d) ν).comp (leviEmb k (pairPlace b' h)) * pairChar k b' μ =
      pairChar k b' (fun i => μ i * ν) := by
  ext g
  simp [pairChar, detChar, det_leviEmb, Fin.prod_univ_two]
  ring

theorem twist_pairInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (b' : Fin 2 → ℕ) (d : ℕ) (h : b' 0 + b' 1 = d) (μ : Fin 2 → kˣ →* ℂˣ) (ν : kˣ →* ℂˣ),
    GlobalTheory.SmGL.IsSmoothChar ν →
    Nonempty ((GlobalTheory.SmGL.twist (GlobalTheory.LeviBlockExponent.pairInd k b' h μ) (GlobalTheory.SmGL.detChar (Fin d) ν)).Equiv
      (GlobalTheory.LeviBlockExponent.pairInd k b' h (fun i => μ i * ν))) := by
  intro k _ _ _ _ b' d h μ ν hν
  refine ⟨(GlobalTheory.LocGL.parIndTwistEquiv (pairPlace b' h) _ hν).trans (GlobalTheory.LocGL.parIndEquiv _ ?_)⟩
  rw [ofChar, twist_twist, ← ofChar, pairChar_mul_twist]
  exact .refl _

end GlobalTheory.LeviBlockExponent
