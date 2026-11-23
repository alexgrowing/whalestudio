import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsExtra

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

namespace GlobalTheory.Twist.SmoothLine

theorem finprod_add_of_at {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) (x z : κ → AF F) (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evI F) z) :
    (∏ᶠ v, φ v fun i => evFin F v ((x + z) i)) = ∏ᶠ v, φ v fun i => evFin F v (x i) := by
  refine finprod_congr fun v => ?_
  have hv : (fun i => evFin F v ((x + z) i)) = fun i => evFin F v (x i) := by
    funext i
    rw [Pi.add_apply, map_add, GlobalTheory.ThK.EvUniqInf.evFin_eq_zero_of_at z hz v i, add_zero]
  rw [hv]

private theorem eq_of_pure_eq_twisted_operators {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ)
    (hne : ∃ y : κ → AF F, ∏ᶠ v, φ v (fun i => evFin F v (y i)) ≠ 0)
    (g g' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' φ) : g = g' := by
  obtain ⟨y, hy⟩ := hne
  ext a
  let z : κ → AF F := fun i =>
    (LinearMap.inl F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i - evI F (y i))) : AF F)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evI F) z := by
    intro u hu
    have hu1 : u.1 = 0 := by
      have hu' : InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
      exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp hu'
    funext i
    show u * z i = 0
    apply Prod.ext
    · show u.1 * (z i).1 = 0
      rw [hu1, zero_mul]
    · show u.2 * 0 = 0
      exact mul_zero _
  have hev : (fun i => evI F ((y + z) i)) = a := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((y i).1 + (z i).1) = a i
    rw [map_add]
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1 + InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i - evI F (y i))) = a i
    rw [RingEquiv.apply_symm_apply]
    show evI F (y i) + (a i - evI F (y i)) = a i
    abel
  have h1 : g (fun i => evI F ((y + z) i)) * (∏ᶠ v, φ v fun i => evFin F v ((y + z) i)) =
      g' (fun i => evI F ((y + z) i)) * (∏ᶠ v, φ v fun i => evFin F v ((y + z) i)) := congrFun h (y + z)
  rw [finprod_add_of_at φ y z hz, hev] at h1
  exact mul_right_cancel₀ hy h1

theorem smooth_line_pure : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    (∃ y : Fin n × Fin d → AF F, ∏ᶠ v, φ v (fun i => evFin F v (y i)) ≠ 0) →
    ∀ c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      (∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ) →
      ∃ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hCM hψ hG hW γ hγ f φ hSB hfin hne c hc
  obtain ⟨c', g, hc0, hlim, hact⟩ :=
    GlobalTheory.WeilArchSmooth.exists_orbit hP M ψ χX χW om hCM hψ hW γ hγ f
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hfin, hG.std] with v h1 h2
    rw [h1, h2]
  have hR := GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd

  have hsame : ∀ t, c t = c' t := by
    intro t
    have hpure : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c' t) φ := by
      rw [← hc t]
      exact hact t _ hR
    exact eq_of_pure_eq_twisted_operators φ hne _ _ hpure
  refine ⟨g, ?_⟩
  have hfun : (fun t : ℝ => t⁻¹ • (c t - c 0)) = fun t : ℝ => t⁻¹ • (c' t - f) := by
    funext t
    rw [hsame t, hsame 0, hc0]
  rw [hfun]
  exact hlim

end GlobalTheory.Twist.SmoothLine
