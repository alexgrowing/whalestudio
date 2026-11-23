import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem l2_limit_eq_pointwise_limit : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (a : ℕ → Mat n → V) (b : Mat n → V) (x : Lp V 2 μ), (∀ k, MemLp (fun y : G n => a k y.val) 2 μ) → Tendsto (fun k => cls μ (a k)) atTop (𝓝 x) → (∀ z ∈ GLs n, Tendsto (fun k => a k z) atTop (𝓝 (b z))) → MemLp (fun y : G n => b y.val) 2 μ ∧ cls μ b = x := by
  intro n _ _ μ _ V _ _ _ a b x hm hc hp
  have hin : TendstoInMeasure μ (fun k => (cls μ (a k) : G n → V)) atTop (x : G n → V) :=
    tendstoInMeasure_of_tendsto_Lp hc
  obtain ⟨ns, hns, hae⟩ := hin.exists_seq_tendsto_ae
  have hall : ∀ᵐ y ∂μ, ∀ k, (cls μ (a k) : G n → V) y = a k y.val :=
    ae_all_iff.2 fun k => coe_cls μ (hm k)
  have hbx : (fun y : G n => b y.val) =ᵐ[μ] x := by
    filter_upwards [hae, hall] with y h1 h2
    have hy : y.val ∈ GLs n := by
      have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
      exact hu.ne_zero
    have h3 : Tendsto (fun k => a (ns k) y.val) atTop (𝓝 (b y.val)) :=
      (hp y.val hy).comp hns.tendsto_atTop
    have h4 : Tendsto (fun k => a (ns k) y.val) atTop (𝓝 (x y)) := by
      simpa only [h2] using h1
    exact tendsto_nhds_unique h3 h4
  exact cls_of_ae μ hbx

end GlobalTheory.CompanionTheory.PresSobA
