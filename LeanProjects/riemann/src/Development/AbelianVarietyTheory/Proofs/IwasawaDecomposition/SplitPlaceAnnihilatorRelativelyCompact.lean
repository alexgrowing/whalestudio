import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct RestrictedProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitAnnihilator

open GlobalTheory.IdemModTwo

open Classical in

theorem continuous_singleV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (singleV F v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem trace_split {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} (he : SplitAt D v e)
    (x y : Fv D.host.F v) :
    Algebra.trace (AF D.host.F) (AE D) (fj D (singleV D.host.F v x) * e * (fj D (singleV D.host.F v y) * e)) =
      pairA D.host.F 0 (singleV D.host.F v (x * y)) := by
  have h1 : fj D (singleV D.host.F v x) * e * (fj D (singleV D.host.F v y) * e) =
      fj D (singleV D.host.F v (x * y)) * e := by
    rw [mul_mul_mul_comm, he.1, ← map_mul, singleV_mul, GlobalTheory.SplitIdem.evalV_singleV_same]
  have h2 := GlobalTheory.FockCompare.SymplVal.trace_AE D (fj D (singleV D.host.F v (x * y)) * e)
  rw [map_mul (cA D), cA_fj, ← mul_add, he.2.2, ← map_mul (fj D), singleV_mul, GlobalTheory.SplitIdem.evalV_singleV_same, mul_one] at h2
  rw [h1]
  exact tmul_one_inj (F := D.host.F) (E := D.host.E) h2

theorem annihilator_subset_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1) → ∀ ε : AE D, IsSplitIdem D ε → ∀ V ∈ nhds (0 : AE D), ∃ C : Set (AE D), IsCompact C ∧ ∀ a, ε * a = a → (∀ s ∈ V, ε * s = s → ψ (Algebra.trace (AF D.host.F) (AE D) (a * s)) = 1) → a ∈ C := by
  intro D ψ hψ e hε V hV
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 hε
  obtain ⟨y, hy⟩ := hψ v
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : ProperSpace (Fv D.host.F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion D.host.F v
  let j : Fv D.host.F v → AE D := fun x => fj D (singleV D.host.F v x) * e
  have hj : Continuous j := by
    have h1 : Continuous (algebraMap (AF D.host.F) (AE D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))
    have h2 : Continuous fun x : Fv D.host.F v => pairA D.host.F 0 (singleV D.host.F v x) :=
      Continuous.prodMk continuous_const (continuous_singleV D.host.F v)
    exact (h1.comp h2).mul continuous_const
  have hj0 : j 0 = 0 := by
    have h0 : singleV D.host.F v 0 = 0 := by
      rw [← sub_self (0 : Fv D.host.F v), singleV_sub, sub_self]
    simp only [j, h0, map_zero, zero_mul]
  have hV' : j ⁻¹' V ∈ nhds (0 : Fv D.host.F v) := hj.continuousAt.preimage_mem_nhds (by rwa [hj0])
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hV'
  refine ⟨j '' Metric.closedBall 0 (‖y‖ / r), (isCompact_closedBall _ _).image hj, fun a ha hs => ?_⟩
  obtain ⟨x, hx⟩ := he.exists_scalar a
  rw [ha] at hx
  refine ⟨x, ?_, hx.symm⟩
  by_contra hn
  rw [mem_closedBall_zero_iff, not_le] at hn
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hr.le) hn
  have hx0 : x ≠ 0 := norm_pos_iff.1 hxpos
  have hmem : y / x ∈ Metric.ball (0 : Fv D.host.F v) r := by
    rw [mem_ball_zero_iff, norm_div, div_lt_iff₀ hxpos]
    rw [div_lt_iff₀ hr] at hn
    linarith
  have h := hs (j (y / x)) (hball hmem) (by
    show e * (_ * e) = _ * e
    rw [mul_left_comm, he.1])
  rw [hx] at h
  change ψ (Algebra.trace _ _ (_ * (_ * e))) = 1 at h
  rw [trace_split he, mul_div_cancel₀ _ hx0] at h
  exact hy h

end GlobalTheory.SplitAnnihilator

end
