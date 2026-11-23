import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.CoefInt

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem continuous_psiN (d : BesselDatum A B ι) {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) :
    Continuous (d.psiN ψ) := by
  have i0 : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  have i1 : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have hm : Continuous (mt B) := Units.continuous_val.comp continuous_subtype_val
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have ha : ∀ v, Continuous fun g => actV B g v := fun v => hm.matrix_mulVec continuous_const
  refine hψ.comp (ht.comp (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)))
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    continuous_const.mul ((continuous_apply b).comp (ha _))

def FlagCocompact : Prop :=
  ∀ (D : D7) (B : HSp D) (ρ : ℕ) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E), IsIsoSub B e →
    ∃ K : Set (NFlag B e), IsCompact K ∧ ∀ n, ∃ γ ∈ NFlagQ B e, ∃ k ∈ K, n = γ * k

theorem exists_compact (H : FlagCocompact) (d : BesselDatum A B ι) :
    ∃ K : Set (GA D B), IsCompact K ∧ ∀ n ∈ d.N, ∃ γ ∈ GQ B, ∃ k ∈ K, n = γ * k := by
  obtain ⟨K, hK, h⟩ := H D B _ (GlobalTheory.BesselCompare.toBes d).e (GlobalTheory.BesselCompare.toBes d).e_iso
  have hN := (GlobalTheory.BesselCompare.same_toBes d).2.2.1
  refine ⟨Subtype.val '' K, hK.image continuous_subtype_val, fun n hn => ?_⟩
  obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨n, hN ▸ hn⟩
  exact ⟨γ, hγ, k, ⟨k, hk, rfl⟩, congrArg Subtype.val e⟩

theorem coeff_integrable_continuous_of (H : FlagCocompact) : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → ∀ F : GA D B → ℂ, Continuous F → (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → (∀ g, IntegrableOn (fun n : d.N => F ((n : GA D B) * g) * star (d.psiN ψ (n : GA D B))) 𝓝 ν) ∧ Continuous (d.coeff ψ ν 𝓝 F) ∧ ∀ C : Set (GA D B), IsCompact C → ∃ M : ℝ, ∀ n ∈ d.N, ∀ g ∈ C, ‖F (n * g)‖ ≤ M := by
  intro D A B ι d ψ hψ ν 𝓝 hν F hF hinv
  obtain ⟨b1, b2, b3, b4, b5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hbd : ∀ C : Set (GA D B), IsCompact C → ∃ M : ℝ, ∀ n ∈ d.N, ∀ g ∈ C, ‖F (n * g)‖ ≤ M := by
    intro C hC
    obtain ⟨K, hK, h⟩ := exists_compact H d
    obtain ⟨M, hM⟩ := (hK.mul hC).exists_bound_of_continuousOn hF.continuousOn
    refine ⟨M, fun n hn g hg => ?_⟩
    obtain ⟨γ, hγ, k, hk, rfl⟩ := h n hn
    rw [mul_assoc, hinv γ hγ]
    exact hM _ (Set.mul_mem_mul hk hg)
  have hfin : ν 𝓝 ≠ ⊤ := by rw [hν.2.2]; exact ENNReal.one_ne_top
  have : SecondCountableTopology d.N := TopologicalSpace.Subtype.secondCountableTopology _
  have hχ : Continuous fun n : d.N => star (d.psiN ψ (n : GA D B)) :=
    ((continuous_psiN d hψ.1).comp continuous_subtype_val).star
  have hc : ∀ g, Continuous fun n : d.N => F ((n : GA D B) * g) * star (d.psiN ψ (n : GA D B)) := fun g =>
    (hF.comp (continuous_subtype_val.mul continuous_const)).mul hχ
  have hn : ∀ g (n : d.N), ‖F ((n : GA D B) * g) * star (d.psiN ψ (n : GA D B))‖ = ‖F ((n : GA D B) * g)‖ :=
    fun g n => by rw [norm_mul, norm_star, BesselDatum.psiN, hψ.2.1, mul_one]
  refine ⟨fun g => ?_, ?_, hbd⟩
  · obtain ⟨M, hM⟩ := hbd {g} isCompact_singleton
    exact Measure.integrableOn_of_bounded (M := M) hfin (hc g).measurable.aestronglyMeasurable
      (.of_forall fun n => (hn g n).trans_le (hM n n.2 g rfl))
  · refine continuous_iff_continuousAt.2 fun g => ?_
    obtain ⟨C, hC, hCg⟩ := exists_compact_mem_nhds g
    obtain ⟨M, hM⟩ := hbd C hC
    have : IsFiniteMeasure (ν.restrict 𝓝) := isFiniteMeasure_restrict.2 hfin
    refine continuousAt_of_dominated (bound := fun _ => M)
      (.of_forall fun x => (hc x).measurable.aestronglyMeasurable) ?_ (integrable_const M)
      (.of_forall fun n => ?_)
    · filter_upwards [hCg] with x hx
      exact .of_forall fun n => (hn x n).trans_le (hM n n.2 x hx)
    · exact ((hF.comp (continuous_const.mul continuous_id)).mul continuous_const).continuousAt

end GlobalTheory.RootExch.CoefInt
