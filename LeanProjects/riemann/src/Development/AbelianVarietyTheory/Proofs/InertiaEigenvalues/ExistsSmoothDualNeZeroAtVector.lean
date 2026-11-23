import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.SmoothForm

theorem exists_smooth_form_ne_zero : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsSmooth ρ → ∀ v : V, v ≠ 0 → ∃ l : Module.Dual ℂ V, l ∈ smoothPart ρ.dual ∧ l v ≠ 0 := by
  intro G V _ _ _ _ _ ρ hK hρ v hv
  obtain ⟨K, hKo, hKc, hKU⟩ := hK {g | ρ g v = v} ((hρ v).mem_nhds (by simp))
  have hfix : v ∈ fixed ρ K := GlobalTheory.IwahoriInj.mem_fixed.2 fun h hh => hKU hh
  have hnot : v ∉ twKer ρ K 1 := fun h => hv (GlobalTheory.IwahoriInj.eq_zero_of_fixed hρ hKc hfix h)
  have hq : (twKer ρ K 1).mkQ v ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (V ⧸ twKer ρ K 1), f ((twKer ρ K 1).mkQ v) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hq ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  refine ⟨f ∘ₗ (twKer ρ K 1).mkQ, ?_, hf⟩
  have hinv : ∀ g ∈ K, ρ.dual g (f ∘ₗ (twKer ρ K 1).mkQ) = f ∘ₗ (twKer ρ K 1).mkQ := by
    intro g hg
    refine LinearMap.ext fun x => ?_
    rw [Representation.dual_apply]
    show f ((twKer ρ K 1).mkQ (ρ g⁻¹ x)) = f ((twKer ρ K 1).mkQ x)
    congr 1
    exact (Submodule.Quotient.eq _).2 (GlobalTheory.IwahoriInj.sub_mem_twKer (inv_mem hg) x)
  exact GlobalTheory.SmGL.mem_smoothPart_of_nhds
    (Filter.mem_of_superset (hKo.mem_nhds K.one_mem) fun g hg => hinv g hg)

end GlobalTheory.SmoothForm
