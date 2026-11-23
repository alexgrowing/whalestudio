import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.RightOfFd
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateSubgroup

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Two

open MeasureTheory

variable {G B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] {Γ S A : Subgroup G}

theorem cnt_sub [Countable Γ] [DiscreteTopology Γ] (S : Subgroup G) : Countable (Γ.subgroupOf S) ∧ DiscreteTopology (Γ.subgroupOf S) := by
  let j : Γ.subgroupOf S → Γ := fun γ => ⟨γ.1.1, γ.2⟩
  have ji : Function.Injective j := fun a b h => Subtype.ext (Subtype.ext (congrArg Subtype.val h :))
  exact ⟨ji.countable, DiscreteTopology.of_continuous_injective ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) ji⟩

theorem IsAv.conj_sub (hA : IsClosed (A : Set G)) (L : Lat (Γ.subgroupOf A)) {f c : G → ℂ} (h : IsAv (Γ.subgroupOf A) Subtype.val f c)
    {γ : G} (hγ : γ ∈ Γ) (h1 : ∀ u ∈ A, γ⁻¹ * u * γ ∈ A) (h2 : ∀ u ∈ A, γ * u * γ⁻¹ ∈ A) (hf : ∀ x, f (γ * x) = f x) (x : G) :
    c (γ * x) = c x :=
  _root_.UpperTheory.Reformulated.B.ConjugateSubgroup.conj_sub hA L h hγ h1 h2 hf x

variable [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [MeasurableSpace B] [BorelSpace B]
  [LocallyCompactSpace B] [SecondCountableTopology B] [T2Space B] {ΓB : Subgroup B}

theorem stage_sub [Countable Γ] [DiscreteTopology Γ] (hS : IsClosed (S : Set G)) (hA : IsClosed (A : Set G)) (hAS : A ≤ S)
    {ι : B →* G} (cι : Continuous ι) (hι : ∀ b, ι b ∈ S) {π : S →* B} (cπ : Continuous π) (πι : ∀ b, π ⟨ι b, hι b⟩ = b)
    (ker : ∀ s : S, π s = 1 ↔ s.1 ∈ A) (hB : ∀ b ∈ ΓB, ι b ∈ Γ) (hπ : ∀ s : S, s.1 ∈ Γ → π s ∈ ΓB)
    (LA : Lat (Γ.subgroupOf A)) (LB : Lat ΓB) : Lat (Γ.subgroupOf S) ∧ ∀ f cA c : G → ℂ, Continuous f →
      (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → IsAv (Γ.subgroupOf A) Subtype.val f cA → IsAv ΓB ι cA c →
      IsAv (Γ.subgroupOf S) Subtype.val f c := by
  have : LocallyCompactSpace A := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology A := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  have h : Semi (Γ.subgroupOf S) (Γ.subgroupOf A) ΓB (Subgroup.inclusion hAS) (ι.codRestrict S hι)
      (fun s => ⟨s.1 * (ι (π s))⁻¹, (ker (s * (⟨ι (π s), hι _⟩ : S)⁻¹)).1 (by rw [map_mul, map_inv, πι, mul_inv_cancel])⟩) π :=
    ⟨continuous_subtype_val.subtype_mk _, cι.subtype_mk _, Continuous.subtype_mk (by fun_prop) _, cπ, Subgroup.inclusion_injective _,
      fun s => Subtype.ext (inv_mul_cancel_right _ _), fun a => (ker _).2 a.2, πι, fun _ => Iff.rfl, hB, hπ⟩
  have L := h.lat LA LB (cnt_sub S).1 (cnt_sub S).2
  exact ⟨L, fun f cA c a b d e => h.stage L LA LB (inc := S.subtype) continuous_subtype_val a (fun γ hγ => b _ hγ) d e⟩

end PositivityTheory.ThKEnd.Two

end
