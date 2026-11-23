import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.ContraSub

open GlobalTheory.ContraRefl

section General

variable {G V X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]

def incl {π : Representation ℂ G V} (S : Subrepresentation π) :
    S.toRepresentation.IntertwiningMap π where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := by ext _; rfl

theorem isSmooth_sub {π : Representation ℂ G V} (hπ : IsSmooth π) (S : Subrepresentation π) :
    IsSmooth S.toRepresentation := fun x => by
  have : {g : G | S.toRepresentation g x = x} = {g : G | π g x.1 = x.1} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact hπ x.1

theorem contraMap_incl_surjective
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : Representation ℂ G V} (hπ : IsSmooth π) (S : Subrepresentation π) :
    Function.Surjective (contraMap (incl S)) := by
  intro l
  obtain ⟨K, ho, hc, hKs⟩ := hG _ ((isSmooth_contra S.toRepresentation l).mem_nhds (by simp))
  have hlK : l ∈ fixed (contra S.toRepresentation) K := mem_fix.2 fun h hh => hKs hh
  obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend (l : Module.Dual ℂ S.toSubmodule)
  obtain ⟨l', h1, h2⟩ := exists_fixed_contra hπ ho hc (l₀ ∘ₗ (fixed π K).subtype)
  have hl'K : l' ∈ fixed (contra π) K := mem_fix.2 h1
  refine ⟨l', Subtype.ext (form_ext (isSmooth_sub hπ S) hc (fun h hh w => ?_) (fun h hh w => ?_)
    fun w hw => ?_)⟩
  · exact invariant_of_fixed ⟨l', hl'K⟩ h hh (w : V)
  · exact invariant_of_fixed ⟨l, hlK⟩ h hh w
  · have hwK : (w : V) ∈ fixed π K :=
      mem_fix.2 fun h hh => congrArg Subtype.val (mem_fix.1 hw h hh)
    have e1 := h2 ⟨w, hwK⟩
    have e2 := LinearMap.congr_fun hl₀ w
    exact e1.trans e2

theorem contraMap_injective {Y : Type} [AddCommGroup Y] [Module ℂ Y] {σ : Representation ℂ G X}
    {τ : Representation ℂ G Y} (f : σ.IntertwiningMap τ) (hf : Function.Surjective f) :
    Function.Injective (contraMap f) := by
  intro l l' h
  refine Subtype.ext (LinearMap.ext fun y => ?_)
  obtain ⟨x, rfl⟩ := hf y
  exact LinearMap.congr_fun (congrArg Subtype.val h) x

theorem isSubquotient_contra
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {σ : Representation ℂ G X} {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    (h : IsSubquotient σ ρ) : IsSubquotient (contra σ) (contra ρ) := by
  obtain ⟨S, f, hf⟩ := h
  exact (IsSubquotient.of_injective (contraMap f) (contraMap_injective f hf)).trans
    (IsSubquotient.of_surjective (contraMap (incl S)) (contraMap_incl_surjective hG hρ S))

end General

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin N) k) V) (ρ : Representation ℂ (GL (Fin N) k) W),
    IsSmooth σ → IsSmooth ρ → IsSubquotient σ ρ → IsSubquotient (contra σ) (contra ρ) := by
  intro k _ _ _ _ N V W _ _ _ _ σ ρ _ hρ h
  refine isSubquotient_contra (fun U hU => ?_) hρ h
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin N) U hU
  exact ⟨J, h1, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

end GlobalTheory.CompanionTheory.ContraSub
