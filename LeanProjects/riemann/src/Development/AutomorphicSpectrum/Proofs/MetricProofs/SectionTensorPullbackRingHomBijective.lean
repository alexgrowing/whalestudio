import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Set Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_const_of_section_mem_range : ∀ (n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Countable Λ] (B : Set (Fin n → ℂ)), IsOpen B → IsPreconnected B → B.Nonempty → ∀ (P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))) (s : (Fin n → ℂ) → (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => P b x) B) → DifferentiableOn ℂ s B → (∀ b ∈ B, s b ∈ (P b).range) → ∃ x : Λ, ∀ b ∈ B, s b = P b x := by
  intro n g Λ _ _ B hB hpc hne P s hP hs hrange
  haveI : Nonempty B := hne.to_subtype
  haveI : LocallyCompactSpace B := hB.locallyCompactSpace
  haveI : BaireSpace B := BaireSpace.of_t2Space_locallyCompactSpace
  have hclosed : ∀ x : Λ, IsClosed {b : B | s b = P b x} := fun x =>
    isClosed_eq hs.continuousOn.restrict (hP x).continuousOn.restrict
  have hunion : (⋃ x : Λ, {b : B | s b = P b x}) = univ := by
    refine eq_univ_of_forall fun b => ?_
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp (hrange b b.2)
    exact mem_iUnion.mpr ⟨x, hx.symm⟩
  obtain ⟨x, b₀, hb₀⟩ := nonempty_interior_of_iUnion_of_closed hclosed hunion
  refine ⟨x, ?_⟩
  have hopen : IsOpen ((Subtype.val : B → Fin n → ℂ) '' interior {b : B | s b = P b x}) :=
    hB.isOpenMap_subtype_val _ isOpen_interior
  have hev : (fun b => s b - P b x) =ᶠ[𝓝 (b₀ : Fin n → ℂ)] 0 := by
    filter_upwards [hopen.mem_nhds ⟨b₀, hb₀, rfl⟩]
    rintro _ ⟨c, hc, rfl⟩
    have hmem : c ∈ {b : B | s b = P b x} := interior_subset hc
    have hc' : s c = P c x := hmem
    show s c - P c x = 0
    exact sub_eq_zero.mpr hc'
  have han : AnalyticOnNhd ℂ (fun b => s b - P b x) B :=
    GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hB (hs.sub (hP x))
  intro b hb
  have h0 : s b - P b x = 0 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpc b₀.2 hev hb
  exact sub_eq_zero.mp h0

end GlobalTheory.CompanionTheory.Ar.Flat
