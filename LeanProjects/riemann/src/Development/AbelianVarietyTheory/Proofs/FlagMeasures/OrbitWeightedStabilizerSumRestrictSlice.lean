import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.Slice

theorem exists_smul_eq_out (G : Type) {α : Type} [Group G] [MulAction G α] (x : α) :
    ∃ g : G, g • x = Quotient.out (Quotient.mk (MulAction.orbitRel G α) x) := by
  have h : (MulAction.orbitRel G α) (Quotient.out (Quotient.mk (MulAction.orbitRel G α) x)) x :=
    Quotient.exact (Quotient.out_eq _)
  exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)

theorem card_stabilizer_smul (G : Type) {α : Type} [Group G] [MulAction G α] (g : G) (x : α) :
    ENat.card (MulAction.stabilizer G (g • x)) = ENat.card (MulAction.stabilizer G x) := by
  have h : (MulAction.orbitRel G α) (g • x) x :=
    MulAction.orbitRel_apply.mpr (MulAction.mem_orbit x g)
  exact ENat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel h).toEquiv

theorem card_stabilizer_subgroup {G α : Type} [Group G] [MulAction G α] (H : Subgroup G) (x : α)
    (h : ∀ g : G, g • x = x → g ∈ H) :
    ENat.card (MulAction.stabilizer H x) = ENat.card (MulAction.stabilizer G x) :=
  ENat.card_congr
    { toFun := fun a => ⟨(a.1 : G), a.2⟩
      invFun := fun a => ⟨⟨a.1, h a.1 a.2⟩, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem orbSum_restrict : ∀ (G α : Type) [Group G] [MulAction G α] (H : Subgroup G) (X X₀ : Set α) (N : α → ℝ≥0∞), X₀ ⊆ X → Stable G X → Stable H X₀ → (∀ (g : G) x, N (g • x) = N x) → (∀ x ∈ X, ∃ g : G, g • x ∈ X₀) → (∀ (g : G), ∀ x ∈ X₀, g • x ∈ X₀ → g ∈ H) → orbSum H X₀ N = orbSum G X N := by
  intro G α _ _ H X X₀ N hsub hX hX₀ hN hmeet hret
  let f : {q : MulAction.orbitRel.Quotient H α // Quotient.out q ∈ X₀} →
      {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X} := fun q =>
    ⟨Quotient.mk (MulAction.orbitRel G α) (Quotient.out q.1), by
      obtain ⟨g, hg⟩ := exists_smul_eq_out G (Quotient.out q.1)
      rw [← hg]
      exact hX g _ (hsub q.2)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : (MulAction.orbitRel G α) (Quotient.out a.1) (Quotient.out b.1) :=
      Quotient.exact (congrArg Subtype.val hab)
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h1)
    have hgH : g ∈ H := hret g _ b.2 (hg ▸ a.2)
    have h2 : (MulAction.orbitRel H α) (Quotient.out a.1) (Quotient.out b.1) :=
      MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨⟨g, hgH⟩, hg⟩)
    apply Subtype.ext
    rw [← Quotient.out_eq a.1, ← Quotient.out_eq b.1]
    exact Quotient.sound h2
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨g, hg⟩ := hmeet _ b.2
    obtain ⟨k, hk⟩ := exists_smul_eq_out H (g • Quotient.out b.1)
    refine ⟨⟨Quotient.mk (MulAction.orbitRel H α) (g • Quotient.out b.1), ?_⟩, ?_⟩
    · rw [← hk]; exact hX₀ k _ hg
    · apply Subtype.ext
      show Quotient.mk (MulAction.orbitRel G α)
        (Quotient.out (Quotient.mk (MulAction.orbitRel H α) (g • Quotient.out b.1))) = b.1
      rw [← hk]
      conv_rhs => rw [← Quotient.out_eq b.1]
      apply Quotient.sound
      refine MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨(k : G) * g, ?_⟩)
      rw [mul_smul]; rfl
  unfold orbSum
  rw [← (Equiv.ofBijective f ⟨hinj, hsurj⟩).tsum_eq]
  refine tsum_congr fun q => ?_
  obtain ⟨g, hg⟩ := exists_smul_eq_out G (Quotient.out q.1)
  have e : Quotient.out ((Equiv.ofBijective f ⟨hinj, hsurj⟩) q).1 = g • Quotient.out q.1 := hg.symm
  rw [e, hN, card_stabilizer_smul, card_stabilizer_subgroup H _
    (fun a ha => hret a _ q.2 (by rw [ha]; exact q.2))]

end GlobalTheory.Mass.Slice
