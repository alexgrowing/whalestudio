import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem spMap_away_mem_basicOpen {S : Type} [CommRing S] (s : S)
    (x : Sp (Localization.Away s)) :
    (spMap (algebraMap S (Localization.Away s))).base x ∈ PrimeSpectrum.basicOpen s := by
  show algebraMap S (Localization.Away s) s ∉ x.asIdeal
  intro h
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))

theorem exists_basicOpen_cover_affine (S : Type) [CommRing S] (Y : Scheme.{0}) (u : Sp S ⟶ Y) :
    ∃ (n : ℕ) (s : Fin n → S) (W : Fin n → Y.Opens), Ideal.span (Set.range s) = ⊤ ∧
      (∀ i, IsAffineOpen (W i)) ∧ ∀ i, (spMap (algebraMap S (Localization.Away (s i))) ≫ u) ⁻¹ᵁ W i = ⊤ := by
  classical
  let T : Set S := {s | ∃ W : Y.Opens, IsAffineOpen W ∧
    ∀ x : Sp S, x ∈ PrimeSpectrum.basicOpen s → u.base x ∈ W}
  have hT : Ideal.span T = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff', eq_top_iff]
    intro x _
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (u.base x)) isOpen_univ
    obtain ⟨_, ⟨s, rfl⟩, hxs, hsW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        hxW (u ⁻¹ᵁ W).isOpen
    have hsT : s ∈ T := ⟨W, hW, fun y hy => hsW hy⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, TopologicalSpace.Opens.mem_iSup.mpr ⟨hsT, hxs⟩⟩
  obtain ⟨F, hFT, hF⟩ := (Ideal.span_eq_top_iff_finite T).mp hT
  have hW : ∀ t : F, ∃ W : Y.Opens, IsAffineOpen W ∧
      ∀ x : Sp S, x ∈ PrimeSpectrum.basicOpen (t : S) → u.base x ∈ W := fun t => hFT t.2
  choose Wf hWa hWs using hW
  refine ⟨F.card, fun i => (F.equivFin.symm i : S), fun i => Wf (F.equivFin.symm i), ?_,
    fun i => hWa _, fun i => ?_⟩
  · have : Set.range (fun i => (F.equivFin.symm i : S)) = (F : Set S) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact (F.equivFin.symm i).2
      · intro hy
        exact ⟨F.equivFin ⟨y, hy⟩, by simp⟩
    rw [this, hF]
  · rw [eq_top_iff]
    intro x _
    exact hWs _ _ (spMap_away_mem_basicOpen _ x)

end GlobalTheory.SecGlue
