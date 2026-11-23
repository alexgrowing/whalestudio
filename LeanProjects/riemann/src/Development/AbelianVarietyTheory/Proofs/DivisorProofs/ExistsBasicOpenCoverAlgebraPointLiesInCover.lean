import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_away_cover_sm : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), ∃ (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ ∧ ∀ a, Sm W (spOver (IsScalarTower.toAlgHom R D (Localization.Away (s a))) ≫ x) := by
  intro R _ X K W hW D _ _ x
  let f : Sp D ⟶ X.left := x.left
  let S : Set D := {s | ∃ i, ∀ q : PrimeSpectrum D, q ∈ PrimeSpectrum.basicOpen s → f q ∈ W i}
  have hS : Ideal.span S = ⊤ := by
    by_contra h'
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h'
    let p : PrimeSpectrum D := ⟨m, hm.isPrime⟩
    have hp : f p ∈ (⨆ i, W i) := by rw [hW]; trivial
    obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 hp
    obtain ⟨_, ⟨s, rfl⟩, hs, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := f ⁻¹' (W i : Set X.left)) hi ((W i).isOpen.preimage f.continuous)
    have hsS : s ∈ S := ⟨i, fun q hq ↦ hsub hq⟩
    exact hs (hle (Ideal.subset_span hsS))
  have h1 : (1 : D) ∈ Submodule.span D S := by
    change (1 : D) ∈ Ideal.span S; rw [hS]; trivial
  obtain ⟨T, hTS, hT⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨T.card, fun a ↦ (T.equivFin.symm a : D), ?_, ?_⟩
  · have hr : Set.range (fun a ↦ (T.equivFin.symm a : D)) = (T : Set D) := by
      ext y; constructor
      · rintro ⟨a, rfl⟩; exact (T.equivFin.symm a).2
      · intro hy; exact ⟨T.equivFin ⟨y, hy⟩, by simp⟩
    rw [hr, Ideal.eq_top_iff_one]; exact hT
  · intro a
    obtain ⟨i, hi⟩ := hTS (T.equivFin.symm a).2
    refine ⟨i, fun q _ ↦ ?_⟩
    have hq : (spMap (algebraMap D (Localization.Away ((T.equivFin.symm a : D)))) q : PrimeSpectrum D) ∈
        PrimeSpectrum.basicOpen ((T.equivFin.symm a : D)) :=
      (PrimeSpectrum.localization_away_comap_range (Localization.Away ((T.equivFin.symm a : D))) _).le ⟨q, rfl⟩
    exact hi _ hq

end GlobalTheory.PtExt
