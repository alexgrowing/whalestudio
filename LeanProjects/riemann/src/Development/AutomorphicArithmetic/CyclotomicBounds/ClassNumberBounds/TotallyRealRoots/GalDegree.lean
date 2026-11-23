import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalRoots
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

variable {E : Type*} [Field E]

private theorem mem_fixingSubgroup_adjoinRoots (m : ℕ) (g : Gal(AlgebraicClosure E/E)) :
    g ∈ (adjoinRoots E m).fixingSubgroup ↔ ∀ ζ : AlgebraicClosure E, ζ ^ m = 1 → g ζ = ζ := by
  constructor
  · intro hg ζ hζ
    exact (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg ζ
      (IntermediateField.subset_adjoin E _ hζ)
  · intro h
    have hle : adjoinRoots E m ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      intro ζ hζ
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      have : Subgroup.zpowers g ≤ MulAction.stabilizer Gal(AlgebraicClosure E/E) ζ := by
        rw [Subgroup.zpowers_le]
        exact h ζ hζ
      exact fun f hf => this hf
    exact (IntermediateField.le_iff_le _ _).1 hle (Subgroup.mem_zpowers g)

private theorem comap_princ_eq [CharZero E] (n : ℕ) :
    (princ l n).comap (eps l E) = (adjoinRoots E (l ^ n)).fixingSubgroup := by
  ext g
  rw [Subgroup.mem_comap, eps_mem_princ_iff, mem_fixingSubgroup_adjoinRoots]

theorem card_map_redPow_galImage [CharZero E] (n : ℕ) :
    Nat.card ((galImage l E).map (redPow l n)) = Module.finrank E (adjoinRoots E (l ^ n)) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← comap_princ_eq, princ,
    MonoidHom.comap_ker, Subgroup.index_ker, galImage, MonoidHom.map_range]

theorem resOrder_galImage [CharZero E] :
    resOrder l (galImage l E) = Module.finrank E (adjoinRoots E l) := by
  have h := comap_princ_eq (l := l) (E := E) 1
  rw [pow_one] at h
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← h, princ_one_eq_ker,
    MonoidHom.comap_ker, Subgroup.index_ker, resOrder, galImage, MonoidHom.map_range]

theorem le_depth_galImage_iff [CharZero E] (n : ℕ) :
    (n : ℕ∞) ≤ depth l (galImage l E) ↔
      ∀ ζ : AlgebraicClosure E, ζ ^ l ^ n = 1 → ζ ∈ adjoinRoots E l := by
  have h := comap_princ_eq (l := l) (E := E) 1
  rw [pow_one] at h
  rw [depth, le_nu_iff_pow_mem_princ]
  constructor
  · intro H ζ hζ
    rw [← InfiniteGalois.fixedField_fixingSubgroup (adjoinRoots E l),
      IntermediateField.mem_fixedField_iff]
    intro g hg
    rw [← h, Subgroup.mem_comap] at hg
    have := H (eps l E g) ⟨⟨g, rfl⟩, hg⟩
    rw [pow_one, eps_mem_princ_iff] at this
    exact this ζ hζ
  · rintro H u ⟨⟨g, rfl⟩, hg⟩
    rw [pow_one, eps_mem_princ_iff]
    intro ζ hζ
    have hg' : g ∈ (adjoinRoots E l).fixingSubgroup := by
      rw [← h]
      exact hg
    exact (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg' ζ (H ζ hζ)

end KStar.TotallyRealRoots
