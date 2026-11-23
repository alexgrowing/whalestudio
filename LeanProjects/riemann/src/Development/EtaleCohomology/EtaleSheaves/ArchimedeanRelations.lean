import Development.EtaleCohomology.EtaleSheaves.KernelLocalization.RangeOfBd
import Development.EtaleCohomology.EtaleSheaves.TruncKerPf
import Development.EtaleCohomology.EtaleSheaves.DescIntPf
import Development.EtaleCohomology.EtaleSheaves.FiltGenPf
import Development.EtaleCohomology.EtaleSheaves.DiscLvlPf
import Development.EtaleCohomology.EtaleSheaves.ShiftLvlPf
import Development.EtaleCohomology.EtaleSheaves.LeafConeExactPf

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.LeafGhostCut LateralTheory.E.DescIntPf LateralTheory.E.KernelLocalization
namespace LateralTheory.E.RelativeTruncationSingleDegree
theorem sub_of (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (h : RelZS R F n f)
    (hf : ∀ z : Hrel R f F n, pull R f F n (fgt R f F n z) = 0) : Subsingleton (Hrel R f F n) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  have h1 : fgt R f F n z = 0 := (injective_iff_map_eq_zero _).1 h.2 _ (hf z)
  exact (injective_iff_map_eq_zero _).1 (LateralTheory.E.TruncationKernel.fgt_injective_of_pull_surjective R F f n h.1) z h1
theorem rel_of (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (h : Subsingleton (Hrel R f F n)) :
    RelZS R F n f := by
  refine ⟨fun m hm y => range_of_bd R F f m n (by omega) y (Subsingleton.elim _ _), ?_⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LateralTheory.E.TruncationKernel.exists_fgt_eq_of_pull_eq_zero R F f n x hx
  rw [Subsingleton.elim y 0, map_zero]
theorem pull_fgt (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (z : Hrel R f F n) :
    pull R f F n (fgt R f F n z) = 0 := by
  obtain ⟨c, rfl⟩ := z.mk_surjective
  exact LateralTheory.E.LeafConeExactPf.pre_inr_eq_zero _ _ c
theorem etale_relK_single_degree_pieces_of_piece_and_filtration : EtaleRelativeIsoTruncationFromLevels := by
  intro R _ F U E u n hlow h0
  refine rel_of R F u n (LateralTheory.E.CechFiltPf.CechFilt_of_disc_shift_filtGen LateralTheory.E.DiscLvlPf.DiscLvl_of LateralTheory.E.ShiftLvlPf.ShiftLvl_of
    LateralTheory.E.FiltGenPf.FiltGen_of R F u n fun p => sub_of R F _ _ ?_ (pull_fgt R F _ _))
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simpa using h0
  · exact hlow p _ (by omega)
end LateralTheory.E.RelativeTruncationSingleDegree
