import Development.EtaleCohomology.EtaleSheaves.DescIntPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescIntPf

namespace LateralTheory.E.TruncationPieces

def RelK (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {K L : Cx R} (f : K ⟶ L) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (HK.pull R f F m)) ∧ Function.Injective (HK.pull R f F n)

def piece (R : Type) [CommRing R] {U E : Spc} (u : U ⟶ E) (p : ℕ) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (((chains R).obj U).X (-(p : ℤ))) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (((chains R).obj E).X (-(p : ℤ))) :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (((chains R).map u).f (-(p : ℤ)))

def Piece : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (u : U ⟶ E) (p : ℕ) (k : ℤ),
  RelZS R F k (disc.map (u.app (Opposite.op (SimplexCategory.mk p)))) → RelK R F (k + p) (piece R u p)

def Filt : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (u : U ⟶ E) (n : ℤ),
  (∀ p : ℕ, RelK R F n (piece R u p)) → RelZS R F n u

theorem etale_relK_single_degree_pieces_of_piece_and_filtration (hP : Piece) (hF : Filt) : LateralTheory.E.DescIntPf.EtaleRelativeIsoTruncationFromLevels := by
  intro R _ F U E u n hlow h0
  refine hF R F u n (fun p => ?_)
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have := hP R F u 0 n h0
    simpa using this
  · have hk : n - (p : ℤ) < n := by omega
    have := hP R F u p (n - p) (hlow p (n - p) hk)
    simpa using this

end LateralTheory.E.TruncationPieces
