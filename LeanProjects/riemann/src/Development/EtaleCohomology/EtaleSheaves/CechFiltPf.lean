import Development.EtaleCohomology.EtaleSheaves.CechLevel

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.CechFiltPf

def Piece : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E₀ E : Spc} (g : E₀ ⟶ E) (p : ℕ) (n : ℤ),
  Subsingleton (Hrel R (disc.map (g.app (op (SimplexCategory.mk p)))) F (n - p)) →
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map
    (((chains R).map g).f (-(p : ℤ))))) F n)

def Filt : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E₀ E : Spc} (g : E₀ ⟶ E) (n : ℤ),
  (∀ p : ℕ, Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map
    (((chains R).map g).f (-(p : ℤ))))) F n)) →
  Subsingleton (Hrel R g F n)

theorem CechFilt_of (hP : Piece) (hF : Filt) : LateralTheory.E.SSPf.CechFilt := by
  intro R _ F E₀ E g n h
  exact hF R F g n (fun p => hP R F g p n (h p))

universe u v

def FiltGen : Prop := ∀ {C : Type u} [Category.{v} C] [Abelian C] {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ),
  (∀ j, 0 < j → IsZero (K.X j)) → (∀ j, 0 < j → IsZero (L.X j)) → (∀ j, j < 0 → IsZero (I.X j)) →
  (∀ k ≤ 0, Subsingleton (CohomologyClass (mappingCone ((HomologicalComplex.single C (ComplexShape.up ℤ) k).map (φ.f k))) I n)) →
  Subsingleton (CohomologyClass (mappingCone φ) I n)

theorem chains_isZero (R : Type) [CommRing R] (E : Spc) (j : ℤ) (hj : 0 < j) : IsZero (((chains R).obj E).X j) := by
  unfold chains
  exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by
    show -(i : ℤ) ≠ j
    omega)

theorem res_isZero (R : Type) [CommRing R] (F : Shv R) (j : ℤ) (hj : j < 0) : IsZero ((res R F).X j) := by
  unfold res InjectiveResolution.cochainComplex
  exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by
    show (i : ℤ) ≠ j
    omega)

theorem Filt_of (hG : FiltGen.{2, 1}) : Filt := by
  intro R _ F E₀ E g n h
  apply hG ((chains R).map g) n (chains_isZero R E₀) (chains_isZero R E) (res_isZero R F)
  intro k hk
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, k = -(p : ℤ) := ⟨(-k).toNat, by omega⟩
  exact h p

def DiscLvl : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {P Q : PSh} (h : P ⟶ Q) (m : ℤ),
  Subsingleton (Hrel R (disc.map h) F m) →
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h))) F m)

def ShiftLvl : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E₀ E : Spc} (g : E₀ ⟶ E) (p : ℕ) (n : ℤ),
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map
    ((free R).map (g.app (op (SimplexCategory.mk p)))))) F (n - p)) →
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map
    (((chains R).map g).f (-(p : ℤ))))) F n)

theorem Piece_of (hD : DiscLvl) (hS : ShiftLvl) : Piece := by
  intro R _ F E₀ E g p n h
  exact hS R F g p n (hD R F _ _ h)

theorem CechFilt_of_disc_shift_filtGen (hD : DiscLvl) (hS : ShiftLvl) (hG : FiltGen.{2, 1}) : LateralTheory.E.SSPf.CechFilt :=
  CechFilt_of (Piece_of hD hS) (Filt_of hG)

end LateralTheory.E.CechFiltPf
