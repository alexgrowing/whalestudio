import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharValMultiplicativeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusLie

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {R : Type} [CommRing R]

theorem charVal_congr {A : Type} [CommRing A] {a a' : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X)
    (t' : Over.mk a' ⟶ splitTorus S X) (h : t.left = t'.left) (χ : X) : charVal t χ = charVal t' χ := by
  have ha : a = a' := by
    have h1 := Over.w t
    have h2 := Over.w t'
    simp only [Over.mk_hom] at h1 h2
    rw [← h1, ← h2, h]
  subst ha
  have : t = t' := Over.OverMorphism.ext h
  rw [this]

def pullPt {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A') {a : Sp A ⟶ S} {a' : Sp A' ⟶ S}
    (h : a' = spMap g ≫ a) (t : Over.mk a ⟶ splitTorus S X) : Over.mk a' ⟶ splitTorus S X :=
  Over.homMk (spMap g ≫ t.left) (by
    have h1 := Over.w t
    simp only [Over.mk_hom] at h1 ⊢
    rw [Category.assoc, h1, h])

theorem charVal_pullPt {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A') {a : Sp A ⟶ S}
    {a' : Sp A' ⟶ S} (h : a' = spMap g ≫ a) (t : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal (pullPt g h t) χ = g (charVal t χ) := by
  subst h
  exact (GlobalTheory.T.charVal_multiplicative S X A _).2.2.2.2.2 A' g t _ rfl χ

def wOf (δ : X →+ R) : Multiplicative X →* DualNumber R where
  toFun χ := TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ.toAdd)
  map_one' := by
    ext <;> simp
  map_mul' a b := by
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, add_comm]

abbrev evZ (R : Type) [CommRing R] : DualNumber R →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom

theorem base_ev (x : Sp R ⟶ S) :
    x = spMap (evZ R) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x := by
  have : spMap (evZ R) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (evZ R).comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; simp
    rw [this]; simp
  rw [← Category.assoc, this, Category.id_comp]

theorem isTanAt_iff (x : Sp R ⟶ S) (v : epsAt x ⟶ splitTorus S X) :
    IsTanAt (splitTorus S X) x v ↔ ∀ χ, (charVal v χ).fst = 1 := by
  have hT := GlobalTheory.T.charVal_multiplicative S X
  constructor
  · intro hv χ
    have e : pullPt (evZ R) (base_ev x) v = 1 := Over.OverMorphism.ext hv
    have := charVal_pullPt (evZ R) (base_ev x) v χ
    rw [e, (hT R x).2.2.1 χ] at this
    exact this.symm
  · intro hv
    have e : pullPt (evZ R) (base_ev x) v = 1 := by
      refine (hT R x).1 _ _ fun χ => ?_
      rw [charVal_pullPt, (hT R x).2.2.1 χ]
      exact hv χ
    exact congrArg (fun t => t.left) e

def ptOf (x : Sp R ⟶ S) (δ : X →+ R) : epsAt x ⟶ splitTorus S X :=
  ((GlobalTheory.T.charVal_multiplicative S X (DualNumber R) (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x)).2.2.2.2.1
    (wOf δ)).choose

theorem charVal_ptOf (x : Sp R ⟶ S) (δ : X →+ R) (χ : X) :
    charVal (ptOf x δ) χ = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ) :=
  ((GlobalTheory.T.charVal_multiplicative S X (DualNumber R) (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x)).2.2.2.2.1
    (wOf δ)).choose_spec χ

theorem ptOf_ext (x : Sp R ⟶ S) (v v' : epsAt x ⟶ splitTorus S X) (h : ∀ χ, charVal v χ = charVal v' χ) : v = v' :=
  (GlobalTheory.T.charVal_multiplicative S X (DualNumber R) _).1 v v' h

theorem epsMul_comp_base (c : R) (x : Sp R ⟶ S) :
    Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x =
      spMap (epsMul c) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x := by
  have : spMap (epsMul c) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (epsMul c).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
      ext r <;> simp [epsMul]
    rw [this]
  rw [← Category.assoc, this]

def deltaOf (x : Sp R ⟶ S) (v : epsAt x ⟶ splitTorus S X) (hv : ∀ χ, (charVal v χ).fst = 1) : X →+ R :=
  AddMonoidHom.mk' (fun χ => (charVal v χ).snd) (fun χ χ' => by
    have := ((GlobalTheory.T.charVal_multiplicative S X (DualNumber R) _).2.2.2.1 v).2 χ χ'
    simp [this, TrivSqZeroExt.snd_mul, hv, add_comm])

theorem exists_lieModel_splitTorus : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (R : Type) [CommRing R]
    (x : Sp R ⟶ S), ∃ M : LieModel (splitTorus S X) x (X →+ R), IsCocharLie M := by
  intro S X _ R _ x
  refine ⟨{ pt := ptOf x, tan := ?_, inj := ?_, onto := ?_, add := ?_, smul := ?_ },
    fun δ χ => charVal_ptOf x δ χ⟩
  · intro δ
    refine (isTanAt_iff x _).2 fun χ => ?_
    rw [charVal_ptOf]; simp
  · intro δ δ' h
    ext χ
    have := congrArg TrivSqZeroExt.snd
      ((charVal_ptOf x δ χ).symm.trans ((congrArg (fun t => charVal t χ) h).trans (charVal_ptOf x δ' χ)))
    simpa using this
  · intro v hv
    have hv' := (isTanAt_iff x v).1 hv
    refine ⟨deltaOf x v hv', ptOf_ext x _ _ fun χ => ?_⟩
    rw [charVal_ptOf]
    ext
    · simp [hv']
    · simp [deltaOf]
  · intro δ δ'
    refine ptOf_ext x _ _ fun χ => ?_
    rw [(GlobalTheory.T.charVal_multiplicative S X (DualNumber R) _).2.1, charVal_ptOf, charVal_ptOf, charVal_ptOf]
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, add_comm]
  · intro c δ
    have e : ptOf x (c • δ) = pullPt (epsMul c) (epsMul_comp_base c x) (ptOf x δ) := by
      refine ptOf_ext x _ _ fun χ => ?_
      rw [charVal_pullPt, charVal_ptOf, charVal_ptOf]
      ext <;> simp [epsMul, mul_comm]
    exact congrArg (fun t => t.left) e

end GlobalTheory.CompanionTheory.Ar.TorusLie
