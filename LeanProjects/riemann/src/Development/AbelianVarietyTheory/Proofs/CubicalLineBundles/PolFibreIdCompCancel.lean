import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

namespace PolFibre

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem dualMapR_id : Chart.dualMapR (RingHom.id R) = RingHom.id _ := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR]

theorem dualMapR_comp (f : R →+* R') (g : R' →+* R'') :
    (Chart.dualMapR g).comp (Chart.dualMapR f) = Chart.dualMapR (g.comp f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR]

theorem spMap_dual_hom (f : R →+* R') : spMap (Chart.dualMapR f) ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
  refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
  congr 1
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {φ : Y ⟶ X} (h : LBIso (L.pull φ) M) (ψ : Z ⟶ Y) :
    LBIso (L.pull (ψ ≫ φ)) (M.pull ψ) :=
  LBIso.chartPull (chartPullSame L _ _ _ ψ fun _ => rfl) (chartPullPull M ψ ψ rfl) h

theorem refl (P : Out.PolAV (Sp R)) : IsPolFibre (RingHom.id R) P P (𝟙 _) :=
  haveI : IsMonHom (Iso.refl P.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  ⟨rfl, (isGrpPullback_of_iso (Iso.refl P.A)).congr (Spec.map_id (CommRingCat.of R)).symm rfl,
    LBIso.chartPull (chartPullPull P.L _ (𝟙 _) rfl) (chartPullId P.L) (PolBaseChange.lbIso_refl P.isLB)⟩

theorem vec_refl {A : Over (Sp R)} (v : epsR R ⟶ A) : IsVecOver (RingHom.id R) (𝟙 _) v v := by
  unfold IsVecOver
  rw [dualMapR_id, Category.comp_id]
  exact (Category.id_comp _).symm.trans (congrArg (· ≫ v.left) (Spec.map_id (CommRingCat.of (DualNumber R))).symm)

variable {f : R →+* R'} {g : R' →+* R''} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {P'' : Out.PolAV (Sp R'')}
  {φ : P'.A.left ⟶ P.A.left}

theorem comp (h : IsPolFibre f P P' φ) {ψ : P''.A.left ⟶ P'.A.left} (h' : IsPolFibre g P' P'' ψ) :
    IsPolFibre (g.comp f) P P'' (ψ ≫ φ) :=
  ⟨h'.1.trans h.1, (h'.2.1.comp h.2.1).congr (spMap_comp_spMap f g) rfl,
    LBIso.trans (pull_isLB P.isLB _) (pull_isLB P'.isLB _) P''.isLB (lbIso_pull_comp h.2.2 ψ) h'.2.2⟩

theorem cancel (h : IsPolFibre f P P' φ) {χ : P''.A.left ⟶ P.A.left} (h' : IsPolFibre (g.comp f) P P'' χ) :
    ∃ ψ, IsPolFibre g P' P'' ψ ∧ ψ ≫ φ = χ := by
  have n := h'.2.1.congr (spMap_comp_spMap f g).symm rfl
  have w : χ ≫ P.A.hom = (P''.A.hom ≫ spMap g) ≫ spMap f := n.1.w.trans (Category.assoc _ _ _).symm
  have e₁ := h.2.1.1.lift_fst _ _ w
  have e₂ := h.2.1.1.lift_snd _ _ w
  generalize h.2.1.1.lift _ _ w = ψ at e₁ e₂
  subst e₁
  exact ⟨ψ, ⟨h'.1.trans h.1.symm, h.2.1.cancel n e₂,
    LBIso.trans (pull_isLB P'.isLB _) (pull_isLB P.isLB _) P''.isLB (lbIso_pull_comp h.2.2 ψ).symm h'.2.2⟩, rfl⟩

theorem vec_iff {A : Over (Sp R)} {A' : Over (Sp R')} {A'' : Over (Sp R'')} {φ : A'.left ⟶ A.left}
    (hφ : IsPullback φ A'.hom A.hom (spMap f)) {ψ : A''.left ⟶ A'.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'}
    {v'' : epsR R'' ⟶ A''} (w : ψ ≫ A'.hom = A''.hom ≫ spMap g) (h : IsVecOver f φ v v') :
    IsVecOver g ψ v' v'' ↔ IsVecOver (g.comp f) (ψ ≫ φ) v v'' := by
  have e : (spMap (Chart.dualMapR g) ≫ v'.left) ≫ φ = spMap (Chart.dualMapR (g.comp f)) ≫ v.left := by
    rw [Category.assoc, h, ← Category.assoc, ← dualMapR_comp]
    exact congrArg (· ≫ v.left) (spMap_comp_spMap _ _)
  refine ⟨fun h' => ?_, fun h' => hφ.hom_ext ?_ ?_⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) h').trans e)
  · exact (Category.assoc _ _ _).trans (Eq.trans h' e.symm)
  · rw [Category.assoc, Category.assoc, w, Over.w v', ← Category.assoc, Over.w v'']
    exact (spMap_dual_hom g).symm

end PolFibre

theorem polFibre_id_comp_cancel : (∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A), IsPolFibre (RingHom.id R) P P (𝟙 _) ∧ IsVecOver (RingHom.id R) (𝟙 _) v v) ∧ ∀ (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') (P : Out.PolAV (Sp R)) (P' : Out.PolAV (Sp R')) (P'' : Out.PolAV (Sp R'')) (φ : P'.A.left ⟶ P.A.left), IsPolFibre f P P' φ → (∀ ψ : P''.A.left ⟶ P'.A.left, IsPolFibre g P' P'' ψ → IsPolFibre (g.comp f) P P'' (ψ ≫ φ)) ∧ (∀ χ : P''.A.left ⟶ P.A.left, IsPolFibre (g.comp f) P P'' χ → ∃ ψ, IsPolFibre g P' P'' ψ ∧ ψ ≫ φ = χ) ∧ ∀ (ψ : P''.A.left ⟶ P'.A.left) (v : epsR R ⟶ P.A) (v' : epsR R' ⟶ P'.A) (v'' : epsR R'' ⟶ P''.A), ψ ≫ P'.A.hom = P''.A.hom ≫ spMap g → IsVecOver f φ v v' → (IsVecOver g ψ v' v'' ↔ IsVecOver (g.comp f) (ψ ≫ φ) v v'') :=
  ⟨fun _ _ P v => ⟨PolFibre.refl P, PolFibre.vec_refl v⟩, fun _ _ _ _ _ _ _ _ _ _ _ _ h =>
    ⟨fun _ h' => PolFibre.comp h h', fun _ h' => PolFibre.cancel h h',
      fun _ _ _ _ w hv => PolFibre.vec_iff h.2.1.1 w hv⟩⟩

end GlobalTheory
