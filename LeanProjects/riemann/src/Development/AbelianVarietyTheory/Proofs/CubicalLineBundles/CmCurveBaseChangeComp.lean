import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.EllComp

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem lbIso_pull_comp {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X} (h : LBIso (L.pull φ) L')
    (ψ : X'' ⟶ X') : LBIso (L.pull (ψ ≫ φ)) (L'.pull ψ) :=
  LBIso.chartPull (chartPullSame L _ _ _ ψ fun _ => rfl) (chartPullPull L' ψ ψ rfl) h

theorem dualMapR_comp (f : R →+* R') (g : R' →+* R'') :
    spMap (Chart.dualMapR g) ≫ spMap (Chart.dualMapR f) = spMap (Chart.dualMapR (g.comp f)) := by
  refine (spMap_comp_spMap _ _).trans ?_
  congr 1
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR]

theorem isPolFibre_comp {f : R →+* R'} {g : R' →+* R''} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')}
    {P'' : Out.PolAV (Sp R'')} {φ : P'.A.left ⟶ P.A.left} {ψ : P''.A.left ⟶ P'.A.left}
    (h : IsPolFibre f P P' φ) (h' : IsPolFibre g P' P'' ψ) : IsPolFibre (g.comp f) P P'' (ψ ≫ φ) :=
  ⟨h'.1.trans h.1, (h'.2.1.comp h.2.1).congr (spMap_comp_spMap _ _) rfl,
    LBIso.trans (pull_isLB P.isLB _) (pull_isLB P'.isLB _) P''.isLB (lbIso_pull_comp h.2.2 ψ) h'.2.2⟩

theorem isVecOver_comp {f : R →+* R'} {g : R' →+* R''} {A : Over (Sp R)} {A' : Over (Sp R')} {A'' : Over (Sp R'')}
    {φ : A'.left ⟶ A.left} {ψ : A''.left ⟶ A'.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'} {v'' : epsR R'' ⟶ A''}
    (h : IsVecOver f φ v v') (h' : IsVecOver g ψ v' v'') : IsVecOver (g.comp f) (ψ ≫ φ) v v'' := by
  unfold IsVecOver at *
  rw [← Category.assoc, h', Category.assoc, h, ← Category.assoc]
  exact congrArg (· ≫ v.left) (dualMapR_comp f g)

theorem exists_isPolFibre_lift {f : R →+* R'} {g : R' →+* R''} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')}
    {P'' : Out.PolAV (Sp R'')} {φ : P'.A.left ⟶ P.A.left} {χ : P''.A.left ⟶ P.A.left}
    (h : IsPolFibre f P P' φ) (n : IsPolFibre (g.comp f) P P'' χ) :
    ∃ ψ : P''.A.left ⟶ P'.A.left, ψ ≫ φ = χ ∧ IsPolFibre g P' P'' ψ := by
  have n' : IsGrpPullback P''.A P.A (spMap g ≫ spMap f) χ := n.2.1.congr (spMap_comp_spMap _ _).symm rfl
  have w : χ ≫ P.A.hom = (P''.A.hom ≫ spMap g) ≫ spMap f := n'.1.w.trans (Category.assoc _ _ _).symm
  have e : h.2.1.1.lift _ _ w ≫ φ = χ := h.2.1.1.lift_fst _ _ w
  refine ⟨h.2.1.1.lift _ _ w, e, n.1.trans h.1.symm,
    h.2.1.cancel (n'.congr rfl e.symm) (h.2.1.1.lift_snd _ _ w), ?_⟩
  refine LBIso.trans (pull_isLB P'.isLB _) (pull_isLB P.isLB _) P''.isLB (lbIso_pull_comp h.2.2 _).symm ?_
  rw [e]
  exact n.2.2

theorem isVecOver_cancel {f : R →+* R'} {g : R' →+* R''} {A : Over (Sp R)} {A' : Over (Sp R')} {A'' : Over (Sp R'')}
    {φ : A'.left ⟶ A.left} {ψ : A''.left ⟶ A'.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'} {v'' : epsR R'' ⟶ A''}
    (hφ : IsPullback φ A'.hom A.hom (spMap f)) (hψ : IsPullback ψ A''.hom A'.hom (spMap g))
    (h : IsVecOver f φ v v') (n : IsVecOver (g.comp f) (ψ ≫ φ) v v'') : IsVecOver g ψ v' v'' := by
  obtain ⟨w, hw, -⟩ := existsUnique_isVecOver hψ v'
  have hp : IsPullback (ψ ≫ φ) A''.hom A.hom (spMap (g.comp f)) := by
    rw [← spMap_comp_spMap]
    exact hψ.paste_horiz hφ
  rw [(existsUnique_isVecOver hp v).unique n (isVecOver_comp h hw)]
  exact hw

theorem isLieNormSq_iff {f : R →+* R'} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {φ : P'.A.left ⟶ P.A.left}
    {v : epsR R ⟶ P.A} {v' : epsR R' ⟶ P'.A} (h : IsPolFibre f P P' φ) (hv : IsVecOver f φ v v') (σ : R' →+* ℂ)
    (r : ℝ) : IsLieNormSq P' v' σ r ↔ IsLieNormSq P v (σ.comp f) r := by
  constructor
  · rintro ⟨Q, ψ, w, u, Hm, χ, z, h₁, h₂, h₃⟩
    exact ⟨Q, ψ ≫ φ, w, u, Hm, χ, z, isPolFibre_comp h h₁, isVecOver_comp hv h₂, h₃⟩
  · rintro ⟨Q, ψ₀, w, u, Hm, χ, z, h₁, h₂, h₃⟩
    obtain ⟨ψ, rfl, hψ⟩ := exists_isPolFibre_lift h h₁
    exact ⟨Q, ψ, w, u, Hm, χ, z, hψ, isVecOver_cancel h.2.1.1 hψ.2.1.1 hv h₂, h₃⟩

theorem ellMap_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (R' : Type) [CommRing R'] (ω' : R') (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left), EllMap C' C f φ → (∀ (R'' : Type) [CommRing R''] (ω'' : R'') (C'' : Ell H R'' ω'') (f' : R' →+* R'') (φ' : C''.P.A.left ⟶ C'.P.A.left), EllMap C'' C' f' φ' → EllMap C'' C (f'.comp f) (φ' ≫ φ)) ∧ (∀ σ : R' →+* ℂ, C.IsPrincipalAt (σ.comp f) → C'.IsPrincipalAt σ) ∧ ∀ (σ : R' →+* ℂ) (r : ℝ), Out.PolBaseChangeSt → (IsLieNormSq C'.P C'.v σ r ↔ IsLieNormSq C.P C.v (σ.comp f) r) := by
  intro E _ _ _ H R _ ω C R' _ ω' C' f φ h
  refine ⟨fun R'' _ ω'' C'' f' φ' h' => ⟨?_, isPolFibre_comp h.2.1 h'.2.1, isVecOver_comp h.2.2.1 h'.2.2.1, fun a => ?_⟩,
    fun σ hC Q ψ hψ => hC Q (ψ ≫ φ) (isPolFibre_comp h.2.1 hψ), fun σ r _ => isLieNormSq_iff h.2.1 h.2.2.1 σ r⟩
  · rw [RingHom.comp_apply, h.1, h'.1]
  · rw [← Category.assoc, h'.2.2.2 a, Category.assoc, h.2.2.2 a, Category.assoc]

end GlobalTheory.CM.EllComp
end
