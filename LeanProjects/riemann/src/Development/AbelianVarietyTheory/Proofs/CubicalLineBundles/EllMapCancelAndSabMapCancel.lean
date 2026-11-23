import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.Factor

theorem dualMapR_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    Chart.dualMapR (f'.comp f) = (Chart.dualMapR f').comp (Chart.dualMapR f) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [Chart.dualMapR]

theorem ellMap_cancel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R R' R'' : Type} [CommRing R]
    [CommRing R'] [CommRing R''] {f : R →+* R'} {f' : R' →+* R''} {ω : R} {ω' : R'} {ω'' : R''} {C : Ell H R ω}
    {C' : Ell H R' ω'} {C'' : Ell H R'' ω''} {φ : C'.P.A.left ⟶ C.P.A.left} {ψ : C''.P.A.left ⟶ C.P.A.left}
    (h : EllMap C' C f φ) (k : EllMap C'' C (f'.comp f) ψ) :
    ∃ φ' : C''.P.A.left ⟶ C'.P.A.left, EllMap C'' C' f' φ' ∧ φ' ≫ φ = ψ := by
  obtain ⟨hω, ⟨hg, hp, hL⟩, hv, ha⟩ := h
  obtain ⟨kω, ⟨kg, kp, kL⟩, kv, ka⟩ := k
  rw [← spMap_comp_spMap] at kp
  have w : ψ ≫ C.P.A.hom = (C''.P.A.hom ≫ spMap f') ≫ spMap f := by rw [kp.1.w, Category.assoc]
  obtain ⟨l, h₁, h₂⟩ : ∃ l : C''.P.A.left ⟶ C'.P.A.left, l ≫ φ = ψ ∧ l ≫ C'.P.A.hom = C''.P.A.hom ≫ spMap f' :=
    ⟨hp.1.lift _ _ w, hp.1.lift_fst _ _ w, hp.1.lift_snd _ _ w⟩
  subst h₁
  refine ⟨l, ⟨hω ▸ kω, ⟨kg.trans hg.symm, hp.cancel kp h₂, ?_⟩, ?_, fun a => ?_⟩, rfl⟩
  · have e : LBIso (C.P.L.pull (l ≫ φ)) (C'.P.L.pull l) :=
      LBIso.chartPull (chartPullSame C.P.L _ _ _ l fun _ => rfl) (chartPullPull C'.P.L l l rfl) hL
    exact LBIso.trans (pull_isLB C'.P.isLB _) (pull_isLB C.P.isLB _) C''.P.isLB e.symm kL
  · unfold IsVecOver at hv kv ⊢
    apply hp.1.hom_ext
    · rw [Category.assoc, kv, Category.assoc, hv, dualMapR_comp, ← spMap_comp_spMap, Category.assoc]
    · rw [Category.assoc, h₂, ← Category.assoc, Over.w C''.v, Category.assoc, Over.w C'.v]
      refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
      congr 1
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · apply hp.1.hom_ext
    · rw [Category.assoc, ka, Category.assoc, Category.assoc, ha]
    · rw [Category.assoc, h₂, ← Category.assoc, Over.w, Category.assoc, Over.w, h₂]

theorem ellMap_cancel_and_sabMap_cancel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R''),
  (∀ (ω : R) (ω' : R') (ω'' : R'') (C : Ell H R ω) (C' : Ell H R' ω') (C'' : Ell H R'' ω'') (φ : C'.P.A.left ⟶ C.P.A.left) (ψ : C''.P.A.left ⟶ C.P.A.left), EllMap C' C f φ → EllMap C'' C (f'.comp f) ψ → ∃ φ' : C''.P.A.left ⟶ C'.P.A.left, EllMap C'' C' f' φ' ∧ φ' ≫ φ = ψ) ∧
  ∀ (S : Scheme.{0}) (y : Sp R' ⟶ S) (y' : Sp R'' ⟶ S) (t : SAB H S) (t' : SAB H (Sp R')) (t'' : SAB H (Sp R'')) (m : SABMap t' t y) (n : SABMap t'' t y'), spMap f' ≫ y = y' → ∃ m' : SABMap t'' t' (spMap f'), m'.φ ≫ m.φ = n.φ := by
  intro E _ _ _ H R R' R'' _ _ _ f f'
  refine ⟨fun _ _ _ _ _ _ _ _ h k => ellMap_cancel h k, fun S y y' t t' t'' m n e => ?_⟩
  subst e
  obtain ⟨m', h⟩ := ObjMaps.exists_sab_cancel m n
  exact ⟨m', h.symm⟩

end GlobalTheory.CM.Factor
end
