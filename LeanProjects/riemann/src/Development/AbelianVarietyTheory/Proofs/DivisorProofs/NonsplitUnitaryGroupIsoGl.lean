import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.EulerTw
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.GamInert

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

omit [IsCMField E] in

theorem gl_ext_pLoc {x y : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)}
    (h : ∀ w, GeneralLinearGroup.map (pLoc E w) x = GeneralLinearGroup.map (pLoc E w) y) : x = y := by
  refine Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun w => ?_))
  exact congrArg (fun z : GL (Fin n) (w.adicCompletion E) => z i j) (h w)

omit [IsCMField E] in
theorem pLoc_idem (T : Finset (Pl E)) (w : Pl E) : pLoc E w (idem E T) = if w ∈ T then 1 else 0 := rfl

theorem pLoc_prjG (T : Finset (Pl E)) (w : Pl E) (x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    GeneralLinearGroup.map (pLoc E w) (prjG E n T x) =
      if w ∈ T then GeneralLinearGroup.map (pLoc E w) x else 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pLoc E w (idem E T * x i j + (1 - idem E T) * (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) = _
  rw [map_add, map_mul, map_mul, map_sub, map_one, pLoc_idem]
  split_ifs with hw
  · rw [one_mul, sub_self, zero_mul, add_zero]; rfl
  · rw [zero_mul, sub_zero, zero_add, one_mul, Units.val_one, Matrix.one_apply, Matrix.one_apply, apply_ite (pLoc E w),
      map_one, map_zero]

omit [IsCMField E] in

theorem continuous_comp_pLoc (w : Pl E) :
    Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E w)) :=
  Continuous.units_map _ (continuous_id.matrix_map
    (RestrictedProduct.continuous_eval (R := fun v : Pl E => v.adicCompletion E) w))

theorem orb_eq {u : Pl E} (hu : ¬ IsSplitAt u) : orb E u = {u} := by
  have h : cPl E u = u := (GlobalTheory.ConjAtPlace.conjSrc_eq_iff u).2 hu
  rw [orb, h]
  simp

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : Pl E), ¬ IsSplitAt u → ∃ e : GlobalTheory.EulerTw.Gam E n u ≃ₜ* GLw n u, ∀ g, e g = GeneralLinearGroup.map (pLoc E u) g.1 := by
  intro E _ _ _ n u hu
  have ho := orb_eq E hu
  have hmem : ∀ x : GLw n u, locGL E n u x ∈ Gam E n u := fun x =>
    ⟨locGL E n u x, gl_ext_pLoc E n fun w => by
      rw [pLoc_prjG, ho]
      split_ifs with hw
      · rfl
      · rw [pLoc_locGL_of_ne (by simpa using hw)]⟩
  refine ⟨{ toFun := fun g => GeneralLinearGroup.map (pLoc E u) g.1
            invFun := fun x => ⟨locGL E n u x, hmem x⟩
            left_inv := ?_
            right_inv := fun x => pLoc_locGL u x
            map_mul' := fun g h => map_mul (GeneralLinearGroup.map (pLoc E u)) g.1 h.1
            continuous_toFun := (continuous_comp_pLoc E n u).comp continuous_subtype_val
            continuous_invFun := (GlobalTheory.CuspRep.CuspSub.continuous_locGL u).subtype_mk hmem }, fun g => rfl⟩
  rintro ⟨g, x, rfl⟩
  refine Subtype.ext (gl_ext_pLoc E n fun w => ?_)
  by_cases hw : w = u
  · subst hw
    exact pLoc_locGL _ _
  · change GeneralLinearGroup.map (pLoc E w) (locGL E n u _) = GeneralLinearGroup.map (pLoc E w) (prjG E n (orb E u) x)
    rw [pLoc_locGL_of_ne hw, pLoc_prjG, ho, if_neg (by simpa using hw)]

end GlobalTheory.EulerTw.GamInert
