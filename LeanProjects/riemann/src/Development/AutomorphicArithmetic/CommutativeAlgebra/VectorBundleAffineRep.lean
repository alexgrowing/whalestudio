import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
import Development.AutomorphicArithmetic.CommutativeAlgebra.RepresentedByUnits
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

theorem UpperTheory.vector_bundle_affine_rep :
    ∀ (D : Type) [CommRing D] (d : ℕ) (U : (Spec (CommRingCat.of (MvPolynomial (Fin d) D))).Opens), IsCompl' (varIdeal (RingHom.id (MvPolynomial (Fin d) D))) U → ∃ φ : (Vec D d).psh ⟶ yoneda.obj (U : Scheme.{0}), (∀ (T : Scheme.{0}) (x : (Vec D d).obj Γ(T, ⊤)), φ.app (op T) x ≫ U.ι = specOf (ringOf ((Vec.toAff d).app _ x))) ∧ ∀ T : Scheme.{0}, IsAffine T → Function.Bijective (φ.app (op T)) := by
  intro D _ d U hU
  refine UpperTheory.represented_by_units (varIdeal (RingHom.id (MvPolynomial (Fin d) D))) U hU (Vec D d).psh
    (fun T x => ringOf ((Vec.toAff d).app Γ(T, ⊤) x)) ?_ ?_ ?_
  · intro T T' f x
    exact ringOf_map D f.appTop.hom ((Vec.toAff d).app Γ(T, ⊤) x)
  · intro T x
    rw [map_varIdeal, ← x.2]
    congr 2
    funext j
    simp [ringOf, Vec.toAff]
  · intro T ξ hξ
    rw [map_varIdeal] at hξ
    refine ⟨⟨(ξ.comp MvPolynomial.C, fun j => ξ (MvPolynomial.X j)), hξ⟩, ?_, ?_⟩
    · refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
      · simp [ringOf, Vec.toAff]
      · simp [ringOf, Vec.toAff]
    · intro y hy
      subst hy
      refine Subtype.ext (Prod.ext ?_ ?_)
      · ext c
        simp [ringOf, Vec.toAff]
      · funext j
        simp [ringOf, Vec.toAff]
