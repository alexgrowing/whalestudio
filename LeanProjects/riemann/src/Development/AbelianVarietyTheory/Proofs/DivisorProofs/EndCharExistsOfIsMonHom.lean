import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Eq8

theorem endChar_exists_of_isMonHom (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (_hB : GlobalTheory.Mum.Base R)
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (_hG : IsSemiAbelian G) (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (f : G ⟶ G) (hfm : IsMonHom f) :
    ∃ m, EndChar U f m := by
  have hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hp := isGrpPullback_pullback G (spMap (residue R))
  have e : ((Over.pullback (spMap (residue R))).map f).left ≫ pullback.fst G.hom (spMap (residue R)) =
      pullback.fst G.hom (spMap (residue R)) ≫ f.left := pullback.lift_fst _ _ _
  have hf₁ : IsMonHom ((Over.pullback (spMap (residue R))).map f) :=
    Out.PullGtPf.isMonHom_of_grpPullback hp hp f _ e
  obtain ⟨m, hm⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hr hp).2 _
    (GlobalTheory.TorusPart.gtTorus (U.gt 0) hr hp ≫ (Over.pullback (spMap (residue R))).map f) inferInstance
  refine ⟨m, fun κ _ a ha G₀ _ φ h f₀ hf => ?_⟩
  let σ : ResidueField R →+* κ := Ideal.Quotient.lift _ a fun x hx => ha x (by simpa using hx)
  have ea : a = σ.comp (residue R) := RingHom.ext fun _ => rfl
  have es : spMap a = spMap σ ≫ spMap (residue R) := by rw [← Spec.map_comp]; rfl
  let ψ : G₀.left ⟶ ((Over.pullback (spMap (residue R))).obj G).left :=
    pullback.lift φ (G₀.hom ≫ spMap σ) (by rw [Category.assoc, ← es, h.1.w])
  have hψ : ψ ≫ pullback.fst G.hom (spMap (residue R)) = φ := pullback.lift_fst _ _ _
  have k : IsGrpPullback G₀ ((Over.pullback (spMap (residue R))).obj G) (spMap σ) ψ :=
    hp.cancel (h.congr es hψ.symm) (pullback.lift_snd _ _ _)
  have e₀ : f₀.left ≫ ψ = ψ ≫ ((Over.pullback (spMap (residue R))).map f).left := hp.1.hom_ext
    (by rw [Category.assoc, hψ, hf, Category.assoc, e, ← Category.assoc, hψ])
    (by rw [Category.assoc, k.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, k.1.w])
  rw [← GlobalTheory.TorusPart.pullTorus_gtTorus (U.gt 0) hr ha hp h k ea hψ.symm,
    ← GlobalTheory.TorusPart.pullTorus_comp k k _ f₀ e₀, hm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]

end GlobalTheory.Poinc.Eq8
