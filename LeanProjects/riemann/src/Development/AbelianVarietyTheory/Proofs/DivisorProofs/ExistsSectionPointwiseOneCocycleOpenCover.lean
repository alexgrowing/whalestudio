import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverAlgebraPointLiesInCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFirstCohomologyAwayNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleLocalSectionsGlueBasicOpenCoverStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PtExt.CocSec

variable {R : Type} [CommRing R]

def liftU {D E : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] (t : D) (ψ : D →ₐ[R] E)
    (h : IsUnit (ψ t)) : Localization.Away t →ₐ[R] E :=
  IsLocalization.liftAlgHom (M := Submonoid.powers t) (f := ψ) (by
    rintro ⟨_, m, rfl⟩
    simpa using h.pow m)

theorem liftU_comp {D E : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] (t : D)
    (ψ : D →ₐ[R] E) (h : IsUnit (ψ t)) :
    (liftU t ψ h).comp (IsScalarTower.toAlgHom R D (Localization.Away t)) = ψ := by
  ext r
  simp [liftU]

theorem comp_liftU {D E E' : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] [CommRing E']
    [Algebra R E'] (t : D) (ψ : D →ₐ[R] E) (h : IsUnit (ψ t)) (θ : E →ₐ[R] E') :
    θ.comp (liftU t ψ h) = liftU t (θ.comp ψ) (h.map θ) := by
  apply IsLocalization.algHom_ext (Submonoid.powers t)
  ext r
  have h1 := DFunLike.congr_fun (liftU_comp t ψ h) r
  have h2 := DFunLike.congr_fun (liftU_comp t (θ.comp ψ) (h.map θ)) r
  simp only [AlgHom.comp_apply] at h1 h2 ⊢
  exact (congrArg θ h1).trans h2.symm

end GlobalTheory.PtExt.CocSec

end

open GlobalTheory.PtExt.CocSec in

theorem GlobalTheory.PtExt.CocSec.exists_section : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc W u → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), ∃ σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), Sm W (spOver ψ ≫ x) → σ E' (θ.comp ψ) - θ (σ E ψ) = u E E' θ (spOver ψ ≫ x) := by
  intro R _ X K W hW u hu D _ _ x
  obtain ⟨n, s, hs, hsm⟩ := GlobalTheory.T.exists_basicOpen_cover_algebraPoint_liesInCover R X K W hW D x
  classical
  let k : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E := fun a E _ _ ψ ↦
    if h : IsUnit (ψ (s a)) then
      u _ E (liftU (s a) ψ h) (spOver (IsScalarTower.toAlgHom R D (Localization.Away (s a))) ≫ x)
    else 0
  have hk : ∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
      k a E' (θ.comp ψ) - θ (k a E ψ) = u E E' θ (spOver ψ ≫ x) := by
    intro a E _ _ E' _ _ ψ θ h
    have h' : IsUnit ((θ.comp ψ) (s a)) := h.map θ
    simp only [k, dif_pos h, dif_pos h']
    rw [← comp_liftU (s a) ψ h θ, hu _ _ _ (liftU (s a) ψ h) θ _ (hsm a), ← Category.assoc,
      spOver_comp, liftU_comp]
    ring
  obtain ⟨e, he1, he2⟩ := GlobalTheory.T.cech_first_cohomology_away_natural R D n s hs (fun a b E _ _ ψ ↦ k a E ψ - k b E ψ)
    (fun a b E _ _ E' _ _ ψ θ ha hb ↦ by
      have h1 := hk a E E' ψ θ ha
      have h2 := hk b E E' ψ θ hb
      simp only [map_sub]
      linear_combination h1 - h2)
    (fun a b c E _ _ ψ _ _ _ ↦ by ring)
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.pointwiseCocycle_local_sections_glue_basicOpen_cover R X K W u hu D x n s hs (fun a E _ _ ψ ↦ k a E ψ + e a E ψ)
    (fun a E _ _ E' _ _ ψ θ ha ↦ by
      have h1 := hk a E E' ψ θ ha
      have h2 := he1 a E E' ψ θ ha
      simp only [map_add]
      linear_combination h1 + h2)
    (fun a b E _ _ ψ ha hb ↦ by
      have h := he2 a b E ψ ha hb
      linear_combination h)
  exact ⟨σ, hσ⟩
