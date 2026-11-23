import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HolUnifScale

variable {g : ℕ}

def scaleLin (lam : Fin g → ℂ) (h : ∀ j, lam j ≠ 0) : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) where
  toFun w := fun j ↦ lam j * w j
  invFun w := fun j ↦ (lam j)⁻¹ * w j
  map_add' a b := by funext j; simp [mul_add]
  map_smul' c a := by funext j; simp; ring
  left_inv w := by funext j; exact inv_mul_cancel_left₀ (h j) _
  right_inv w := by funext j; exact mul_inv_cancel_left₀ (h j) _

def scale (lam : Fin g → ℂ) (h : ∀ j, lam j ≠ 0) : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
  (scaleLin lam h).toContinuousLinearEquiv

@[simp] lemma scale_apply (lam : Fin g → ℂ) (h : ∀ j, lam j ≠ 0) (w : Fin g → ℂ) :
    scale lam h w = fun j ↦ lam j * w j := rfl

variable {A : Over (Sp ℂ)} [GrpObj A] {Lb : LB A.left}

def latPull (u : HolUnif A Lb g) (lam : Fin g → ℂ) (h : ∀ j, lam j ≠ 0) : Submodule ℤ (Fin g → ℂ) :=
  ZLattice.comap ℝ u.Λ ((scaleLin lam h).restrictScalars ℝ).toLinearMap

lemma mem_latPull (u : HolUnif A Lb g) (lam : Fin g → ℂ) (h : ∀ j, lam j ≠ 0) (z : Fin g → ℂ) :
    z ∈ latPull u lam h ↔ scale lam h z ∈ u.Λ := Iff.rfl

def rescale (u : HolUnif A Lb g) (lam : Fin g → ℂ) (h : ∀ j, lam j ≠ 0) : HolUnif A Lb g where
  ex w := u.ex (scale lam h w)
  ex_add z w := by rw [map_add]; exact u.ex_add _ _
  ex_onto := u.ex_onto.comp (scale lam h).surjective
  Λ := latPull u lam h
  ker z := (u.ker _).trans (mem_latPull u lam h z).symm
  discrete := by
    haveI := u.discrete
    exact ZLattice.comap_discreteTopology ℝ u.Λ
      (LinearMap.continuous_of_finiteDimensional _) (LinearEquiv.injective _)
  full := by
    have hs : ((latPull u lam h : Submodule ℤ (Fin g → ℂ)) : Set (Fin g → ℂ)) =
        ((scaleLin lam h).restrictScalars ℝ).symm '' (u.Λ : Set (Fin g → ℂ)) := by
      rw [LinearEquiv.image_symm_eq_preimage]; rfl
    have he := Submodule.span_image (R := ℝ) (s := (u.Λ : Set (Fin g → ℂ)))
      ((scaleLin lam h).restrictScalars ℝ).symm.toLinearMap
    simp only [LinearEquiv.coe_coe] at he
    rw [hs, he, u.full, Submodule.map_top, LinearEquiv.range]
  hol U f := by
    obtain ⟨h1, h2⟩ := u.hol U f
    refine ⟨h1.preimage (scale lam h).continuous, ?_⟩
    exact h2.comp (scale lam h).differentiable.differentiableOn (fun z hz ↦ hz)
  fr i w := u.fr i (scale lam h w)
  fr_hol i := (u.fr_hol i).comp (scale lam h).differentiable.differentiableOn (fun z hz ↦ hz)
  fr_ne i z hz := u.fr_ne i _ hz
  fr_compat i j z hz := u.fr_compat i j _ hz

end GlobalTheory.HolUnifScale

namespace GlobalTheory.HolUnifScale

variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {Lb : LB A.left}

lemma diag_form (lam : Fin g → ℂ) (h : ∀ j, lam j ≠ 0) (d : Fin g → ℝ) (z l : Fin g → ℂ) :
    z ⬝ᵥ (Matrix.diagonal fun j ↦ ((d j * ‖lam j‖ ^ 2 : ℝ) : ℂ)).mulVec (star l) =
      scale lam h z ⬝ᵥ (Matrix.diagonal fun j ↦ (d j : ℂ)).mulVec (star (scale lam h l)) := by
  simp only [dotProduct, Matrix.mulVec_diagonal, scale_apply, Pi.star_apply, star_mul']
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  push_cast
  rw [← Complex.mul_conj', Complex.star_def]
  ring

lemma diag_herm (d : Fin g → ℝ) : (Matrix.diagonal fun j ↦ (d j : ℂ)).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext j; simp [Complex.conj_ofReal]

end GlobalTheory.HolUnifScale

open GlobalTheory.HolUnifScale in

theorem GlobalTheory.holUnif_rescale : ∀ (A : Over (Sp ℂ)) [GrpObj A] (Lb : LB A.left) (g : ℕ) (u : HolUnif A Lb g) (lam : Fin g → ℂ),
    (∀ j, lam j ≠ 0) → ∃ u' : HolUnif A Lb g, (∀ w, u'.ex w = u.ex (fun j ↦ lam j * w j)) ∧
      (∀ (d : Fin g → ℝ) χ, u.IsAH (Matrix.diagonal fun j ↦ (d j : ℂ)) χ →
        ∃ χ', u'.IsAH (Matrix.diagonal fun j ↦ ((d j * ‖lam j‖ ^ 2 : ℝ) : ℂ)) χ') ∧
      (∀ W v, u'.IsDiff W v ↔ u.IsDiff (fun j ↦ lam j * W j) v) := by
  intro A _ Lb g u lam h
  refine ⟨rescale u lam h, fun w ↦ rfl, ?_, ?_⟩
  · intro d χ ⟨_, hpos, hχ, hfr⟩
    refine ⟨fun l ↦ χ ⟨scale lam h l, l.2⟩, ?_, ?_, fun l ↦ hχ _, ?_⟩
    · have := diag_herm (fun j ↦ d j * ‖lam j‖ ^ 2)
      simpa using this
    · intro z hz
      rw [diag_form lam h d z z]
      exact hpos _ ((map_ne_zero_iff _ (scale lam h).injective).mpr hz)
    · intro l i z hz
      have e := hfr ⟨scale lam h l, l.2⟩ i (scale lam h z) hz
      show u.fr i (scale lam h z) = _ * _ * u.fr i (scale lam h (z + l))
      rw [diag_form lam h d z l, diag_form lam h d l l, map_add]
      exact e
  · intro W v
    unfold HolUnif.IsDiff
    have hf : ∀ (U : A.left.Opens) (f : Γ(A.left, U)),
        (fun z ↦ valAt' ((rescale u lam h).ex z).left U f) = (fun z ↦ valAt' (u.ex z).left U f) ∘ scale lam h :=
      fun _ _ ↦ rfl
    simp only [hf, ContinuousLinearEquiv.comp_right_fderiv, map_zero]
    rfl
