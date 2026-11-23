import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul)
open GlobalTheory.LB (resG_resG resG_self)

namespace GlobalTheory.UniColFrame

theorem det_uniR {R : Type*} [CommRing R] {m : ℕ} (n : Low m → R) : (uniR n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (uniR n)]
  · exact Finset.prod_eq_one fun a _ => by simp [uniR_apply]
  · intro a b h
    have h' : a < b := h
    simp [uniR_apply, h'.not_gt, h'.ne]

theorem isFrame_cols {X : Scheme.{0}} {F : X.Modules} {V : X.Opens} {m : ℕ} {e : Fin m → Γ(F, V)}
    (he : IsFrame e) (M : Matrix (Fin m) (Fin m) Γ(X, V)) (hM : IsUnit M.det) :
    IsFrame fun j => ∑ l, M l j • e l := fun W h => by
  have hM' : IsUnit (M.map (resG X h)).det := by
    have := hM.map (resG X h)
    rwa [RingHom.map_det] at this
  have hb : Function.Bijective (M.map (resG X h)).mulVec :=
    ⟨Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hM'),
      Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hM')⟩
  have key : ⇑(Fintype.linearCombination Γ(X, W) fun j => resM F h (∑ l, M l j • e l)) =
      ⇑(Fintype.linearCombination Γ(X, W) fun i => resM F h (e i)) ∘ (M.map (resG X h)).mulVec := by
    funext a
    simp only [Function.comp_apply, Fintype.linearCombination_apply, map_sum, resM_smul,
      Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul, Matrix.map_apply, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [key]
  exact (he W h).comp hb

theorem isFrame_pullCol_uniR : ∀ (X B : Scheme.{0}) (g : X ⟶ B) (E : B.Modules) (m : ℕ), IsVB E m → ∀ (U : B.Opens) (e : Fin m → Γ(E, U)), IsFrame e → ∀ (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U) (n : Low m → Γ(X, V)), IsFrame (pullCol g e hV (uniR n)) := by
  intro X B g E m hE U e he V hV n
  have := hE.isQuasicoherent
  have h1 : IsFrame fun i => QCoh.pullbackSections g E hV (e i) := by
    have h2 := (he.pullback g).res hV
    have h3 : (fun i => resM _ hV (QCoh.pullbackSections g E (le_refl (g ⁻¹ᵁ U)) (e i))) =
        fun i => QCoh.pullbackSections g E hV (e i) :=
      funext fun i => QCoh.res_pullbackSections g E _ _ _
    rwa [h3] at h2
  exact isFrame_cols h1 (uniR n) (by rw [det_uniR]; exact isUnit_one)

end GlobalTheory.UniColFrame
