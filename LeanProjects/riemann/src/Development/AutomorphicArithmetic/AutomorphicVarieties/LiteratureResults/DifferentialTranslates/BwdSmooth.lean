import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.MatSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ApplySmooth

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def sandL (Z : HV E a) (x : Lie E a) : HV E a :=
  ⟨toL (Matrix.of x * Matrix.of Z.1 * star (Matrix.of x)), IsSelfAdjoint.conjugate Z.2 (Matrix.of x)⟩

private theorem contDiff_sandL (Z : HV E a) : ContDiff ℝ ∞ (sandL Z) := by
  obtain ⟨π, hπ⟩ := (HV E a).subtype.exists_leftInverse_of_injective (HV E a).ker_subtype
  have h1 : ContDiff ℝ ∞ fun x : Lie E a => (sandL Z x).1 := by
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    have e : (fun x : Lie E a => (sandL Z x).1 i j) =
        fun x : Lie E a => ∑ k, (∑ l, x i l * Z.1 l k) * star (x j k) := by
      funext x
      simp only [sandL, Matrix.of_symm_apply, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply]
    rw [e]
    have hs : ContDiff ℝ ∞ fun z : Cinf E => star z := (starL' ℝ (A := Cinf E)).contDiff
    refine ContDiff.sum fun k _ => ContDiff.mul (ContDiff.sum fun l _ => ContDiff.mul ?_ contDiff_const) (hs.comp ?_)
    all_goals fun_prop
  have e : sandL Z = fun x => LinearMap.toContinuousLinearMap π (sandL Z x).1 :=
    funext fun x => (LinearMap.congr_fun hπ _).symm
  rw [e]
  exact (LinearMap.toContinuousLinearMap π).contDiff.comp h1

end UpperTheory.V.Lit.Dr

open UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Dr.bwdSmooth :
    BwdSmooth := by
  intro E _ _ _ a ho U Ξ q w X j g x hx
  let y := GeneralLinearGroup.map (pInf E) g
  let s : GL (Fin a) (Af E) ⧸ U := QuotientGroup.mk (GeneralLinearGroup.map (pFin E) g)
  let L : Lie E a →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap
    (LinearMap.mulLeft ℝ y.val : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E))
  have hL : ∀ u : GL (Fin a) (Cinf E), L (toL u.val) = toL (y * u).val := fun _ => rfl
  have hS : ∀ (Z : HV E a) (u : GL (Fin a) (Cinf E)), sandL Z (toL u.val) = sand u Z := fun _ _ => rfl
  obtain ⟨u, hu⟩ := hx
  obtain rfl : x = toL u.val := hu.symm
  have hSL : ∀ Z : HV E a, ContDiffAt ℝ ∞ (fun z => sandL Z (L z)) (toL u.val) := fun Z =>
    ((contDiff_sandL Z).comp L.contDiff).contDiffAt
  have hw : ContDiffAt ℝ ∞ (fun z => w.1 s (sandL (hOne E a) (L z))) (toL u.val) := by
    refine ContDiffAt.comp (g := w.1 s) _ (Geo.contDiffAt_Om w s ?_) (hSL _)
    rw [hL, hS]
    exact sand_mem_cone _ hOne_mem_cone
  have hv' := applySmooth _ _ _ q _ (fun i z => (2 : ℝ) • sandL (hv (X i)) (L z)) _ hw fun i => (hSL _).const_smul _
  have hm : ∀ k, ContDiffAt ℝ ∞ (fun z => extGL (fun t => Ξ.mat t⁻¹ j k) (L z)) (toL u.val) := fun k => by
    refine ContDiffAt.comp (g := extGL fun t => Ξ.mat t⁻¹ j k) _ ?_ L.contDiff.contDiffAt
    rw [hL]
    exact (matSmooth E a Ξ j k).2.contDiffAt (isOpen_invSet.mem_nhds (val_mem_invSet _))
  have hall := ContDiffAt.sum (s := Finset.univ) fun k _ => (hm k).mul (contDiffAt_pi.1 hv' k)
  refine (hall.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet u)] with z hz
  obtain ⟨v, hv⟩ := hz
  obtain rfl : z = toL v.val := hv.symm
  rw [chart_val]
  simp only [map_mul, pInf_infGL, pFin_infGL, mul_one, hL, hS, extGL_val]
  rfl
