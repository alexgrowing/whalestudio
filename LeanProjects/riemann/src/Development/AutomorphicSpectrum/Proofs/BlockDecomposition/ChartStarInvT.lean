import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
open NumberField IsDedekindDomain Topology Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec GlobalTheory.SmGL GlobalTheory.ThetaPull
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.DualAct

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem map_invT {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (invT a R g) = invT a S (GeneralLinearGroup.map p g) := by
  ext i j
  change p (((g⁻¹ : GL (Fin a) R).val) j i) = ((GeneralLinearGroup.map p g)⁻¹ : GL (Fin a) S).val j i
  rw [← map_inv]
  rfl

theorem invT_infGL (y : GL (Fin a) (Cinf E)) :
    invT a (Ad E) (infGL E a y) = infGL E a (invT a (Cinf E) y) :=
  ga_ext (by rw [map_invT, pInf_infGL, pInf_infGL])
    (by rw [map_invT, pFin_infGL, pFin_infGL, map_one])

theorem invT_finGL (k : GL (Fin a) (Af E)) :
    invT a (Ad E) (finGL E a k) = finGL E a (invT a (Af E) k) :=
  ga_ext (by rw [map_invT, pInf_finGL, pInf_finGL, map_one])
    (by rw [map_invT, pFin_finGL, pFin_finGL])

theorem invT_toUnits (k : Kinf E a) :
    invT a (Cinf E) (Unitary.toUnits k) = Unitary.toUnits (barK k) := by
  ext i j
  rfl

omit [IsTotallyComplex E] in
variable (E a) in

def trL : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (Matrix.of X)ᵀ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

omit [IsTotallyComplex E] in
theorem trL_apply (X : Lie E a) : trL E a X = toL (Matrix.of X)ᵀ := rfl

omit [IsTotallyComplex E] in

theorem toL_invT (y : GL (Fin a) (Cinf E)) :
    toL (invT a (Cinf E) y).val = trL E a (GlobalTheory.ThetaPull.invL (toL y.val)) := by
  rw [trL_apply, GlobalTheory.ThetaPull.invL]
  change toL ((y⁻¹ : GL (Fin a) (Cinf E)).val)ᵀ = toL (Matrix.of (Matrix.of.symm (Matrix.of.symm y.val |> Matrix.of)⁻¹))ᵀ
  simp [Matrix.coe_units_inv]

theorem chart_star_invT (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => star (φ (invT a (Ad E) g))) g x =
      star (chart φ (invT a (Ad E) g) (trL E a (GlobalTheory.ThetaPull.invL x))) := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [← toL_invT, chart_val, chart_val, map_mul, invT_infGL]

theorem lieD_star_invT (X : Lie E a) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) :
    lieD X (fun g => star (φ (invT a (Ad E) g))) g =
      star (lieD (toL (-(Matrix.of X)ᵀ)) φ (invT a (Ad E) g)) := by
  have e : chart (fun g => star (φ (invT a (Ad E) g))) g =ᶠ[𝓝 (oneL E a)]
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ chart φ (invT a (Ad E) g) ∘ trL E a ∘ GlobalTheory.ThetaPull.invL :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => chart_star_invT φ g hx
  have h1 : (trL E a ∘ GlobalTheory.ThetaPull.invL) (oneL E a) = oneL E a :=
    (toL_invT 1).symm.trans (by rw [map_one]; rfl)
  have h2 := HasFDerivAt.comp (oneL E a) (f := trL E a ∘ GlobalTheory.ThetaPull.invL)
    (by rw [h1]; exact (differentiableAt_chart hφ (invT a (Ad E) g)).hasFDerivAt)
    ((trL E a).hasFDerivAt.comp (oneL E a) GlobalTheory.ThetaPull.invL_smooth.2)
  have h3 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp (oneL E a) h2
  unfold lieD
  rw [e.fderiv_eq, h3.fderiv]
  have e2 : toL (-(Matrix.of X)ᵀ) = -(toL (Matrix.of X)ᵀ : Lie E a) := rfl
  simp [trL_apply]
  rw [e2, map_neg, map_neg]

theorem act_star_invT (o : Op E a) (φ ψ χ : Sm E a)
    (hψ : ∀ g, ψ.1 g = star (φ.1 (invT a (Ad E) g)))
    (hχ : ∀ g, χ.1 g = star ((act (invTOp o) φ).1 (invT a (Ad E) g))) :
    act o ψ = χ := by
  refine Subtype.ext <| funext fun g => ?_
  rw [hχ]
  cases o with
  | fin k =>
    change ψ.1 (g * finGL E a k) = star (φ.1 (invT a (Ad E) g * finGL E a (invT a (Af E) k)))
    rw [hψ, map_mul, invT_finGL]
  | cpt k =>
    change ψ.1 (g * infGL E a (Unitary.toUnits k)) =
      star (φ.1 (invT a (Ad E) g * infGL E a (Unitary.toUnits (barK k))))
    rw [hψ, map_mul, invT_infGL, invT_toUnits]
  | lie X =>
    have e : ψ.1 = fun g => star (φ.1 (invT a (Ad E) g)) := funext hψ
    change lieD X ψ.1 g = star (lieD (toL (-(Matrix.of X)ᵀ)) φ.1 (invT a (Ad E) g))
    rw [e, lieD_star_invT X φ.2 g]

end GlobalTheory.CompanionTheory.DualAct
