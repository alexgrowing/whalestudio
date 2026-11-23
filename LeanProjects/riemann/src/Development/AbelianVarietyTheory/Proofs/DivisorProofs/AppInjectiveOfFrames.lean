import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.SubPull

theorem app_injective_of_frames {X : Scheme.{0}} {F E : X.Modules} (φ : F ⟶ E) {U V : X.Opens}
    {ι κ : Type} [Fintype ι] [Fintype κ] {e : ι → Γ(F, U)} {b : ι ⊕ κ → Γ(E, U)}
    (he : IsFrame e) (hb : IsFrame b) (hφ : ∀ j, φ.app U (e j) = b (.inl j)) (h : V ≤ U) :
    Function.Injective (φ.app V) := by
  have li : LinearIndependent Γ(X, V) (appLinear φ V ∘ he.basis h) := by
    have := (hb.basis h).linearIndependent.comp Sum.inl Sum.inl_injective
    convert this using 1
    funext j
    simp only [Function.comp_apply, IsFrame.basis_apply, appLinear_apply, app_resM, hφ]
  have : Function.Injective (appLinear φ V) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have h0 := Fintype.linearIndependent_iff.1 li ((he.basis h).repr x) (by
      rw [← hx]
      conv_rhs => rw [← (he.basis h).sum_repr x]
      simp only [map_sum, map_smul, Function.comp_apply])
    exact (he.basis h).ext_elem fun j => by simp [h0 j]
  exact this

theorem isSubbundle_pullback : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (F E : X.Modules) (i : F ⟶ E) (r : ℕ), IsVB F r → IsSubbundle i → IsSubbundle ((Scheme.Modules.pullback f).map i) := by
  intro X Y f F E i r hF ⟨hm, s, hs⟩
  have hS : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
    { exact := ShortComplex.exact_cokernel i }
  refine ⟨QCoh.mono_of_locally_app_injective _ fun W y hy => ?_, s,
    (hs.pullback f).of_iso (PreservesCokernel.iso (Scheme.Modules.pullback f) i)⟩
  have h₁ : SheafOfModules.IsQuasicoherent
      (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).X₁ := hF.isQuasicoherent
  have h₂ : SheafOfModules.IsQuasicoherent
      (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).X₂ :=
    (VBExt.isVB_and_cls_det_of_shortExact X _ r s hS hF hs).1.isQuasicoherent
  obtain ⟨c, hc⟩ := VBExt.exists_adaptedChart hS hF hs (f y)
  refine ⟨W ⊓ f ⁻¹ᵁ c.U, ⟨hy, hc⟩, inf_le_left, ?_⟩
  exact app_injective_of_frames _ (c.he.pullback f)
    ((VBExt.isFrame_sumElim hS c.he c.ht).pullback f)
    (fun j => QCoh.pullback_map_app_pullbackSections f i _ _) inf_le_right

end GlobalTheory.SubPull
