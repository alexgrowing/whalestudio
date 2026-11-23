import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFiniteTypeIntOfModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNoetherianPadicImageFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLocalHomAdicCompletionExtendStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionRingHomExtPadicAlgClosureStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.ClassicalPt

theorem extend_completion : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z) (R : Type) [CommRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), y (cPt p) = x → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ev₀ : R →+* V) (i : V →+* OO p), IsAdicComplete (maximalIdeal V) V ∧ IsLocalHom ev₀ ∧ IsLocalHom i ∧ Function.Injective i ∧ spMap (i.comp ev₀) ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y ∧ ∀ ev : R →+* OO p, spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ev = i.comp ev₀ := by
  intro o' Ω _ _ _ _ M x R _ j hj p _ y hy
  obtain ⟨φ, hφl, hφ, hφu⟩ := GlobalTheory.T.exists_unique_stalkHom_padicAlgClosure_valuation M.Z x p y hy
  obtain ⟨U, hU, hxU, hft⟩ := GlobalTheory.T.exists_affineOpen_finiteType_int_of_model o' Ω M x
  obtain ⟨hN, K, hK, hφK⟩ := GlobalTheory.T.stalk_noetherian_padicImage_finiteExtension M.Z U hU x hxU hft p φ
  obtain ⟨hdvr, hcpl, -⟩ := GlobalTheory.intRing_complete_dvr p K hK
  obtain ⟨e, he⟩ := hj
  let i : GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K →+* OO p :=
    RingHom.codRestrict ((algebraMap K (PadicAlgCl p)).comp (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K).subtype) (OO p) (fun v => v.2)
  let ψK : M.Z.presheaf.stalk x →+* K :=
    RingHom.codRestrict ((OO p).subtype.comp φ) K (fun a => hφK a)
  let ψ : M.Z.presheaf.stalk x →+* GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K :=
    RingHom.codRestrict ψK (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) (fun a => (φ a).2)
  have hiψ : ∀ a, i (ψ a) = φ a := fun a => rfl
  have hil : IsLocalHom i := ⟨fun v hv => by
    obtain ⟨w, hw⟩ := hv.exists_right_inv
    have hw' : algebraMap K (PadicAlgCl p) (v : K) * (w : PadicAlgCl p) = 1 :=
      congrArg Subtype.val hw
    have h0 : (v : K) ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hw'
      exact zero_ne_one hw'
    refine isUnit_iff_exists_inv.2 ⟨⟨(v : K)⁻¹, ?_⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
    show algebraMap K (PadicAlgCl p) (v : K)⁻¹ ∈ OO p
    rw [map_inv₀, inv_eq_of_mul_eq_one_right hw']
    exact w.2⟩
  have hψl : IsLocalHom ψ := ⟨fun a ha => hφl.map_nonunit a (by rw [← hiψ]; exact ha.map i)⟩
  haveI := hN
  haveI := hcpl
  obtain ⟨ev', hev'l, hev'⟩ := GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_apply (M.Z.presheaf.stalk x) (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ψ hψl
  have hej : ∀ a, e.symm (j a) = algebraMap _ _ a := fun a => by rw [← he a, e.symm_apply_apply]
  let ev₀ : R →+* GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K := ev'.comp e.symm.toRingHom
  have hcomp : (i.comp ev₀).comp j = φ := RingHom.ext fun a => by
    show i (ev' (e.symm (j a))) = φ a
    rw [hej, hev', hiψ]
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K, inferInstance, inferInstance, hdvr, ev₀, i, hcpl, ?_, hil, ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_⟩
    have h1 := hev'l.map_nonunit _ hr
    have h2 := h1.map e.toRingHom
    simpa using h2
  · intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext ((algebraMap K (PadicAlgCl p)).injective h)
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp, hφ]
  · intro ev hev
    have h1 : ev.comp j = φ := hφu _ (by
      rw [← hev, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
    have hf : (ev.comp e.toRingHom).comp (algebraMap _ _) = φ := RingHom.ext fun a => by
      rw [← h1]; simp [he]
    have h2 := GlobalTheory.T.adicCompletion_ringHom_ext_padicAlgClosure (M.Z.presheaf.stalk x) p (ev.comp e.toRingHom) ((i.comp ev₀).comp e.toRingHom)
      (by rw [hf]; exact hφl) (fun a => by
        have := congrArg (fun F => F a) hf
        have h3 := congrArg (fun F => F a) hcomp
        simp only [RingHom.comp_apply] at this h3
        change ev (e (algebraMap _ _ a)) = i (ev₀ (e (algebraMap _ _ a)))
        rw [he, h3, ← h1]
        rfl)
    refine RingHom.ext fun r => ?_
    have := congrArg (fun F => F (e.symm r)) h2
    simpa using this

end GlobalTheory.ClassicalPt
