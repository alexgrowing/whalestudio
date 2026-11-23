import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesNatural
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe w u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}} [X.Over (Spec (.of A))]
  (F : X.Modules)

abbrev reesPush : X.Modules := (Scheme.Modules.pushforward (reesPr I X)).obj (reesSheaf I F)

def reesMul (r : reesAlgebra I) : reesPush I F ⟶ reesPush I F :=
  (Scheme.Modules.pushforward (reesPr I X)).map
    (smulHom (reesSheaf I F) (algebraMap (reesAlgebra I) Γ(reesScheme I X, ⊤) r))

lemma reesMul_one : reesMul I F 1 = 𝟙 _ := by
  rw [reesMul, map_one, ← smulRingHom_apply, map_one]
  exact (Scheme.Modules.pushforward (reesPr I X)).map_id _

lemma reesMul_mul (r s : reesAlgebra I) : reesMul I F (r * s) = reesMul I F s ≫ reesMul I F r := by
  rw [reesMul, reesMul, reesMul, map_mul, ← smulRingHom_apply, map_mul, ← Functor.map_comp]
  rfl

lemma reesMul_zero : reesMul I F 0 = 0 := by
  rw [reesMul, map_zero, ← smulRingHom_apply, map_zero]
  exact (Scheme.Modules.pushforward (reesPr I X)).map_zero _ _

lemma reesMul_add (r s : reesAlgebra I) : reesMul I F (r + s) = reesMul I F r + reesMul I F s := by
  rw [reesMul, reesMul, reesMul, map_add, ← smulRingHom_apply, map_add]
  exact (Scheme.Modules.pushforward (reesPr I X)).map_add

variable {ι : Type w} (𝔘 : ι → X.Opens) (p : ℕ)

abbrev reesPre : (Opens X.toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{u} := (modulesAb (reesPush I F)).obj

def reesCechRingHom : reesAlgebra I →+* AddMonoid.End (cechH (reesPre I F) 𝔘 p) where
  toFun r := cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p
  map_one' := by
    ext x
    change cechHMap 𝔘 (modulesAbMap (reesMul I F 1)).hom p x = x
    rw [reesMul_one, modulesAbMap_id]
    exact cechHMap_id 𝔘 p x
  map_mul' r s := by
    ext x
    change cechHMap 𝔘 (modulesAbMap (reesMul I F (r * s))).hom p x =
      cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p (cechHMap 𝔘 (modulesAbMap (reesMul I F s)).hom p x)
    rw [reesMul_mul, modulesAbMap_comp, ← cechHMap_comp]
    rfl
  map_zero' := by
    ext x
    change cechHMap 𝔘 (modulesAbMap (reesMul I F 0)).hom p x = 0
    rw [reesMul_zero]
    exact cechHMap_zero 𝔘 p x
  map_add' r s := by
    ext x
    change cechHMap 𝔘 (modulesAbMap (reesMul I F (r + s))).hom p x =
      cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p x +
        cechHMap 𝔘 (modulesAbMap (reesMul I F s)).hom p x
    rw [reesMul_add, modulesAbMap_add]
    exact cechHMap_add 𝔘 _ _ p x

@[instance_reducible]
def reesCechModule : Module (reesAlgebra I) (cechH (reesPre I F) 𝔘 p) :=
  Module.compHom _ (reesCechRingHom I F 𝔘 p)

variable [IsNoetherianRing A] [IsProper (X ↘ Spec (.of A))] {F} (hF : IsCoherent F)
  (hU : iSup 𝔘 = ⊤) (hUaff : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a)))

omit [IsNoetherianRing A] [IsProper (X ↘ Spec (.of A))] in
include hF hU hUaff in

theorem exists_reesCech_addEquiv :
    ∃ e : cechH (reesPre I F) 𝔘 p ≃+ Sheaf.H.{u} (modulesAb (reesSheaf I F)) p,
      ∀ (r : reesAlgebra I) x, e (cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p x) = r • e x := by
  have : (reesSheaf I F).IsQuasicoherent := (isCoherent_reesSheaf hF).1
  set pr := reesPr I X
  have hUr : ⨆ k, pr ⁻¹ᵁ 𝔘 k = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hU]
    rfl
  have hUraff : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, pr ⁻¹ᵁ 𝔘 (t a)) := fun m t => by
    have h := preimage_inter pr 𝔘 t
    rw [← inter_eq_iInf (fun k => pr ⁻¹ᵁ 𝔘 k) t, ← h, inter_eq_iInf]
    exact (hUaff m t).preimage pr
  refine ⟨(cechHPushforwardEquiv pr (reesSheaf I F) 𝔘 p).trans
    (cechHAddEquivH (fun k => pr ⁻¹ᵁ 𝔘 k) hUr hUraff (reesSheaf I F) p), fun r x => ?_⟩
  simp only [AddEquiv.trans_apply]
  rw [cechHPushforwardEquiv_naturality pr (reesSheaf I F) 𝔘 p _
    (modulesAbMap (smulHom (reesSheaf I F)
      (algebraMap (reesAlgebra I) Γ(reesScheme I X, ⊤) r))).hom (fun W y => rfl) x,
    cechHAddEquivH_naturality]
  rfl

include hF hU hUaff in

theorem finite_reesCech :
    @Module.Finite (reesAlgebra I) (cechH (reesPre I F) 𝔘 p) _ _ (reesCechModule I F 𝔘 p) := by
  let := reesCechModule I F 𝔘 p
  obtain ⟨e, he⟩ := exists_reesCech_addEquiv I 𝔘 p hF hU hUaff
  have := finite_H_of_isProper (A := reesAlgebra I) (reesSheaf I F) (isCoherent_reesSheaf hF) p
  exact Module.Finite.equiv (e.toLinearEquiv fun r x => he r x).symm

end

end GroundTheory.Arith.SchemeCoh
