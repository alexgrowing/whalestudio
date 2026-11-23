import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent GlobalTheory.LatGlue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)

set_option autoImplicit false

namespace GlobalTheory.LatGlue

theorem finite_projective_comap_of_range_eq {A B : Type} [CommRing A] [CommRing B] (γ : A →+* B)
    (hγ : Function.Injective γ) (R : Subring B) (hR : γ.range = R) {ι : Type} (L : Submodule B (ι → B))
    (M : Submodule R (ι → R)) (hM : ∀ a : ι → R, a ∈ M ↔ (fun i => (a i : B)) ∈ L)
    [Module.Finite R M] [Module.Projective R M] :
    Module.Finite A (L.comap (piMap γ ι)) ∧ Module.Projective A (L.comap (piMap γ ι)) := by
  subst hR
  let e : A ≃+* γ.range := RingEquiv.ofBijective γ.rangeRestrict
    ⟨fun x y hxy => hγ (congrArg Subtype.val hxy), γ.rangeRestrict_surjective⟩
  have he : ∀ x, ((e x : γ.range) : B) = γ x := fun _ => rfl
  have he' : ∀ y : γ.range, γ (e.symm y) = y := fun y => by rw [← he, e.apply_symm_apply]
  haveI := RingHomInvPair.of_ringEquiv e
  haveI := RingHomInvPair.of_ringEquiv e.symm
  haveI : RingHomInvPair (e.symm : γ.range →+* A) (e : A →+* γ.range) := RingHomInvPair.symm _ _
  let φ : M ≃ₛₗ[(e.symm : γ.range →+* A)] (L.comap (piMap γ ι)) :=
    { toFun := fun a => ⟨fun i => e.symm (a.1 i), by
        have := (hM a.1).1 a.2
        rw [Submodule.mem_comap]
        convert this using 1
        funext i
        rw [piMap_apply, he']⟩
      map_add' := fun a b => Subtype.ext (funext fun i => by simp)
      map_smul' := fun c a => Subtype.ext (funext fun i => by simp)
      invFun := fun v => ⟨fun i => e (v.1 i), (hM _).2 v.2⟩
      left_inv := fun a => Subtype.ext (funext fun i => by simp)
      right_inv := fun v => Subtype.ext (funext fun i => by simp) }
  exact ⟨Module.Finite.of_surjective φ.toLinearMap φ.surjective, Module.Projective.of_equiv φ⟩

theorem finite_projective_comap_of_isDescended : ∀ (X : Scheme.{0}) [IsIntegral X] (K' : IntermediateField X.functionField (Kbar X)) (U : AffOp X) (A : Type) [CommRing A] (γ : A →+* U.Bp), Function.Injective γ → γ.range = ringOver K' U → ∀ (h : ℕ) (L : Submodule U.Bp (Fin h → U.Bp)), IsDescended K' U L → Module.Finite A (L.comap (piMap γ (Fin h))) ∧ Module.Projective A (L.comap (piMap γ (Fin h))) := by
  intro X _ K' U A _ γ hγ hR h L hL
  haveI := hL.1
  haveI := hL.2.1
  exact finite_projective_comap_of_range_eq γ hγ _ hR L (descMod K' U L) (fun _ => mem_descMod)

end GlobalTheory.LatGlue
