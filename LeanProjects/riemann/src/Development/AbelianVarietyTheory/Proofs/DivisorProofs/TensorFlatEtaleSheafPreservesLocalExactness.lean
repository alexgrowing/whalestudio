import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionwiseTensorPresheafLocallyBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC
namespace TensFlat

variable {R : Type} [CommRing R]

theorem rl_comm {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module (ULift.{1} R) M] [Module (ULift.{1} R) N] [Module (ULift.{1} R) P] [Module (ULift.{1} R) Q]
    (f : M →ₗ[ULift.{1} R] P) (g : N →ₗ[ULift.{1} R] Q) (x : TensorProduct (ULift.{1} R) M N) :
    LinearMap.rTensor Q f (LinearMap.lTensor M g x) = LinearMap.lTensor P g (LinearMap.rTensor N f x) := by
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.comp_apply]

theorem tres_comp (X Y : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) {W V U : Scheme.{0}} (m : W ⟶ V) (k : V ⟶ U)
    (x : TensorProduct (ULift.{1} R) (X.obj (op U)) (Y.obj (op U))) :
    TensorProduct.map (X.map (m ≫ k).op).hom (Y.map (m ≫ k).op).hom x =
      TensorProduct.map (X.map m.op).hom (Y.map m.op).hom (TensorProduct.map (X.map k.op).hom (Y.map k.op).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem nat_apply {X Z : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (ψ : X ⟶ Z) {V U : Scheme.{0}} (k : V ⟶ U)
    (a : X.obj (op U)) : (Z.map k.op).hom ((ψ.app (op U)).hom a) = (ψ.app (op V)).hom ((X.map k.op).hom a) := by
  have h := congrArg (fun h => ModuleCat.Hom.hom h a) (ψ.naturality k.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

theorem tres_rTensor {X Z : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (Y : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    (ψ : X ⟶ Z) {V U : Scheme.{0}} (k : V ⟶ U) (x : TensorProduct (ULift.{1} R) (X.obj (op U)) (Y.obj (op U))) :
    TensorProduct.map (Z.map k.op).hom (Y.map k.op).hom (LinearMap.rTensor _ (ψ.app (op U)).hom x) =
      LinearMap.rTensor _ (ψ.app (op V)).hom (TensorProduct.map (X.map k.op).hom (Y.map k.op).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, nat_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tres_lTensor (X : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) {Y Z : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)}
    (ψ : Y ⟶ Z) {V U : Scheme.{0}} (k : V ⟶ U) (x : TensorProduct (ULift.{1} R) (X.obj (op U)) (Y.obj (op U))) :
    TensorProduct.map (X.map k.op).hom (Z.map k.op).hom (LinearMap.lTensor _ (ψ.app (op U)).hom x) =
      LinearMap.lTensor _ (ψ.app (op V)).hom (TensorProduct.map (X.map k.op).hom (Y.map k.op).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, nat_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ker_tensor_loc {A B C : Shv R} (f : A ⟶ B) (g : B ⟶ C)
    (hex : ∀ U (b : Sec B U), Sec.map g b = 0 → Loc U fun V k => ∃ a : Sec A V, Sec.map f a = Sec.res k b)
    (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (W : Scheme.{0})
    (z : TensorProduct (ULift.{1} R) (LinearMap.ker (g.hom.app (op W)).hom) (P.obj (op W))) :
    Loc W fun W' n => ∃ y : TensorProduct (ULift.{1} R) (Sec A W') (P.obj (op W')),
      LinearMap.rTensor _ (f.hom.app (op W')).hom y = TensorProduct.map (B.obj.map n.op).hom (P.map n.op).hom
        (LinearMap.rTensor _ (LinearMap.ker (g.hom.app (op W)).hom).subtype z) := by
  induction z using TensorProduct.induction_on with
  | zero => exact loc_of_forall W _ fun W' n => ⟨0, by simp⟩
  | tmul b p =>
    refine loc_mono W _ _ (hex W b.1 (LinearMap.mem_ker.mp b.2)) ?_
    rintro W' n ⟨a, ha⟩
    refine ⟨a ⊗ₜ (P.map n.op).hom p, ?_⟩
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, Submodule.coe_subtype]
    exact congrArg (· ⊗ₜ[ULift.{1} R] (P.map n.op).hom p) ha
  | add z₁ z₂ h₁ h₂ =>
    refine loc_mono W _ _ (loc_and W _ _ h₁ h₂) ?_
    rintro W' n ⟨⟨y₁, e₁⟩, ⟨y₂, e₂⟩⟩
    exact ⟨y₁ + y₂, by simp only [map_add, e₁, e₂]⟩

end TensFlat

open TensFlat in

theorem tensor_flat_loc_exact : ∀ (R : Type) [CommRing R] (M : Shv R), FlatS M → ∀ {A B C : Shv R} (f : A ⟶ B) (g : B ⟶ C), f ≫ g = 0 → (∀ U (b : Sec B U), Sec.map g b = 0 → Loc U fun V k => ∃ a : Sec A V, Sec.map f a = Sec.res k b) → ∀ U (x : TensorProduct (ULift.{1} R) (Sec B U) (Sec M U)), (Loc U fun V k => LinearMap.rTensor _ (g.hom.app (op V)).hom (TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x) = 0) → Loc U fun V k => ∃ y : TensorProduct (ULift.{1} R) (Sec A V) (Sec M V), LinearMap.rTensor _ (f.hom.app (op V)).hom y = TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x := by
  intro R _ M hM A B C f g _ hex U x hx
  obtain ⟨P, φ, hsurj, hinj, hflat⟩ := hM
  have h1 := (GlobalTheory.T.sectionwiseTensor_presheaf_locallyBijective R B.obj P M.obj φ hsurj hinj U).1 x
  apply loc_trans
  refine loc_mono U _ _ (loc_and U _ _ h1 hx) ?_
  rintro V k ⟨⟨x', hx'⟩, hz⟩
  have hz0 : LinearMap.lTensor _ (φ.app (op V)).hom (LinearMap.rTensor _ (g.hom.app (op V)).hom x') = 0 := by
    rw [← rl_comm, hx']
    exact hz
  have h2 := (GlobalTheory.T.sectionwiseTensor_presheaf_locallyBijective R C.obj P M.obj φ hsurj hinj V).2 _ hz0
  apply loc_trans
  refine loc_mono V _ _ h2 ?_
  intro W m hm
  have hg0 : LinearMap.rTensor _ (g.hom.app (op W)).hom
      (TensorProduct.map (B.obj.map m.op).hom (P.map m.op).hom x') = 0 := by
    rw [← tres_rTensor]; exact hm
  by_cases hW : Nonempty W
  · haveI := hflat W hW
    have hexact := Module.Flat.rTensor_exact (P.obj (op W))
      (LinearMap.exact_subtype_ker_map (g.hom.app (op W)).hom)
    obtain ⟨z, hzx⟩ := (hexact _).mp hg0
    refine loc_mono W _ _ (ker_tensor_loc f g hex P W z) ?_
    rintro W' n ⟨y, hy⟩
    refine ⟨LinearMap.lTensor _ (φ.app (op W')).hom y, ?_⟩
    rw [rl_comm, hy, hzx, tres_comp, tres_comp, ← hx', tres_lTensor, tres_lTensor]
  · haveI : IsEmpty W := not_nonempty_iff.mp hW
    exact loc_of_isEmpty W _

end GlobalTheory.EtC
