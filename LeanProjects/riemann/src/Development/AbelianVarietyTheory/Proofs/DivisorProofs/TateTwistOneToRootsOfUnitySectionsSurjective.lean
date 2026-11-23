import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuValInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneToRootsOfUnitySectionsInjectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw

noncomputable section
namespace GlobalTheory.EtC.MuTw

theorem appTop_comp_apply' {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Γ(U, ⊤)) :
    (k ≫ g).appTop.hom a = k.appTop.hom (g.appTop.hom a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

theorem isUnit_natCast_of_hom {V U : Scheme.{0}} (g : V ⟶ U) (q : ℕ) (hq : IsUnit (q : Γ(U, ⊤))) :
    IsUnit (q : Γ(V, ⊤)) := by
  have := hq.map g.appTop.hom
  rwa [map_natCast] at this

theorem muVal_pow (q : ℕ) [NeZero q] {U : Scheme.{0}} (y : Sec (muS q) U) : muVal q y ^ q = 1 := by
  have hr := (mem_rootsOfUnity q _).1 (Additive.toMul (ULift.down (α := Additive (rootsOfUnity q Γ(U, ⊤))) y)).2
  change (( _ : Γ(U, ⊤)ˣ) : Γ(U, ⊤)) ^ q = 1
  rw [← Units.val_pow_eq_pow_val, hr, Units.val_one]

theorem etaS_lift_pow (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) (z : Sec (muS q) V) (a : ℕ)
    (h : muVal q z = ζ.1 ^ a) :
    Sec.map (etaS q) (ofRings.sec (twF q 1) V
      (Submodule.Quotient.mk (Finsupp.single ζ (ULift.up (a : ZMod q))))) = z := by
  refine (etaS_sec q V _).trans ((eta_mk q Γ(V, ⊤) ζ _).trans ?_)
  apply muVal_injective q V
  rw [h]
  change (((Additive.toMul (((a : ZMod q)) • Additive.ofMul (root q ζ)) : rootsOfUnity q Γ(V, ⊤)) :
    Γ(V, ⊤)ˣ) : Γ(V, ⊤)) = _
  rw [smul_eq, toMul_nsmul, toMul_ofMul, root_pow_coe, ZMod.val_natCast]
  exact (pow_eq_pow_mod a (prim_pow q ζ)).symm

end GlobalTheory.EtC.MuTw

namespace GlobalTheory.EtC.MuTw

theorem etaS_surjective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
    Function.Surjective ((etaS q).hom.app (op U)).hom := by
  intro q _ U hq y
  have hloc : Loc U fun V g => ∃ s : Sec (tw q 1) V, Sec.map (etaS q) s = Sec.res g y := by
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.1 U _ ?_
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq) ?_
    rintro V g ⟨ζ⟩
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 V _ _
      ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.1 ζ (muVal q (Sec.res g y)) (muVal_pow q _)) ?_
    rintro W k ⟨a, ha⟩
    refine ⟨_, etaS_lift_pow q W (Prim.map k.appTop.hom ζ) (Sec.res (k ≫ g) y) a ?_⟩
    rw [muVal_res, appTop_comp_apply', ← muVal_res, ha]
    rfl
  obtain ⟨S, hS, hSy⟩ := hloc
  choose s hs using hSy
  have hsh := (tw q 1).cond
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))),
    isSheaf_iff_isSheaf_of_type] at hsh
  let fam : Presieve.FamilyOfElements ((tw q 1).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) S.arrows :=
    fun V g hg => s V g hg
  have hfam : fam.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
    apply GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_injective q Z (isUnit_natCast_of_hom (g₁ ≫ f₁) q hq)
    change Sec.map (etaS q) (Sec.res g₁ (s _ f₁ h₁)) = Sec.map (etaS q) (Sec.res g₂ (s _ f₂ h₂))
    rw [etaS_res, etaS_res, hs, hs]
    apply muVal_injective q Z
    simp only [muVal_res]
    rw [← appTop_comp_apply', ← appTop_comp_apply', e]
  obtain ⟨x, hx, -⟩ := hsh S hS fam hfam
  refine ⟨x, ?_⟩
  have hsep := (muS q).cond
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))),
    isSheaf_iff_isSheaf_of_type] at hsep
  refine (hsep S hS).isSeparatedFor.ext (fun V g hg => ?_)
  change Sec.res g (Sec.map (etaS q) x) = Sec.res g y
  rw [← etaS_res]
  have h1 : Sec.res g x = s V g hg := hx g hg
  rw [h1, hs]

end GlobalTheory.EtC.MuTw
