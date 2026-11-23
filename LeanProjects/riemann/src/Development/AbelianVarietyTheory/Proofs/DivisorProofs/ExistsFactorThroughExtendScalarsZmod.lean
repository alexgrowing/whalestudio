import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

namespace FactorExt

theorem intCast_surj (Q : ℕ) : Function.Surjective (Int.cast : ℤ → ULift.{1} (ZMod Q)) := by
  intro r
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective r.down
  exact ⟨z, ULift.ext _ _ (by simp [hz])⟩

theorem map_smul_of_add {A B M N : Type*} [Ring A] [Ring B] (f : A →+* B)
    (hA : Function.Surjective (Int.cast : ℤ → A)) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (g : M →+ N) (r : A) (m : M) : g (r • m) = f r • g m := by
  obtain ⟨z, rfl⟩ := hA r
  rw [Int.cast_smul_eq_zsmul, map_zsmul, map_intCast, Int.cast_smul_eq_zsmul]

variable {R S : Type} [CommRing R] [CommRing S]

theorem extSh_hom_ext (φ : R →+* S) {F : Shv R} {G : Shv S} (f g : (extSh φ).obj F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (a : Sec F U), Sec.map f (extSh.sec φ F U a) = Sec.map g (extSh.sec φ F U a)) : f = g := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := Scheme.etaleTopology) (P := F.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ))
    f.hom g.hom G.cond ?_
  ext U : 2
  apply (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext a
  exact h (unop U) a

end FactorExt

end GlobalTheory.EtC

end

noncomputable section

namespace GlobalTheory.EtC

namespace FactorExt

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
  (hR : Function.Surjective (Int.cast : ℤ → ULift.{1} R)) {I : Cx R} {K : Cx S} (ρ : SemiMap I K)
include hR

def lin (s : ℤ) (U : Scheme.{0}) :
    (I.X s).obj.obj (op U) ⟶ (ModuleCat.restrictScalars (uliftHom φ)).obj ((K.X s).obj.obj (op U)) :=
  ModuleCat.ofHom (X := (I.X s).obj.obj (op U))
    (Y := (ModuleCat.restrictScalars (uliftHom φ)).obj ((K.X s).obj.obj (op U)))
    { toFun := ρ.app U s
      map_add' := map_add _
      map_smul' := fun r a => by
        exact map_smul_of_add (uliftHom φ) hR (ρ.app U s) r a }

def pre (s : ℤ) : (I.X s).obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ) ⟶ (K.X s).obj where
  app U := ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).homEquiv _ _).symm (lin φ hR ρ s (unop U))
  naturality {U V} g := by
    rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    ext a
    exact (ρ.nat g.unop s a).symm

def term (s : ℤ) : (extCx φ I).X s ⟶ K.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} S))).homEquiv _ _).symm (pre φ hR ρ s)

theorem term_sec (s : ℤ) (U : Scheme.{0}) (a : Sec (I.X s) U) :
    Sec.map (term φ hR ρ s) (extSh.sec φ (I.X s) U a) = ρ.app U s a := by
  have h1 : toSheafify Scheme.etaleTopology.{0} ((I.X s).obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ)) ≫
      (term φ hR ρ s).hom = pre φ hR ρ s := by
    have := Adjunction.homEquiv_unit (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} S)))
      _ _ (term φ hR ρ s)
    rw [sheafificationAdjunction_unit_app] at this
    exact this.symm.trans (Equiv.apply_symm_apply _ _)
  have h2 := Adjunction.homEquiv_unit (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)) _ _
    ((pre φ hR ρ s).app (op U))
  have e1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (NatTrans.congr_app h1 (op U)))
    (((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.app ((I.X s).obj.obj (op U))).hom a)
  have e2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h2) a
  simp only [pre, Equiv.apply_symm_apply] at e2
  exact e1.trans e2.symm

def hom : extCx φ I ⟶ K where
  f s := term φ hR ρ s
  comm' s t _ := by
    apply FactorExt.extSh_hom_ext φ
    intro U a
    show Sec.map (K.d s t) (Sec.map (term φ hR ρ s) (extSh.sec φ (I.X s) U a)) =
      Sec.map (term φ hR ρ t) (Sec.map ((extSh φ).map (I.d s t)) (extSh.sec φ (I.X s) U a))
    rw [term_sec, extSh.sec_map, term_sec, ρ.comm]

end FactorExt

theorem SemiMap.factor_extCx : ∀ (Q q : ℕ) (hq : q ∣ Q) (I : Cx (ZMod Q)) (K : Cx (ZMod q)) (ρ : SemiMap I K),
    ∃ u : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K, ∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U),
      ρ.app U s a = Sec.map (u.f s) ((extπ (ZMod.castHom hq (ZMod q)) I).app U s a) :=
  fun Q _ hq _ _ ρ => ⟨FactorExt.hom _ (FactorExt.intCast_surj Q) ρ,
    fun U s a => (FactorExt.term_sec (ZMod.castHom hq _) (FactorExt.intCast_surj Q) ρ s U a).symm⟩

end GlobalTheory.EtC

end
