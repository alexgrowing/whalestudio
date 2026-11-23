import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

noncomputable section

variable {B : Scheme.{0}} {q : ℕ}

private def prL (K I : Cx (ZMod q)) (n p : ℤ) :
    Cochain K I n →ₗ[ULift.{1} (ZMod q)] (K.X p ⟶ I.X (p + n)) where
  toFun α := α.v p (p + n) rfl
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private def mkC {K I : Cx (ZMod q)} {n : ℤ} (f : ∀ p, K.X p ⟶ I.X (p + n)) : Cochain K I n :=
  Cochain.mk fun p r h => f p ≫ eqToHom (by rw [h])

private theorem mkC_v {K I : Cx (ZMod q)} {n : ℤ} (f : ∀ p, K.X p ⟶ I.X (p + n)) (p : ℤ) :
    (mkC f).v p (p + n) rfl = f p := by
  simp [mkC]

private theorem coch_ext {K I : Cx (ZMod q)} {n : ℤ} {a b : Cochain K I n}
    (h : ∀ p, a.v p (p + n) rfl = b.v p (p + n) rfl) : a = b := by
  refine Cochain.ext _ _ fun p r hpr => ?_
  subst hpr
  exact h p

private def asm {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] {K I : Cx (ZMod q)} {n : ℤ}
    (f : ∀ p, M →ₗ[ULift.{1} (ZMod q)] (K.X p ⟶ I.X (p + n))) :
    M →ₗ[ULift.{1} (ZMod q)] Cochain K I n where
  toFun x := mkC fun p => f p x
  map_add' x y := coch_ext fun p => by
    rw [Cochain.add_v, mkC_v, mkC_v, mkC_v, map_add]
  map_smul' r x := coch_ext fun p => by
    rw [RingHom.id_apply, Cochain.smul_v, mkC_v, mkC_v, map_smul]

private theorem asm_v {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] {K I : Cx (ZMod q)} {n : ℤ}
    (f : ∀ p, M →ₗ[ULift.{1} (ZMod q)] (K.X p ⟶ I.X (p + n))) (x : M) (p : ℤ) :
    (asm f x).v p (p + n) rfl = f p x :=
  mkC_v (fun p => f p x) p

private theorem preL_v {K K' I : Cx (ZMod q)} (f : K' ⟶ K) (n p : ℤ) (α : Cochain K I n) :
    (preL f I n α).v p (p + n) rfl = f.f p ≫ α.v p (p + n) rfl := by
  change ((Cochain.ofHom f).comp α (zero_add n)).v p (p + n) rfl = _
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]

private def fanTP (C : B.Etale ⥤ Cx (ZMod q)) (I : Cx (ZMod q)) (n : ℤ) :
    Fan (fun p : ℤ => HP (C ⋙ HomologicalComplex.eval _ _ p) (I.X (p + n))) :=
  Fan.mk (TP C I n) fun p =>
    { app := fun U => ModuleCat.ofHom (prL (C.obj U.unop) I n p)
      naturality := fun U V a => by
        refine ModuleCat.hom_ext (LinearMap.ext fun α => ?_)
        exact preL_v (C.map a.unop) n p α }

private def fanLim (C : B.Etale ⥤ Cx (ZMod q)) (I : Cx (ZMod q)) (n : ℤ) : IsLimit (fanTP C I n) :=
  mkFanLimit _
    (fun s =>
      { app := fun U => ModuleCat.ofHom (asm (K := C.obj U.unop) (I := I) (n := n) fun p => ((s.proj p).app U).hom)
        naturality := fun U V a => by
          refine ModuleCat.hom_ext (LinearMap.ext fun x => coch_ext fun p => ?_)
          have h := congrArg (fun t => t.hom x) ((s.proj p).naturality a)
          exact (asm_v (K := C.obj V.unop) (I := I) (n := n) (fun p => ((s.proj p).app V).hom) _ p).trans
            (h.trans ((congrArg (fun t => (C.map a.unop).f p ≫ t)
              (asm_v (K := C.obj U.unop) (I := I) (n := n) (fun p => ((s.proj p).app U).hom) x p).symm).trans
              (preL_v (C.map a.unop) n p _).symm)) })
    (fun s p => by
      ext U x
      exact asm_v (K := C.obj U.unop) (I := I) (n := n) (fun p => ((s.proj p).app U).hom) x p)
    (fun s m hm => by
      ext U x
      refine coch_ext fun p => ?_
      refine Eq.trans ?_ (asm_v (K := C.obj U.unop) (I := I) (n := n) (fun p => ((s.proj p).app U).hom) x p).symm
      rw [← hm p]
      rfl)

theorem UpperTheory.totalHomPresheaf_isSheaf_injective_of_homAcyclic :
    ∀ (q : ℕ) {B : Scheme.{0}} (C : B.Etale ⥤ Cx (ZMod q)) (I : Cx (ZMod q)), (∀ p : ℤ, Good (C ⋙ HomologicalComplex.eval _ _ p)) → (∀ n, Injective (I.X n)) → ∀ n : ℤ, ∃ h : Presheaf.IsSheaf (EtTop B) (TP C I n), Injective (⟨TP C I n, h⟩ : SShv B q) := by
  intro q B C I hC hI n
  have hS := fun p : ℤ => hC p (I.X (p + n)) (hI _)
  let S : ℤ → SShv B q := fun p => ⟨HP (C ⋙ HomologicalComplex.eval _ _ p) (I.X (p + n)), (hS p).choose⟩
  haveI : ∀ p, Injective (S p) := fun p => (hS p).choose_spec
  let G := sheafToPresheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))
  let e : G.obj (∏ᶜ S) ≅ TP C I n :=
    PreservesProduct.iso G S ≪≫ (limit.isLimit _).conePointUniqueUpToIso (fanLim C I n)
  have h : Presheaf.IsSheaf (EtTop B) (TP C I n) := (Presheaf.isSheaf_of_iso_iff e).1 (∏ᶜ S).cond
  refine ⟨h, ?_⟩
  exact Injective.of_iso ((fullyFaithfulSheafToPresheaf _ _).preimageIso (Y := ⟨TP C I n, h⟩) e) inferInstance

end
