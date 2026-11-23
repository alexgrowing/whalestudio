import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
import Development.EtaleCohomology.KummerTheory.InjSlice
import Development.EtaleCohomology.WeilConjectures.AcycPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSectionsStatement

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

private lemma res_val {R : Type} [CommRing R] {X : Scheme.{0}} {J : Shv R} (φ : (free R).obj (yoneda.obj X) ⟶ J)
    {V : Scheme.{0}} (x : V ⟶ X) :
    Sec.map φ (freeGen R (yoneda.obj X) V x) = Sec.res x (Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))) := by
  have h3 := (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X) J).2.2.1 V X x (𝟙 X)
  have nat : Sec.res x (Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))) =
      Sec.map φ (Sec.res x (freeGen R (yoneda.obj X) X (𝟙 X))) := by
    simp only [Sec.res, Sec.map]
    exact (congrArg (fun f => ModuleCat.Hom.hom f (freeGen R (yoneda.obj X) X (𝟙 X)))
      (φ.hom.naturality x.op)).symm
  rw [nat, h3]
  simp

private noncomputable def evE (R : Type) [CommRing R] (X : Scheme.{0}) (J : Shv R) :
    ((free R).obj (yoneda.obj X) ⟶ J) ≃ₗ[ULift.{1} R] Sec J X :=
  LinearEquiv.ofBijective
    { toFun := fun φ => Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ⟨by
      intro φ ψ h
      refine (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X) J).2.1 φ ψ fun U x => ?_
      rw [res_val φ x, res_val ψ x]
      exact congrArg (Sec.res x) h,
     by
      intro s
      obtain ⟨φ, hφ⟩ := (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X) J).1 (fun U x => Sec.res x s) (by
        intro V U g x
        simp [Sec.res])
      refine ⟨φ, ?_⟩
      refine (hφ X (𝟙 X)).trans ?_
      simp [Sec.res]⟩

private lemma pullbackSymmetry_lift_map_comm {A A' Y B : Scheme.{0}} (p : Y ⟶ B) (u : A ⟶ B) (u' : A' ⟶ B) (l : A' ⟶ A) (hl : l ≫ u = u') :
    pullback.lift (pullback.fst u' p ≫ l) (pullback.snd u' p)
        (by rw [Category.assoc, hl, pullback.condition]) ≫ (pullbackSymmetry p u).inv =
      (pullbackSymmetry p u').inv ≫ pullback.map p u' p u (𝟙 Y) l (𝟙 B) (by simp) (by simp [hl]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSymmetry_inv_comp_fst, pullback.lift_snd, Category.assoc, pullback.lift_fst]
    simp
  · rw [Category.assoc, pullbackSymmetry_inv_comp_snd, pullback.lift_fst, Category.assoc, pullback.lift_snd]
    simp

private lemma sym_nat {B Y : Scheme.{0}} (p : Y ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) :
    (LateralTheory.KummerTheory.tot p).map ((LateralTheory.EWeil.AcycPf.incl B).map a) ≫ (pullbackSymmetry p U.hom).inv =
      (pullbackSymmetry p U'.hom).inv ≫ resY p a := by
  have w : a.left ≫ U.hom = U'.hom := Over.w ((LateralTheory.EWeil.AcycPf.incl B).map a)
  exact pullbackSymmetry_lift_map_comm p U.hom U'.hom a.left w

private lemma res_res {R : Type} [CommRing R] {F : Shv R} {U V W : Scheme.{0}} (f : V ⟶ U) (g : W ⟶ V) (s : Sec F U) :
    Sec.res g (Sec.res f s) = Sec.res (g ≫ f) s := by
  simp [Sec.res]

private lemma ev_pre {R : Type} [CommRing R] {X X' : Scheme.{0}} {J : Shv R} (f : X' ⟶ X)
    (φ : (free R).obj (yoneda.obj X) ⟶ J) :
    Sec.map ((free R).map (yoneda.map f) ≫ φ) (freeGen R (yoneda.obj X') X' (𝟙 X')) =
      Sec.res f (Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))) := by
  have h4 := (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X') J).2.2.2 (yoneda.obj X) (yoneda.map f) X' (𝟙 X')
  have hc : Sec.map ((free R).map (yoneda.map f) ≫ φ) (freeGen R (yoneda.obj X') X' (𝟙 X')) =
      Sec.map φ (Sec.map ((free R).map (yoneda.map f)) (freeGen R (yoneda.obj X') X' (𝟙 X'))) := rfl
  rw [hc, h4, ← res_val φ f]
  congr 2

private noncomputable def isoHP (q : ℕ) {B Y : Scheme.{0}} (p : Y ⟶ B) (J : Shv (ZMod q)) :
    HP (gY p ⋙ yoneda ⋙ free (ZMod q)) J ≅ (LateralTheory.EWeil.AcycPf.incl B).op ⋙ (LateralTheory.KummerTheory.tot p).op ⋙ J.obj :=
  NatIso.ofComponents (fun U => LinearEquiv.toModuleIso
      ((evE (ZMod q) (YU p U.unop) J).trans
        (J.obj.mapIso (pullbackSymmetry p U.unop.hom).symm.op).toLinearEquiv)) (by
    rintro ⟨U⟩ ⟨U'⟩ ⟨a⟩
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => ?_)
    have h := ev_pre (R := ZMod q) (J := J) (resY p a) φ
    change Sec.res (pullbackSymmetry p U'.hom).inv (Sec.map ((free (ZMod q)).map (yoneda.map (resY p a)) ≫ φ)
        (freeGen (ZMod q) (yoneda.obj (YU p U')) (YU p U') (𝟙 _))) =
      Sec.res ((LateralTheory.KummerTheory.tot p).map ((LateralTheory.EWeil.AcycPf.incl B).map a))
        (Sec.res (pullbackSymmetry p U.hom).inv (Sec.map φ (freeGen (ZMod q) (yoneda.obj (YU p U)) (YU p U) (𝟙 _))))
    rw [h]
    refine (res_res _ _ _).trans (Eq.trans ?_ (res_res _ _ _).symm)
    exact congrArg (fun t => Sec.res (F := J) t _) (sym_nat p a).symm)

theorem UpperTheory.homAcyclic_free_pullback_yoneda_of_injective_restriction :
    LateralTheory.KummerTheory.InjSlice → LateralTheory.EWeil.AcycPf.RestrInj → ∀ (q : ℕ) {B Y : Scheme.{0}} (p : Y ⟶ B), Good (gY p ⋙ yoneda ⋙ free (ZMod q)) := by
  intro hI hR q B Y p J hJ
  obtain ⟨h1, i1⟩ := (hI (ZMod q) J p).1
  obtain ⟨h2, i2⟩ := hR (ZMod q) B ⟨(LateralTheory.KummerTheory.tot p).op ⋙ J.obj, h1⟩
  have e := isoHP q p J
  refine ⟨(Presheaf.isSheaf_of_iso_iff e).2 h2, ?_⟩
  exact Injective.of_iso ((sheafToPresheaf _ _).preimageIso (X := ⟨_, h2⟩) e.symm) i2
