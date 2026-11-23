import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendChainMapAlongQuasiIsoKInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexSemilinearMapCompBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSheafIsLocallyFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodSemilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsZmodOfFlatResolutionStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ScalarExt

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) (φ.hom.naturality g.op)).symm

theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hP : ∀ V g, P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hP0⟩ := h
  exact ⟨S, hS, fun V g hg => hP V g (hP0 V g hg)⟩

theorem agree_on_twist {Q q : ℕ} [NeZero Q] (k : ℤ) {T : Cx (ZMod Q)} {J : Cx (ZMod q)} (ε : sgl (tw Q k) ⟶ T)
    (σ σ' : SemiMap T J)
    (he : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))) =
      σ'.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))))
    (U : Scheme.{0}) (y : Sec (tw Q k) U) :
    σ.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) y)) = σ'.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) y)) := by
  refine ((GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (J.X 0) U).1 _ _ (loc_mono ((GlobalTheory.T.tateTwist_sections_locally_generated Q k).1 U y) fun V g hg => ?_))
  rw [σ.nat, σ'.nat, sec_map_res, sec_map_res]
  rcases hg with h0 | ⟨ζ, c, hc⟩
  · rw [h0]; simp
  · have hm : ∀ {A B : Shv (ZMod Q)} (φ : A ⟶ B) (x : Sec A V), Sec.map φ (c • x) = c • Sec.map φ x :=
      fun φ x => map_nsmul (φ.hom.app (op V)).hom c x
    rw [hc, hm, hm, map_nsmul, map_nsmul, he]

end GlobalTheory.EtC.ScalarExt

namespace GlobalTheory.EtC.ScalarExt

theorem semiMap_op_eq_of_flat_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (k : ℤ) {T : Cx (ZMod Q)} (e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes Q k T e → (∀ t, FlatS (T.X t)) → ∀ σ σ' : SemiMap T (res _ (tw q k)), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (e U ζ) = σ'.app U 0 (e U ζ)) → ∀ (E : Spc) (n : ℤ) (x : CohomologyClass ((chains (ZMod Q)).obj E) T n), σ.op.app E n x = σ'.op.app E n x := by
  intro Q q _ h k T e hT hflat σ σ' hσ E n x
  obtain ⟨hge, ε, hqi, hεe⟩ := hT
  haveI := hge
  have hl := zmod_semilinear h σ
  have hl' := zmod_semilinear h σ'
  let εb : sgl ((ext (ZMod.castHom h (ZMod q))).obj (tw Q k)) ⟶ (extCx (ZMod.castHom h (ZMod q))).obj T :=
    ((HomologicalComplex.singleMapHomologicalComplex (ext (ZMod.castHom h (ZMod q))) (ComplexShape.up ℤ) 0).app
      (tw Q k)).inv ≫ (extCx (ZMod.castHom h (ZMod q))).map ε
  have hq2 : QuasiIso ((extCx (ZMod.castHom h (ZMod q))).map ε) :=
    GlobalTheory.T.quasiIso_extendScalars_zmod_of_flat_resolution Q q h (tw Q k) T (GlobalTheory.T.tateTwistSheaf_isLocallyFlat Q k) hflat ε hqi
  haveI : IsIso ((HomologicalComplex.singleMapHomologicalComplex (ext (ZMod.castHom h (ZMod q))) (ComplexShape.up ℤ) 0).app
      (tw Q k)).inv := Iso.isIso_inv _
  have hq1 : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex (ext (ZMod.castHom h (ZMod q))) (ComplexShape.up ℤ) 0).app
      (tw Q k)).inv := quasiIso_of_isIso _
  haveI : QuasiIso εb := quasiIso_comp (hφ := hq1) (hφ' := hq2) _ _
  haveI : (res (ZMod q) (tw q k)).IsKInjective :=
    inferInstanceAs ((injectiveResolution (tw q k)).cochainComplex.IsKInjective)
  haveI : (res (ZMod q) (tw q k)).IsStrictlyGE 0 :=
    inferInstanceAs ((injectiveResolution (tw q k)).cochainComplex.IsStrictlyGE 0)
  haveI : IsIso (sglι (tw Q k)) := by unfold sglι; exact Iso.isIso_inv _
  have he : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))) =
      σ'.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))) := fun U ζ => by
    rw [hεe]; exact hσ U ζ
  have hcomp : εb ≫ semiBar σ hl = εb ≫ semiBar σ' hl' := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i = 0
    · subst hi
      have key : (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ (semiBar σ hl).f 0 =
          (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ (semiBar σ' hl').f 0 := by
        change (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ ((adj _).homEquiv _ _).symm (semiHom σ hl 0) =
          (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ ((adj _).homEquiv _ _).symm (semiHom σ' hl' 0)
        rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_left_symm]
        congr 1
        rw [← cancel_epi (sglι (tw Q k))]
        ext U y
        exact agree_on_twist k ε σ σ' he U.unop y
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      dsimp only [εb]
      erw [HomologicalComplex.comp_f, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) key
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _
  obtain ⟨H⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) _ _ _ εb).2 _ _ hcomp
  have h1 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective (ZMod Q) (ZMod q) (unitSemi T) σ (semiBar σ hl) (semi_factor σ hl)).1 E n x
  have h2 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective (ZMod Q) (ZMod q) (unitSemi T) σ' (semiBar σ' hl') (semi_factor σ' hl')).1 E n x
  rw [h1, h2, ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial (ZMod q)).2.2.2.2 _ _ ⟨H⟩ _ n).2]

end GlobalTheory.EtC.ScalarExt

end
