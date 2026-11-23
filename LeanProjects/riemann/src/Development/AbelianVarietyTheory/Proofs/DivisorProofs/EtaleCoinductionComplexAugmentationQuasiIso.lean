import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocallyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSectionsStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

variable {R : Type} [CommRing R]

theorem coindQ_map_res {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map f (Sec.res g x) = Sec.res g (Sec.map f x) := by
  have := congrArg (fun h => h.hom x) (f.hom.naturality g.op)
  simpa using this

theorem coindQ_res_res (F : Shv R) {W V U : Scheme.{0}} (g : W ⟶ V) (x : V ⟶ U) (s : Sec F U) :
    Sec.res g (Sec.res x s) = Sec.res (g ≫ x) s := by
  simp [Sec.res]

def coindQ_gen (J : Shv R) (U : Scheme.{0}) : ((free R).obj (yoneda.obj U) ⟶ J) →ₗ[ULift.{1} R] Sec J U where
  toFun ψ := Sec.map ψ (freeGen R (yoneda.obj U) U (𝟙 U))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

theorem coindQ_gen_bijective (J : Shv R) (U : Scheme.{0}) : Function.Bijective (coindQ_gen J U) := by
  obtain ⟨hex, huniq, hres, -⟩ := GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj U) J
  have key : ∀ (V : Scheme.{0}) (x : V ⟶ U),
      freeGen R (yoneda.obj U) V x = Sec.res x (freeGen R (yoneda.obj U) U (𝟙 U)) := by
    intro V x
    rw [hres V U x (𝟙 U)]
    simp
  constructor
  · intro ψ ψ' h
    apply huniq
    intro V x
    rw [key V x, coindQ_map_res, coindQ_map_res]
    exact congrArg (Sec.res x) h
  · intro s
    obtain ⟨ψ, hψ⟩ := hex (fun V x => Sec.res x s) (fun W V g x => by
      rw [coindQ_res_res]; rfl)
    refine ⟨ψ, ?_⟩
    show Sec.map ψ (freeGen R (yoneda.obj U) U (𝟙 U)) = s
    rw [hψ U (𝟙 U)]
    simp [Sec.res]

theorem coindQ_injSec (J : Shv R) (hJ : ∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J))
    (U : Scheme.{0}) : Injective (J.obj.obj (op U)) := by
  have := hJ (yoneda.obj U)
  have hI : Injective (ModuleCat.of (ULift.{1} R) ((free R).obj (yoneda.obj U) ⟶ J)) :=
    Module.injective_object_of_injective_module _ _
  exact Injective.of_iso (LinearEquiv.ofBijective (coindQ_gen J U) (coindQ_gen_bijective J U)).toModuleIso hI

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

theorem coindQ_exactAt_succ {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R)
    (hJ : ∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) (n : ℕ) :
    (coindCx φ J).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  rw [GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
  intro U b hb
  have := coindQ_injSec J hJ U
  let b' : (scalarsRes φ).complex.X (n + 1) ⟶ J.obj.obj (op U) := b
  have hb' : (scalarsRes φ).complex.d (n + 2) (n + 1) ≫ b' = 0 := by
    have h2 : (coindCx φ J).d (n + 1) (n + 2) = (homSh J).map ((scalarsRes φ).complex.d (n + 2) (n + 1)).op :=
      coindCx_d φ J (n + 1)
    have hb2 : Sec.map ((coindCx φ J).d (n + 1) (n + 2)) b = 0 := hb
    rw [h2] at hb2
    exact hb2
  let a' := ((scalarsRes φ).exact_succ n).descToInjective b' hb'
  have ha' : (scalarsRes φ).complex.d (n + 1) n ≫ a' = b' :=
    ((scalarsRes φ).exact_succ n).comp_descToInjective b' hb'
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ?_⟩
  have h1 : (coindCx φ J).d n (n + 1) = (homSh J).map ((scalarsRes φ).complex.d (n + 1) n).op :=
    coindCx_d φ J n
  have key : Sec.map ((coindCx φ J).d n (n + 1)) (a' : Sec ((coindCx φ J).X n) U) = b := by
    rw [h1]; exact ha'
  exact ⟨Sec.res g (a' : Sec ((coindCx φ J).X n) U),
    (coindQ_map_res ((coindCx φ J).d n (n + 1)) g _).trans (congrArg (Sec.res g) key)⟩

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

abbrev coindQ_p {S : Type} [CommRing S] (φ : R →+* S) :
    (scalarsRes φ).complex.X 0 ⟶ scalarsMod φ :=
  (scalarsRes φ).π.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (scalarsMod φ)).hom

instance {S : Type} [CommRing S] (φ : R →+* S) : Epi (coindQ_p φ) := by
  exact epi_comp _ _

theorem coindQ_d_p {S : Type} [CommRing S] (φ : R →+* S) :
    (scalarsRes φ).complex.d 1 0 ≫ coindQ_p φ = 0 := by
  show _ ≫ (_ ≫ _) = 0
  rw [ProjectiveResolution.complex_d_comp_π_f_zero_assoc, zero_comp]

def coindQ_sc {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R) : ShortComplex (Shv R) :=
  ShortComplex.mk (coindToHom φ J ≫ (homSh J).map (coindQ_p φ).op)
    ((homSh J).map ((scalarsRes φ).complex.d 1 0).op) (by
      rw [Category.assoc, ← Functor.map_comp, ← op_comp, coindQ_d_p, op_zero, Functor.map_zero, comp_zero])

theorem coindQ_sc_f_sec {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R) (U : Scheme.{0})
    (a : Sec ((restr φ).obj ((coind φ).obj J)) U) :
    Sec.map (coindQ_sc φ J).f a =
      (coindQ_p φ ≫ homOfLin (ModuleCat.CoextendScalars.equiv (liftHom φ) _ a) : _ ⟶ J.obj.obj (op U)) := rfl

theorem coindQ_sc_inj {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R) (U : Scheme.{0}) :
    Function.Injective (Sec.map (coindQ_sc φ J).f (U := U)) := by
  intro a a' h
  have h' := (coindQ_sc_f_sec φ J U a).symm.trans (h.trans (coindQ_sc_f_sec φ J U a'))
  have h3 := (cancel_epi (coindQ_p φ)).1 h'
  apply ModuleCat.CoextendScalars.ext
  exact congrArg ModuleCat.Hom.hom h3

theorem coindQ_sc_mono {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R) : Mono (coindQ_sc φ J).f := by
  suffices h : Mono (coindQ_sc φ J).f.hom from Sheaf.Hom.mono_of_presheaf_mono _ _ _
  have hU : ∀ U, Mono ((coindQ_sc φ J).f.hom.app U) := by
    intro U
    rw [ModuleCat.mono_iff_injective]
    exact coindQ_sc_inj φ J U.unop
  exact NatTrans.mono_of_mono_app _

theorem coindQ_sc_exact {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R) : (coindQ_sc φ J).Exact := by
  rw [GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
  intro U b hb
  let b' : (scalarsRes φ).complex.X 0 ⟶ J.obj.obj (op U) := b
  have hb' : (scalarsRes φ).complex.d 1 0 ≫ b' = 0 := hb
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' (scalarsRes φ).isColimitCokernelCofork b' hb'
  let c : scalarsMod φ ⟶ J.obj.obj (op U) :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (scalarsMod φ)).inv ≫ l
  have hc : coindQ_p φ ≫ c = b' := by
    simp only [c, coindQ_p, Category.assoc, Iso.hom_inv_id_assoc]
    exact hl
  let a : Sec ((restr φ).obj ((coind φ).obj J)) U := (ModuleCat.CoextendScalars.equiv (liftHom φ) _).symm c.hom
  have key : Sec.map (coindQ_sc φ J).f a = b := by
    rw [coindQ_sc_f_sec]
    exact hc
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨Sec.res g a, ?_⟩⟩
  exact (coindQ_map_res _ g _).trans (congrArg (Sec.res g) key)

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

theorem coindAug_quasiIso : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (J : Shv R),
    (∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) → QuasiIso (coindAug φ J) := by
  intro R S _ _ φ J hJ
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨coindQ_sc_exact φ J, coindQ_sc_mono φ J⟩
      refine ShortComplex.isoMk (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 _) (Iso.refl _) (Iso.refl _) ?_ ?_
      · simp only [Iso.refl_hom, Category.comp_id]
        exact (coindAug_f_zero φ J).symm
      · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        exact (coindCx_d φ J 0).symm
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)]
    exact coindQ_exactAt_succ φ J hJ n

end GlobalTheory.EtC
