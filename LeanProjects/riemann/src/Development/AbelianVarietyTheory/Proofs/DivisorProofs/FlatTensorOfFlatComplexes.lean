import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocForallFinset

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace GlobalTheory.EtC.FlatTens

section Loc
variable {U : Scheme.{0}}

theorem loc_mono {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g → Q V g) (hP : Loc U P) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hP V g hg)⟩

theorem loc_of_forall {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_and {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hP⟩ := hP
  obtain ⟨T, hT, hQ⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

theorem loc_trans {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P := by
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hTP using hP
  refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => hT V g hg), ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hTP V g hg W k hk

theorem loc_finset {ι : Type*} (s : Finset ι) {P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ i ∈ s, Loc U (P i)) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  first
  | exact @_root_.GlobalTheory.LocalizedFinsetForAll.loc_forall_finset
  | exact _root_.GlobalTheory.LocalizedFinsetForAll.loc_forall_finset
  | (apply _root_.GlobalTheory.LocalizedFinsetForAll.loc_forall_finset <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalizedFinsetForAll.loc_forall_finset <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalizedFinsetForAll.loc_forall_finset <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalizedFinsetForAll.loc_forall_finset ..)

end Loc

variable {R : Type} [CommRing R]

def locZero (M : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}) : Submodule (ULift.{1} R) (M.obj (op U)) where
  carrier := {x | Loc U fun V g => (M.map g.op).hom x = 0}
  zero_mem' := loc_of_forall fun V g => map_zero _
  add_mem' {x y} hx hy := loc_mono (fun V g h => by simp [h.1, h.2]) (loc_and hx hy)
  smul_mem' r x hx := loc_mono (fun V g h => by simp [h]) hx

def locIm {A M : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : A ⟶ M) (U : Scheme.{0}) :
    Submodule (ULift.{1} R) (M.obj (op U)) where
  carrier := {x | Loc U fun V g => (M.map g.op).hom x ∈ LinearMap.range (f.app (op V)).hom}
  zero_mem' := loc_of_forall fun V g => by simp
  add_mem' {x y} hx hy := loc_mono (fun V g h => by simpa using add_mem h.1 h.2) (loc_and hx hy)
  smul_mem' r x hx := loc_mono (fun V g h => by simpa using Submodule.smul_mem _ r h) hx

def tensP {ι : Type} (A B : ι → Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :
    Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (⨁ i, (A i).obj U ⊗[ULift.{1} R] (B i).obj U)
  map g := ModuleCat.ofHom (DirectSum.lmap fun i => TensorProduct.map ((A i).map g).hom ((B i).map g).hom)
  map_id U := by
    classical
    ext1
    refine DirectSum.linearMap_ext _ fun i => TensorProduct.ext' fun a b => ?_
    simp [DirectSum.lof_eq_of, DirectSum.lmap_of]
  map_comp f g := by
    classical
    ext1
    refine DirectSum.linearMap_ext _ fun i => TensorProduct.ext' fun a b => ?_
    simp [DirectSum.lof_eq_of, DirectSum.lmap_of]

theorem tensP_map_of {ι : Type} [DecidableEq ι] (A B : ι → Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    {U V : Scheme.{0}ᵒᵖ} (g : U ⟶ V) (i : ι) (a : (A i).obj U) (b : (B i).obj U) :
    ((tensP A B).map g).hom (DirectSum.of (fun i => (A i).obj U ⊗[ULift.{1} R] (B i).obj U) i (a ⊗ₜ b)) =
      DirectSum.of (fun i => (A i).obj V ⊗[ULift.{1} R] (B i).obj V) i (((A i).map g).hom a ⊗ₜ ((B i).map g).hom b) := by
  exact (DirectSum.lmap_of (fun i => TensorProduct.map ((A i).map g).hom ((B i).map g).hom) i (a ⊗ₜ b)).trans
    (by rw [TensorProduct.map_tmul])

def tensMap {ι : Type} {A B M N : ι → Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : ∀ i, A i ⟶ M i)
    (g : ∀ i, B i ⟶ N i) : tensP A B ⟶ tensP M N where
  app U := ModuleCat.ofHom (DirectSum.lmap fun i => TensorProduct.map ((f i).app U).hom ((g i).app U).hom)
  naturality U V k := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => DFinsupp.ext fun i => ?_)
    have hf : ((f i).app V).hom ∘ₗ ((A i).map k).hom = ((M i).map k).hom ∘ₗ ((f i).app U).hom :=
      congrArg ModuleCat.Hom.hom ((f i).naturality k)
    have hg : ((g i).app V).hom ∘ₗ ((B i).map k).hom = ((N i).map k).hom ∘ₗ ((g i).app U).hom :=
      congrArg ModuleCat.Hom.hom ((g i).naturality k)
    let y : ⨁ i, (A i).obj U ⊗[ULift.{1} R] (B i).obj U := x
    change TensorProduct.map ((f i).app V).hom ((g i).app V).hom (TensorProduct.map ((A i).map k).hom ((B i).map k).hom (y i)) =
      TensorProduct.map ((M i).map k).hom ((N i).map k).hom (TensorProduct.map ((f i).app U).hom ((g i).app U).hom (y i))
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, hf, hg, TensorProduct.map_comp, LinearMap.comp_apply]

theorem tensMap_of {ι : Type} [DecidableEq ι] {A B M N : ι → Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)}
    (f : ∀ i, A i ⟶ M i) (g : ∀ i, B i ⟶ N i) (U : Scheme.{0}ᵒᵖ) (i : ι) (a : (A i).obj U) (b : (B i).obj U) :
    ((tensMap f g).app U).hom (DirectSum.of (fun i => (A i).obj U ⊗[ULift.{1} R] (B i).obj U) i (a ⊗ₜ b)) =
      DirectSum.of (fun i => (M i).obj U ⊗[ULift.{1} R] (N i).obj U) i (((f i).app U).hom a ⊗ₜ ((g i).app U).hom b) := by
  exact (DirectSum.lmap_of (fun i => TensorProduct.map ((f i).app U).hom ((g i).app U).hom) i (a ⊗ₜ b)).trans
    (by rw [TensorProduct.map_tmul])

theorem lift_of {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) [DecidableEq {p : ℤ × ℤ // p.1 + p.2 = w}]
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (DirectSum.of (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p
      (a ⊗ₜ b)) = μ.mul U p.1.1 p.1.2 w p.2 a b := by
  unfold Pair.lift
  convert DirectSum.toModule_lof (ULift.{1} R) (φ := fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
    TensorProduct.lift (μ.mul U p.1.1 p.1.2 w p.2)) p (a ⊗ₜ b) using 2
  · congr; exact Subsingleton.elim _ _
  · rfl
  · simp

def liftN {I J K : Cx R} (μ : Pair I J K) (w : ℤ) :
    tensP (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => (I.X p.1.1).obj) (fun p => (J.X p.1.2).obj) ⟶ (K.X w).obj where
  app U := ModuleCat.ofHom (μ.lift U.unop w)
  naturality U V k := by
    have h : μ.lift V.unop w ∘ₗ Tens.res k.unop w = ((K.X w).obj.map k).hom ∘ₗ μ.lift U.unop w := by
      classical
      refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
      simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, Tens.res, DirectSum.lmap_of, TensorProduct.map_tmul]
      rw [lift_of, lift_of]
      exact (μ.nat k.unop p.1.1 p.1.2 w p.2 a b).symm
    exact ModuleCat.hom_ext (LinearMap.ext fun x => LinearMap.congr_fun h x)

theorem lift_res {I J K : Cx R} (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    μ.lift V w (Tens.res g w x) = Sec.res g (μ.lift U w x) :=
  congr(($((liftN μ w).naturality g.op)).hom x)

end GlobalTheory.EtC.FlatTens

namespace GlobalTheory.EtC.FlatTens
open TensorProduct LinearMap

theorem exists_fg_tens {S A B : Type*} [CommRing S] [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    (y : A ⊗[S] B) : ∃ (A0 : Submodule S A) (B0 : Submodule S B) (y0 : A0 ⊗[S] B0), A0.FG ∧ B0.FG ∧
      TensorProduct.map A0.subtype B0.subtype y0 = y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨⊥, ⊥, 0, Submodule.fg_bot, Submodule.fg_bot, map_zero _⟩
  | tmul a b =>
    exact ⟨S ∙ a, S ∙ b, ⟨a, Submodule.mem_span_singleton_self a⟩ ⊗ₜ ⟨b, Submodule.mem_span_singleton_self b⟩,
      Submodule.fg_span_singleton a, Submodule.fg_span_singleton b, rfl⟩
  | add x y hx hy =>
    obtain ⟨A1, B1, x1, hA1, hB1, rfl⟩ := hx
    obtain ⟨A2, B2, y2, hA2, hB2, rfl⟩ := hy
    refine ⟨A1 ⊔ A2, B1 ⊔ B2, TensorProduct.map (Submodule.inclusion le_sup_left) (Submodule.inclusion le_sup_left) x1 +
      TensorProduct.map (Submodule.inclusion le_sup_right) (Submodule.inclusion le_sup_right) y2, hA1.sup hA2, hB1.sup hB2, ?_⟩
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply (TensorProduct.map _ _), ← TensorProduct.map_comp,
      ← TensorProduct.map_comp]
    rfl

theorem comm_lTensor {S M N N' : Type*} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [AddCommGroup N'] [Module S N'] (h : N →ₗ[S] N') (z : M ⊗[S] N) :
    TensorProduct.comm S M N' (lTensor M h z) = rTensor M h (TensorProduct.comm S M N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem key_alg {S A B I J : Type*} [CommRing S] [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    [AddCommGroup I] [Module S I] [AddCommGroup J] [Module S J] (f : A →ₗ[S] I) (g : B →ₗ[S] J) (y : A ⊗[S] B)
    (hy : TensorProduct.map f g y = 0) :
    ∃ (A0 : Submodule S A) (B0 : Submodule S B) (I1 : Submodule S I) (J1 : Submodule S J) (hA : A0 ≤ I1.comap f)
      (hB : B0 ≤ J1.comap g) (y0 : A0 ⊗[S] B0), I1.FG ∧ J1.FG ∧ TensorProduct.map A0.subtype B0.subtype y0 = y ∧
      TensorProduct.map (f.restrict hA) (g.restrict hB) y0 = 0 := by
  obtain ⟨A0, B0, y0, hA0, hB0, rfl⟩ := exists_fg_tens y
  set I0 := A0.map f
  set J0 := B0.map g
  set z0 : I0 ⊗[S] J0 := TensorProduct.map (f.submoduleMap A0) (g.submoduleMap B0) y0 with hz0
  have hz : TensorProduct.map I0.subtype J0.subtype z0 = 0 := by
    rw [hz0, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    exact (congrArg (fun h => h y0) (TensorProduct.map_comp f g A0.subtype B0.subtype)).trans hy
  have h1 : rTensor J I0.subtype (lTensor I0 J0.subtype z0) = rTensor J I0.subtype 0 := by
    rw [map_zero, ← LinearMap.comp_apply, rTensor_comp_lTensor]; exact hz
  obtain ⟨I1, hI1, hle, e1⟩ := (hA0.map f).exists_rTensor_fg_inclusion_eq h1
  rw [map_zero] at e1
  set z1 : I1 ⊗[S] J0 := rTensor J0 (Submodule.inclusion hle) z0 with hz1
  have hl : lTensor I1 J0.subtype z1 = 0 := by
    rw [hz1, ← LinearMap.comp_apply, lTensor_comp_rTensor, ← rTensor_comp_lTensor, LinearMap.comp_apply]
    exact e1
  have h2 : rTensor I1 J0.subtype (TensorProduct.comm S I1 J0 z1) = rTensor I1 J0.subtype 0 := by
    rw [map_zero, ← comm_lTensor, hl, map_zero]
  obtain ⟨J1, hJ1, hle', e2⟩ := (hB0.map g).exists_rTensor_fg_inclusion_eq h2
  rw [map_zero] at e2
  have hA : A0 ≤ I1.comap f := fun a ha => hle (Submodule.mem_map_of_mem ha)
  have hB : B0 ≤ J1.comap g := fun b hb => hle' (Submodule.mem_map_of_mem hb)
  refine ⟨A0, B0, I1, J1, hA, hB, y0, hI1, hJ1, rfl, ?_⟩
  have ef : f.restrict hA = Submodule.inclusion hle ∘ₗ f.submoduleMap A0 := LinearMap.ext fun _ => rfl
  have eg : g.restrict hB = Submodule.inclusion hle' ∘ₗ g.submoduleMap B0 := LinearMap.ext fun _ => rfl
  rw [ef, eg, TensorProduct.map_comp, LinearMap.comp_apply, ← hz0, ← lTensor_comp_rTensor, LinearMap.comp_apply, ← hz1]
  apply (TensorProduct.comm S I1 J1).injective
  rw [comm_lTensor, e2, map_zero]

end GlobalTheory.EtC.FlatTens

namespace GlobalTheory.EtC.FlatTens
open TensorProduct

variable {R : Type} [CommRing R]

def locZero2 (A B : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (V : Scheme.{0}) :
    Submodule (ULift.{1} R) (A.obj (op V) ⊗[ULift.{1} R] B.obj (op V)) where
  carrier := {z | Loc V fun W k => TensorProduct.map (A.map k.op).hom (B.map k.op).hom z = 0}
  zero_mem' := loc_of_forall fun W k => map_zero _
  add_mem' {x y} hx hy := loc_mono (fun W k h => by simp [h.1, h.2]) (loc_and hx hy)
  smul_mem' r x hx := loc_mono (fun W k h => by simp [h]) hx

theorem nat_apply {A M : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : A ⟶ M) {U V : Scheme.{0}ᵒᵖ} (k : U ⟶ V)
    (a : A.obj U) : (f.app V).hom ((A.map k).hom a) = (M.map k).hom ((f.app U).hom a) := by
  have := congr(($(f.naturality k)).hom a)
  simpa using this

theorem tensor_locally_zero_of_exact {A B M N : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : A ⟶ M) (g : B ⟶ N)
    (hfs : ∀ (U : Scheme.{0}) (y : M.obj (op U)), Loc U fun V k => ∃ x, (f.app (op V)).hom x = (M.map k.op).hom y)
    (hgs : ∀ (U : Scheme.{0}) (y : N.obj (op U)), Loc U fun V k => ∃ x, (g.app (op V)).hom x = (N.map k.op).hom y)
    (hfi : ∀ (U : Scheme.{0}) (x : A.obj (op U)), (f.app (op U)).hom x = 0 → x ∈ locZero A U)
    (hgi : ∀ (U : Scheme.{0}) (x : B.obj (op U)), (g.app (op U)).hom x = 0 → x ∈ locZero B U)
    (U : Scheme.{0}) (y : A.obj (op U) ⊗[ULift.{1} R] B.obj (op U))
    (hy : TensorProduct.map (f.app (op U)).hom (g.app (op U)).hom y = 0) : y ∈ locZero2 A B U := by
  obtain ⟨A0, B0, I1, J1, hA, hB, y0, ⟨sI, hsI⟩, ⟨sJ, hsJ⟩, rfl, hy0⟩ := key_alg _ _ y hy
  have cI := loc_finset sI (fun m _ => hfs U m)
  have cJ := loc_finset sJ (fun m _ => hgs U m)
  refine loc_trans (loc_mono (fun V k h => ?_) (loc_and cI cJ))
  obtain ⟨hI, hJ⟩ := h
  have lI : I1 ≤ (LinearMap.range (f.app (op V)).hom).comap (M.map k.op).hom := by
    rw [← hsI, Submodule.span_le]
    intro m hm
    obtain ⟨x, hx⟩ := hI m hm
    exact ⟨x, hx⟩
  have lJ : J1 ≤ (LinearMap.range (g.app (op V)).hom).comap (N.map k.op).hom := by
    rw [← hsJ, Submodule.span_le]
    intro m hm
    obtain ⟨x, hx⟩ := hJ m hm
    exact ⟨x, hx⟩
  set yV := TensorProduct.map (A.map k.op).hom (B.map k.op).hom (TensorProduct.map A0.subtype B0.subtype y0) with hyV
  have e1 : (f.app (op V)).hom.rangeRestrict ∘ₗ (A.map k.op).hom ∘ₗ A0.subtype =
      ((M.map k.op).hom.restrict (fun x hx => lI hx)) ∘ₗ (f.app (op U)).hom.restrict hA :=
    LinearMap.ext fun a => Subtype.ext (nat_apply f k.op a.1)
  have e2 : (g.app (op V)).hom.rangeRestrict ∘ₗ (B.map k.op).hom ∘ₗ B0.subtype =
      ((N.map k.op).hom.restrict (fun x hx => lJ hx)) ∘ₗ (g.app (op U)).hom.restrict hB :=
    LinearMap.ext fun a => Subtype.ext (nat_apply g k.op a.1)
  have hker : yV ∈ LinearMap.ker (TensorProduct.map (f.app (op V)).hom.rangeRestrict (g.app (op V)).hom.rangeRestrict) := by
    have ec : TensorProduct.map (f.app (op V)).hom.rangeRestrict (g.app (op V)).hom.rangeRestrict ∘ₗ
        TensorProduct.map (A.map k.op).hom (B.map k.op).hom ∘ₗ TensorProduct.map A0.subtype B0.subtype =
        TensorProduct.map ((M.map k.op).hom.restrict (fun x hx => lI hx)) ((N.map k.op).hom.restrict (fun x hx => lJ hx)) ∘ₗ
        TensorProduct.map ((f.app (op U)).hom.restrict hA) ((g.app (op U)).hom.restrict hB) := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, e1, e2, TensorProduct.map_comp]
    rw [LinearMap.mem_ker, hyV]
    exact (LinearMap.congr_fun ec y0).trans (by rw [LinearMap.comp_apply, hy0, map_zero])
  rw [TensorProduct.map_ker (LinearMap.exact_subtype_ker_map _) (LinearMap.surjective_rangeRestrict _)
    (LinearMap.exact_subtype_ker_map _) (LinearMap.surjective_rangeRestrict _)] at hker
  have hle : LinearMap.range (LinearMap.lTensor (A.obj (op V)) (LinearMap.ker (g.app (op V)).hom.rangeRestrict).subtype) ⊔
      LinearMap.range (LinearMap.rTensor (B.obj (op V)) (LinearMap.ker (f.app (op V)).hom.rangeRestrict).subtype) ≤
      locZero2 A B V := by
    refine sup_le ?_ ?_
    · rintro _ ⟨u, rfl⟩
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [map_add]; exact add_mem ha hb
      | tmul a b =>
        have hb : (g.app (op V)).hom b.1 = 0 := by
          have := b.2
          rw [LinearMap.mem_ker] at this
          exact congrArg Subtype.val this
        refine loc_mono (fun W k' h => ?_) (hgi V b.1 hb)
        change TensorProduct.map _ _ (a ⊗ₜ b.1) = 0
        rw [TensorProduct.map_tmul, h, TensorProduct.tmul_zero]
    · rintro _ ⟨u, rfl⟩
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [map_add]; exact add_mem ha hb
      | tmul a b =>
        have ha : (f.app (op V)).hom a.1 = 0 := by
          have := a.2
          rw [LinearMap.mem_ker] at this
          exact congrArg Subtype.val this
        refine loc_mono (fun W k' h => ?_) (hfi V a.1 ha)
        change TensorProduct.map _ _ (a.1 ⊗ₜ b) = 0
        rw [TensorProduct.map_tmul, h, TensorProduct.zero_tmul]
  refine loc_mono (fun W k' h => ?_) (hle hker)
  rw [op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp, TensorProduct.map_comp,
    LinearMap.comp_apply]
  exact h

end GlobalTheory.EtC.FlatTens

namespace GlobalTheory.EtC.FlatTens
open TensorProduct

variable {R : Type} [CommRing R]

theorem tens_locIm {ι : Type} {A B M N : ι → Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : ∀ i, A i ⟶ M i)
    (g : ∀ i, B i ⟶ N i)
    (hfs : ∀ i (U : Scheme.{0}) (y : (M i).obj (op U)), Loc U fun V k => ∃ x, ((f i).app (op V)).hom x = ((M i).map k.op).hom y)
    (hgs : ∀ i (U : Scheme.{0}) (y : (N i).obj (op U)), Loc U fun V k => ∃ x, ((g i).app (op V)).hom x = ((N i).map k.op).hom y)
    (U : Scheme.{0}) (x : (tensP M N).obj (op U)) : x ∈ locIm (tensMap f g) U := by
  classical
  suffices h : ∀ x' : ⨁ i, (M i).obj (op U) ⊗[ULift.{1} R] (N i).obj (op U), x' ∈ locIm (tensMap f g) U from h x
  intro x'
  induction x' using DirectSum.induction_on with
  | zero => exact zero_mem _
  | add a b ha hb => exact add_mem ha hb
  | of i y =>
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul a b =>
      refine loc_mono (fun V k h => ?_) (loc_and (hfs i U a) (hgs i U b))
      obtain ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ := h
      refine ⟨DirectSum.of (fun i => (A i).obj (op V) ⊗[ULift.{1} R] (B i).obj (op V)) i (a' ⊗ₜ b'), ?_⟩
      erw [tensMap_of, tensP_map_of, ha', hb']

theorem tens_locZero {ι : Type} {A B M N : ι → Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : ∀ i, A i ⟶ M i)
    (g : ∀ i, B i ⟶ N i)
    (hfs : ∀ i (U : Scheme.{0}) (y : (M i).obj (op U)), Loc U fun V k => ∃ x, ((f i).app (op V)).hom x = ((M i).map k.op).hom y)
    (hgs : ∀ i (U : Scheme.{0}) (y : (N i).obj (op U)), Loc U fun V k => ∃ x, ((g i).app (op V)).hom x = ((N i).map k.op).hom y)
    (hfi : ∀ i (U : Scheme.{0}) (x : (A i).obj (op U)), ((f i).app (op U)).hom x = 0 → x ∈ locZero (A i) U)
    (hgi : ∀ i (U : Scheme.{0}) (x : (B i).obj (op U)), ((g i).app (op U)).hom x = 0 → x ∈ locZero (B i) U)
    (U : Scheme.{0}) (x : (tensP A B).obj (op U)) (hx : ((tensMap f g).app (op U)).hom x = 0) :
    x ∈ locZero (tensP A B) U := by
  classical
  let x' : ⨁ i, (A i).obj (op U) ⊗[ULift.{1} R] (B i).obj (op U) := x
  have hc : ∀ i, TensorProduct.map ((f i).app (op U)).hom ((g i).app (op U)).hom (x' i) = 0 := fun i =>
    congrArg (fun z : ⨁ i, (M i).obj (op U) ⊗[ULift.{1} R] (N i).obj (op U) => z i) hx
  have hof : ∀ i (y : (A i).obj (op U) ⊗[ULift.{1} R] (B i).obj (op U)), y ∈ locZero2 (A i) (B i) U →
      DirectSum.of (fun i => (A i).obj (op U) ⊗[ULift.{1} R] (B i).obj (op U)) i y ∈ locZero (tensP A B) U := by
    intro i y hy
    refine loc_mono (fun V k h => ?_) hy
    change DirectSum.lmap _ (DirectSum.of (fun i => (A i).obj (op U) ⊗[ULift.{1} R] (B i).obj (op U)) i y) = 0
    rw [DirectSum.lmap_of]
    exact (congrArg _ h).trans (map_zero _)
  have hx' : x = ∑ i ∈ x'.support, DirectSum.of _ i (x' i) := (DirectSum.sum_support_of x').symm
  rw [hx']
  exact Submodule.sum_mem _ fun i _ => hof i _ (tensor_locally_zero_of_exact (f i) (g i) (hfs i) (hgs i) (hfi i) (hgi i) U _ (hc i))

theorem flatS_tens : ∀ (R : Type) [CommRing R] {I J T : Cx R} (τ : Pair I J T), τ.IsTensor → (∀ t, FlatS (I.X t)) →
    (∀ t, FlatS (J.X t)) → ∀ w, FlatS (T.X w) := by
  intro R _ I J T τ hτ hI hJ w
  choose PI φI sI iI fI using hI
  choose PJ φJ sJ iJ fJ using hJ
  refine ⟨tensP (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => PI p.1.1) (fun p => PJ p.1.2),
    tensMap (fun p => φI p.1.1) (fun p => φJ p.1.2) ≫ liftN τ w, ?_, ?_, ?_⟩
  · intro U y
    refine loc_trans (loc_mono (fun V g h => ?_) (hτ.1 U w y))
    obtain ⟨x, hx⟩ := h
    refine loc_mono (fun W k h' => ?_) (tens_locIm (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => φI p.1.1)
      (fun p => φJ p.1.2) (fun p => sI p.1.1) (fun p => sJ p.1.2) V x)
    obtain ⟨z, hz⟩ := h'
    refine ⟨z, ?_⟩
    rw [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, hz]
    change τ.lift W w (Tens.res k w x) = _
    rw [lift_res, hx]
    simp [Sec.res]
  · intro U x hx
    refine loc_trans (loc_mono (fun V g h => ?_) (hτ.2 U w _ hx))
    have h' : ((tensMap (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => φI p.1.1) (fun p => φJ p.1.2)).app (op V)).hom
        (((tensP (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => PI p.1.1) (fun p => PJ p.1.2)).map g.op).hom x) = 0 := by
      rw [nat_apply]
      exact h
    refine loc_mono (fun W k h'' => ?_) (tens_locZero (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => φI p.1.1)
      (fun p => φJ p.1.2) (fun p => sI p.1.1) (fun p => sJ p.1.2) (fun p => iI p.1.1) (fun p => iJ p.1.2) V _ h')
    rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact h''
  · intro U hU
    haveI : ∀ p : {p : ℤ × ℤ // p.1 + p.2 = w}, Module.Flat (ULift.{1} R) ((PI p.1.1).obj (op U)) := fun p => fI _ U hU
    haveI : ∀ p : {p : ℤ × ℤ // p.1 + p.2 = w}, Module.Flat (ULift.{1} R) ((PJ p.1.2).obj (op U)) := fun p => fJ _ U hU
    haveI : ∀ p : {p : ℤ × ℤ // p.1 + p.2 = w},
        Module.Flat (ULift.{1} R) ((PI p.1.1).obj (op U) ⊗[ULift.{1} R] (PJ p.1.2).obj (op U)) := fun p => inferInstance
    exact Module.Flat.directSum

end GlobalTheory.EtC.FlatTens

end
