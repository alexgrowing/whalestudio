import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLift
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.res_lof {I J : _root_.GlobalTheory.EtC.Cx R} {V U : Scheme.{0}}
    (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U) (b : _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U) :
    _root_.GlobalTheory.EtC.Tens.res g w
      (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U)
        p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) V ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) V) p
        (_root_.GlobalTheory.EtC.Sec.res g a ⊗ₜ _root_.GlobalTheory.EtC.Sec.res g b) := by
  unfold _root_.GlobalTheory.EtC.Tens.res
  rw [DirectSum.lmap_lof, TensorProduct.map_tmul]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.sres_id {F : _root_.GlobalTheory.EtC.Shv R} {U : Scheme.{0}}
    (a : _root_.GlobalTheory.EtC.Sec F U) : _root_.GlobalTheory.EtC.Sec.res (𝟙 U) a = a := by
  unfold _root_.GlobalTheory.EtC.Sec.res
  simp

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.sres_comp {F : _root_.GlobalTheory.EtC.Shv R} {W V U : Scheme.{0}}
    (g : W ⟶ V) (f : V ⟶ U) (a : _root_.GlobalTheory.EtC.Sec F U) :
    _root_.GlobalTheory.EtC.Sec.res (g ≫ f) a =
      _root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.Sec.res f a) := by
  unfold _root_.GlobalTheory.EtC.Sec.res
  simp

def pre (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_)
    simp [res_lof, sres_id]
  map_comp f g := by
    refine ModuleCat.hom_ext (DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_)
    simp [res_lof, sres_comp]

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.smap_res {F G : _root_.GlobalTheory.EtC.Shv R} (φ : F ⟶ G)
    {V U : Scheme.{0}} (g : V ⟶ U) (a : _root_.GlobalTheory.EtC.Sec F U) :
    _root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.Sec.map φ a) =
      _root_.GlobalTheory.EtC.Sec.map φ (_root_.GlobalTheory.EtC.Sec.res g a) := by
  unfold _root_.GlobalTheory.EtC.Sec.res _root_.GlobalTheory.EtC.Sec.map
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← NatTrans.naturality]

def dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p =>
    (DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp; omega⟩ ∘ₗ
      TensorProduct.map ((I.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id) +
    ((p.1.1.negOnePow : ℤ) • (DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom))

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.dT_lof {I J : _root_.GlobalTheory.EtC.Cx R} (U : Scheme.{0})
    (s t w : ℤ) (h : s + t = w) (a : _root_.GlobalTheory.EtC.Sec (I.X s) U)
    (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    _root_.GlobalTheory.EtC.TensEx.dT I J U w (DirectSum.lof (ULift.{1} R) _
      (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U)
        ⟨(s, t), h⟩ (a ⊗ₜ b)) =
    DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
        ⟨(s + 1, t), by simp; omega⟩
        (_root_.GlobalTheory.EtC.Sec.map (I.d s (s + 1)) a ⊗ₜ b) +
    (s.negOnePow : ℤ) • DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
        ⟨(s, t + 1), by simp; omega⟩
        (a ⊗ₜ _root_.GlobalTheory.EtC.Sec.map (J.d t (t + 1)) b) := by
  unfold _root_.GlobalTheory.EtC.TensEx.dT
  rw [DirectSum.toModule_lof]
  rfl

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

theorem smap_zero {F G : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sec.map (0 : F ⟶ G) a = 0 := rfl

def D (I J : Cx R) (w : ℤ) : pre I J w ⟶ pre I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality U V g := by
    refine ModuleCat.hom_ext (DirectSum.linearMap_ext _ fun ⟨⟨s, t⟩, h⟩ => TensorProduct.ext' fun a b => ?_)
    simp only [pre, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    erw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    rw [res_lof, dT_lof, dT_lof, map_add, map_zsmul, res_lof, res_lof, smap_res, smap_res]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem sec_map_d_map_d_eq_zero (K : _root_.GlobalTheory.EtC.Cx R) {U : Scheme.{0}}
    (i j k : ℤ) (a : _root_.GlobalTheory.EtC.Sec (K.X i) U) :
    _root_.GlobalTheory.EtC.Sec.map (K.d j k) (_root_.GlobalTheory.EtC.Sec.map (K.d i j) a) = 0 := by
  have key := congrArg (fun f : K.X i ⟶ K.X k => (f.hom.app (op U)).hom a) (K.d_comp_d i j k)
  exact key

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.D_comp (I J : _root_.GlobalTheory.EtC.Cx R) (w : ℤ) :
    _root_.GlobalTheory.EtC.TensEx.D I J w ≫
      _root_.GlobalTheory.EtC.TensEx.D I J (w + 1) = 0 := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (DirectSum.linearMap_ext _
    fun ⟨⟨s, t⟩, h⟩ => TensorProduct.ext' fun a b => ?_))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  show _root_.GlobalTheory.EtC.TensEx.dT I J U.unop (w + 1) (_root_.GlobalTheory.EtC.TensEx.dT I J U.unop w
    (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U.unop ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U.unop)
      ⟨(s, t), h⟩ (a ⊗ₜ b))) = 0
  rw [_root_.GlobalTheory.EtC.TensEx.dT_lof, map_add, map_zsmul, _root_.GlobalTheory.EtC.TensEx.dT_lof,
    _root_.GlobalTheory.EtC.TensEx.dT_lof, sec_map_d_map_d_eq_zero, sec_map_d_map_d_eq_zero,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, map_zero]
  simp [Int.negOnePow_succ, smul_add]

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

def cx (I J : Cx R) : Cx R :=
  CochainComplex.of (fun w => (presheafToSheaf Scheme.etaleTopology _).obj (pre I J w))
    (fun w => (presheafToSheaf Scheme.etaleTopology _).map (D I J w))
    (fun w => by rw [← Functor.map_comp, D_comp, Functor.map_zero])

def toS (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Sec ((cx I J).X w) U :=
  ((toSheafify Scheme.etaleTopology (pre I J w)).app (op U)).hom

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.toS_res (I J : _root_.GlobalTheory.EtC.Cx R) {V U : Scheme.{0}}
    (g : V ⟶ U) (w : ℤ) (x : _root_.GlobalTheory.EtC.Tens I J U w) :
    _root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.TensEx.toS I J U w x) =
      _root_.GlobalTheory.EtC.TensEx.toS I J V w (_root_.GlobalTheory.EtC.Tens.res g w x) := by
  have key := congrArg (fun f => ModuleCat.Hom.hom f x)
    ((toSheafify Scheme.etaleTopology (_root_.GlobalTheory.EtC.TensEx.pre I J w)).naturality g.op)
  exact key.symm

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.d_toS (I J : _root_.GlobalTheory.EtC.Cx R)
    (U : Scheme.{0}) (w : ℤ) (x : _root_.GlobalTheory.EtC.Tens I J U w) :
    _root_.GlobalTheory.EtC.Sec.map ((_root_.GlobalTheory.EtC.TensEx.cx I J).d w (w + 1))
        (_root_.GlobalTheory.EtC.TensEx.toS I J U w x) =
      _root_.GlobalTheory.EtC.TensEx.toS I J U (w + 1) (_root_.GlobalTheory.EtC.TensEx.dT I J U w x) := by
  have hd : (_root_.GlobalTheory.EtC.TensEx.cx I J).d w (w + 1) = (presheafToSheaf Scheme.etaleTopology _).map
      (_root_.GlobalTheory.EtC.TensEx.D I J w) := by
    unfold _root_.GlobalTheory.EtC.TensEx.cx
    simp
  have key := congrArg (fun f => ModuleCat.Hom.hom (f.app (op U)) x)
    (toSheafify_naturality Scheme.etaleTopology (_root_.GlobalTheory.EtC.TensEx.D I J w))
  rw [hd]
  exact key.symm

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

def pair (I J : Cx R) : Pair I J (cx I J) where
  mul U s t w h := (TensorProduct.mk (ULift.{1} R) _ _).compr₂ (toS I J U w ∘ₗ
    DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩)
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [toS_res, res_lof]
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [d_toS, dT_lof, map_add, map_zsmul, Units.smul_def]

end GlobalTheory.EtC.TensEx

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in

theorem _root_.GlobalTheory.EtC.tensor_exists :
    ∀ (R : Type) [CommRing R] (I J : _root_.GlobalTheory.EtC.Cx R),
      ∃ (K : _root_.GlobalTheory.EtC.Cx R) (τ : _root_.GlobalTheory.EtC.Pair I J K), τ.IsTensor := by
  intro R _ I J
  refine ⟨_root_.GlobalTheory.EtC.TensEx.cx I J, _root_.GlobalTheory.EtC.TensEx.pair I J, ?_⟩
  have hlift : ∀ (U : Scheme.{0}) (w : ℤ),
      (_root_.GlobalTheory.EtC.TensEx.pair I J).lift U w =
        _root_.GlobalTheory.EtC.TensEx.toS I J U w := by
    intro U w
    refine DirectSum.linearMap_ext _ fun ⟨⟨s, t⟩, h⟩ => TensorProduct.ext' fun a b => ?_
    unfold _root_.GlobalTheory.EtC.Pair.lift
    rw [LinearMap.comp_apply, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul]
    rfl
  unfold _root_.GlobalTheory.EtC.Pair.IsTensor
  simp only [hlift]
  exact ⟨fun U w y =>
      (_root_.GlobalTheory.EtC.toSheafify_loc_bij_lift R (_root_.GlobalTheory.EtC.TensEx.pre I J w)).1 U y,
    fun U w x hx =>
      (_root_.GlobalTheory.EtC.toSheafify_loc_bij_lift R (_root_.GlobalTheory.EtC.TensEx.pre I J w)).2.1 U x hx⟩
