import Development.EtaleCohomology.TateTwists.TtTensExPf

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations
namespace TTP

variable {R : Type} [CommRing R]

noncomputable section

abbrev dI (I : Cx R) (U : Scheme.{0}) (s : ℤ) : Sec (I.X s) U →ₗ[ULift.{1} R] Sec (I.X (s + 1)) U :=
  ((I.d s (s + 1)).hom.app (op U)).hom

theorem dI_dI (I : Cx R) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) : dI I U (s + 1) (dI I U s a) = 0 := by
  have h := congrArg (fun f => ((f.hom.app (op U)).hom a)) (I.d_comp_d s (s + 1) (s + 1 + 1))
  exact h.trans (by simp)

theorem dI_res (I : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (s : ℤ) (a : Sec (I.X s) U) :
    dI I V s (((I.X s).obj.map g.op).hom a) = ((I.X (s + 1)).obj.map g.op).hom (dI I U s a) := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f a) ((I.d s (s + 1)).hom.naturality g.op)
  exact h

def dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p =>
    (DirectSum.lof (ULift.{1} R) {q : ℤ × ℤ // q.1 + q.2 = w + 1}
        (fun q => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map (dI I U p.1.1) LinearMap.id) +
    ((p.1.1.negOnePow : ℤ) • (DirectSum.lof (ULift.{1} R) {q : ℤ × ℤ // q.1 + q.2 = w + 1}
        (fun q => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id (dI J U p.1.2)))

theorem dT_of (I J : Cx R) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    dT I J U w (DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s, t), h⟩ (a ⊗ₜ b)) =
    DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s + 1, t), by omega⟩ (dI I U s a ⊗ₜ b) +
    (s.negOnePow : ℤ) • DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s, t + 1), by omega⟩ (a ⊗ₜ dI J U t b) := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R), dT, DirectSum.toModule_lof]
  simp [DirectSum.lof_eq_of]

theorem dT_dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : (dT I J U (w + 1)).comp (dT I J U w) = 0 := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, LinearMap.zero_apply]
  rw [dT_of, map_add, map_zsmul, dT_of, dT_of]
  simp [dI_dI, Int.negOnePow_succ]

theorem res_of (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Tens.res (I := I) (J := J) g w (DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s, t), h⟩ (a ⊗ₜ b)) =
    DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) V ⊗[ULift.{1} R] Sec (J.X q.1.2) V)
      ⟨(s, t), h⟩ (((I.X s).obj.map g.op).hom a ⊗ₜ ((J.X t).obj.map g.op).hom b) := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R), Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul, DirectSum.lof_eq_of]

theorem res_id (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens.res (I := I) (J := J) (𝟙 U) w = LinearMap.id := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, LinearMap.id_apply]
  rw [res_of]
  simp

theorem res_comp (I J : Cx R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (w : ℤ) :
    Tens.res (I := I) (J := J) (f ≫ g) w = Tens.res f w ∘ₗ Tens.res g w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [res_of, res_of, res_of]
  simp

theorem dT_res (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    dT I J V w ∘ₗ Tens.res g w = Tens.res g (w + 1) ∘ₗ dT I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [res_of, dT_of, dT_of, map_add, map_zsmul, res_of, res_of, dI_res, dI_res]

def PF (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of (ULift.{1} R) (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    apply ModuleCat.hom_ext
    simp only [unop_id, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    exact res_id I J U.unop w
  map_comp f g := by
    apply ModuleCat.hom_ext
    simp only [unop_comp, ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact res_comp I J g.unop f.unop w

def dN (I J : Cx R) (w : ℤ) : PF I J w ⟶ PF I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality U V g := by
    apply ModuleCat.hom_ext
    simp only [PF, ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact dT_res I J g.unop w

theorem dN_dN (I J : Cx R) (w : ℤ) : dN I J w ≫ dN I J (w + 1) = 0 := by
  ext U : 2
  apply ModuleCat.hom_ext
  simp only [NatTrans.comp_app, dN, NatTrans.app_zero, ModuleCat.hom_zero]
  exact dT_dT I J U.unop w

def PC (I J : Cx R) : CochainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℤ :=
  CochainComplex.of (fun w => PF I J w) (fun w => dN I J w) (fun w => dN_dN I J w)

def tensPre (I J : Cx R) : TensPre I J where
  P := PC I J
  e U w := LinearEquiv.refl (ULift.{1} R) (Tens I J U w)
  nat g w x := rfl
  leibniz U s t w h a b := by
    simp only [PC]
    rw [CochainComplex.of_d]
    exact (dT_of I J U s t w h a b).trans (congrArg (HAdd.hAdd _) (Units.smul_def _ _).symm)

end

end TTP

theorem tt_tens_pre_of : tt_tens_pre := fun _ _ I J => ⟨TTP.tensPre I J⟩

end LateralTheory.EtaleFoundations
