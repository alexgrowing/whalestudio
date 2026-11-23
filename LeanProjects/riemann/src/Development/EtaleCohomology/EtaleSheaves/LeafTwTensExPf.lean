import Development.EtaleCohomology.EtaleSheaves.LeafTwPairExistsPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.E.LeafTwTensExPf

open Classical in
section
variable {R : Type} [CommRing R] (I J : Cx R)

theorem tres_tmul {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (a ⊗ₜ b)) =
    DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V) p (Sec.res g a ⊗ₜ Sec.res g b) := by
  simp [Tens.res]

def TP (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => simp_all
    | of p y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp_all
      | tmul a b =>
        have := tres_tmul I J (𝟙 U.unop) w p a b
        simp only [DirectSum.lof_eq_of] at this
        simp [this, Sec.res]
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => simp_all
    | of p y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp_all
      | tmul a b =>
        have h1 := tres_tmul I J (g.unop ≫ f.unop) w p a b
        have h2 := tres_tmul I J f.unop w p a b
        have h3 := tres_tmul I J g.unop w p (Sec.res f.unop a) (Sec.res f.unop b)
        simp only [DirectSum.lof_eq_of] at h1 h2 h3
        simp [h1, h2, Sec.res]
        exact h3.symm
end
end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

abbrev lo {U : Scheme.{0}} {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w}) :
    Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U →ₗ[ULift.{1} R] Tens I J U w :=
  DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p

def dT (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p =>
    lo I J (U := U) (w := w + 1) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map ((I.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
    ((p.1.1.negOnePow : ℤˣ) : ℤ) • (lo I J (U := U) (w := w + 1) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom)

theorem dT_tmul (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    dT I J U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      lo I J ⟨(s + 1, t), by simp only; omega⟩ (Sec.map (I.d s (s + 1)) a ⊗ₜ b) +
      ((s.negOnePow : ℤˣ) : ℤ) • lo I J ⟨(s, t + 1), by simp only; omega⟩ (a ⊗ₜ Sec.map (J.d t (t + 1)) b) := by
  simp [dT, lo, DirectSum.toModule_lof]

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

theorem dd0 {K : Cx R} {U : Scheme.{0}} (s : ℤ) (a : Sec (K.X s) U) :
    Sec.map (K.d (s + 1) (s + 1 + 1)) (Sec.map (K.d s (s + 1)) a) = 0 := by
  rw [LateralTheory.E.LeafTwPairExistsPf.map_map, HomologicalComplex.d_comp_d]
  simp [Sec.map]

theorem dT_nat {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    dT I J V w ∘ₗ Tens.res g w = Tens.res g (w + 1) ∘ₗ dT I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply]
  erw [tres_tmul, dT_tmul, dT_tmul, map_add, map_zsmul, tres_tmul, tres_tmul,
    LateralTheory.E.LeafTwPairExistsPf.res_map, LateralTheory.E.LeafTwPairExistsPf.res_map]

theorem dT_dT (U : Scheme.{0}) (w : ℤ) : dT I J U (w + 1) ∘ₗ dT I J U w = 0 := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [dT_tmul, map_add, map_zsmul]
  rw [dT_tmul (s := s + 1) (t := t) (w := w + 1)]
  rw [dT_tmul (s := s) (t := t + 1) (w := w + 1)]
  rw [dd0 (K := I), dd0 (K := J)]
  simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, zero_add, smul_zero, add_zero,
    Int.negOnePow_succ, Units.val_neg, neg_smul, neg_add_cancel]

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

def dTP (w : ℤ) : TP I J w ⟶ TP I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality _ _ g := ModuleCat.hom_ext (dT_nat I J g.unop w)

def PC : CochainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℤ :=
  CochainComplex.of (TP I J) (dTP I J) (fun w => by
    ext U : 2
    exact ModuleCat.hom_ext (dT_dT I J U.unop w))

def TC : Cx R := ((presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).mapHomologicalComplex _).obj (PC I J)

abbrev un (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Sec ((TC I J).X w) U :=
  ((toSheafify Scheme.etaleTopology.{0} (TP I J w)).app (op U)).hom

theorem un_nat {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Sec.res g (un I J U w x) = un I J V w (Tens.res g w x) :=
  (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology.{0} (TP I J w)).naturality g.op)) x).symm

theorem un_d (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Sec.map ((TC I J).d w (w + 1)) (un I J U w x) = un I J U (w + 1) (dT I J U w x) := by
  have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (congrArg (fun f => f.app (op U)) (toSheafify_naturality Scheme.etaleTopology.{0} (dTP I J w)))) x
  simp only [TC, PC, Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d] at this ⊢
  exact this.symm

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

def tau : Pair I J (TC I J) where
  mul U s t w h := (TensorProduct.mk _ _ _).compr₂ (un I J U w ∘ₗ lo I J ⟨(s, t), h⟩)
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply]
    rw [un_nat]
    congr 1
    exact tres_tmul I J g w ⟨(s, t), h⟩ a b
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply]
    rw [un_d, dT_tmul, map_add, map_zsmul, Units.smul_def]

theorem tau_lift (U : Scheme.{0}) (w : ℤ) : (tau I J).lift U w = un I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp [Pair.lift, tau]

theorem tau_isTensor : (tau I J).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} (TP I J w))
      (U := op U) y, fun V g ⟨t, ht⟩ => ⟨t, ?_⟩⟩
    rw [tau_lift]
    exact ht
  · rw [tau_lift] at hx
    refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} (TP I J w))
      (X := op U) x 0 (by rw [map_zero]; exact hx), fun V g hg => ?_⟩
    have : Tens.res g w x = Tens.res g w 0 := hg
    rwa [map_zero] at this

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf

theorem LeafTwTensEx_of : LateralTheory.E.LeafTwPairExistsPf.LeafTwTensEx := by
  intro q _ i j
  exact ⟨_, tau _ _, tau_isTensor _ _⟩

end LateralTheory.E.LeafTwTensExPf
