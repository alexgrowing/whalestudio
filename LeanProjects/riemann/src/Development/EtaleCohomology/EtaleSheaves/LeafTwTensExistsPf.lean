import Development.EtaleCohomology.EtaleSheaves.LeafTwPairHtpyPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC MonoidalCategory

open scoped TensorProduct DirectSum

namespace LateralTheory.E.LeafTwTensExistsPf

variable {R : Type} [CommRing R]

abbrev PSh1 (R : Type) [CommRing R] := Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)

def tF (R : Type) [CommRing R] : Shv R ⥤ Shv R ⥤ PSh1 R :=
  sheafToPresheaf _ _ ⋙ curriedTensor (PSh1 R) ⋙ (Functor.whiskeringLeft _ _ _).obj (sheafToPresheaf _ _)

instance : MonoidalPreadditive (PSh1 R) where
  whiskerLeft_zero := by intros; exact NatTrans.ext (funext fun U => by simp; rfl)
  zero_whiskerRight := by intros; exact NatTrans.ext (funext fun U => by simp; rfl)
  whiskerLeft_add := by intros; exact NatTrans.ext (funext fun U => by simp; rfl)
  add_whiskerRight := by intros; exact NatTrans.ext (funext fun U => by simp; rfl)

instance : (tF R).PreservesZeroMorphisms where
  map_zero A B := by
    apply NatTrans.ext; funext C
    change (sheafToPresheaf _ _).map (0 : A ⟶ B) ▷ C.obj = 0
    rw [Functor.map_zero]; exact MonoidalPreadditive.zero_whiskerRight

instance (A : Shv R) : ((tF R).obj A).PreservesZeroMorphisms where
  map_zero B C := by
    change A.obj ◁ (sheafToPresheaf _ _).map (0 : B ⟶ C) = 0
    rw [Functor.map_zero]; exact MonoidalPreadditive.whiskerLeft_zero

example (I J : Cx R) : HomologicalComplex.HasMapBifunctor I J (tF R) (ComplexShape.up ℤ) := inferInstance
example (P : PSh1 R) : Presheaf.IsLocallySurjective Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) := inferInstance
example (P : PSh1 R) : Presheaf.IsLocallyInjective Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) := inferInstance

abbrev P (I J : Cx R) : CochainComplex (PSh1 R) ℤ := HomologicalComplex.mapBifunctor I J (tF R) (ComplexShape.up ℤ)

abbrev T (I J : Cx R) : Cx R := ((presheafToSheaf Scheme.etaleTopology _).mapHomologicalComplex _).obj (P I J)

abbrev jm (I J : Cx R) (s t w : ℤ) (h : s + t = w) : ((tF R).obj (I.X s)).obj (J.X t) ⟶ sheafify Scheme.etaleTopology ((P I J).X w) :=
  HomologicalComplex.ιMapBifunctor I J (tF R) (ComplexShape.up ℤ) s t w h ≫ toSheafify Scheme.etaleTopology _

theorem jm_d (I J : Cx R) (s t w : ℤ) (h : s + t = w) :
    jm I J s t w h ≫ sheafifyMap Scheme.etaleTopology ((P I J).d w (w + 1)) =
      ((tF R).map (I.d s (s + 1))).app (J.X t) ≫ jm I J (s + 1) t (w + 1) (by omega) +
      s.negOnePow • (((tF R).obj (I.X s)).map (J.d t (t + 1)) ≫ jm I J s (t + 1) (w + 1) (by omega)) := by
  rw [jm, Category.assoc, ← toSheafify_naturality, ← Category.assoc, HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel s (s + 1) by simp) _ _ (by simp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.up ℤ).Rel t (t + 1) by simp) _ (by simp; omega)]
  simp [Preadditive.add_comp, Category.assoc]

def tau (I J : Cx R) : Pair I J (T I J) where
  mul U s t w h := (TensorProduct.mk _ _ _).compr₂ ((jm I J s t w h).app (op U)).hom
  nat := by
    intro V U g s t w h a b
    have := congrArg (fun f => f.hom (a ⊗ₜ b)) ((jm I J s t w h).naturality g.op)
    exact this.symm
  leibniz := by
    intro U s t w h a b
    change ((jm I J s t w h ≫ sheafifyMap Scheme.etaleTopology ((P I J).d w (w + 1))).app (op U)).hom (a ⊗ₜ b) = _
    rw [jm_d]
    simp only [NatTrans.app_add, NatTrans.app_zsmul, NatTrans.comp_app, ModuleCat.hom_add, ModuleCat.hom_comp,
      LinearMap.add_apply, LinearMap.comp_apply, Units.smul_def]
    simp only [ModuleCat.hom_zsmul, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply]
    rfl

def Phi (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] ToType ((P I J).X w |>.obj (op U)) := by
  classical
  exact DirectSum.toModule _ _ _ fun p =>
    ((HomologicalComplex.ιMapBifunctor I J (tF R) (ComplexShape.up ℤ) p.1.1 p.1.2 w p.2).app (op U)).hom

theorem Phi_lof (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (t : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    Phi I J U w (DirectSum.of (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p t) =
      ((HomologicalComplex.ιMapBifunctor I J (tF R) (ComplexShape.up ℤ) p.1.1 p.1.2 w p.2).app (op U)).hom t := by
  classical
  unfold Phi
  exact DirectSum.toModule_lof (ULift.{1} R) (M := fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p t

theorem lift_eq (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    (tau I J).lift U w x = ((toSheafify Scheme.etaleTopology ((P I J).X w)).app (op U)).hom (Phi I J U w x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => first | (erw [map_zero, map_zero] <;> rfl) | (erw [map_zero, map_zero, map_zero] <;> rfl) | (erw [map_zero, map_zero, map_zero, map_zero] <;> rfl) | (simp only [map_zero]) | rfl
  | add x y hx hy => erw [map_add, map_add, map_add, hx, hy] <;> rfl
  | of p t =>
    rw [Phi_lof]
    unfold Pair.lift
    erw [DirectSum.toModule_lof]
    induction t using TensorProduct.induction_on with
    | zero => erw [map_zero, map_zero, map_zero]; rfl
    | add x y hx hy => erw [map_add, map_add, map_add, hx, hy]; rfl
    | tmul a b => rw [TensorProduct.lift.tmul]; rfl

theorem Phi_nat (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    ((P I J).X w |>.map g.op).hom (Phi I J U w x) = Phi I J V w (Tens.res g w x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => first | (erw [map_zero, map_zero] <;> rfl) | (erw [map_zero, map_zero, map_zero] <;> rfl) | (erw [map_zero, map_zero, map_zero, map_zero] <;> rfl) | (simp only [map_zero]) | rfl
  | add x y hx hy => erw [map_add, map_add, map_add, map_add, hx, hy] <;> rfl
  | of p t =>
    rw [Phi_lof]
    unfold Tens.res
    erw [DirectSum.lmap_lof]
    erw [Phi_lof]
    have := congrArg (fun f => f.hom t)
      ((HomologicalComplex.ιMapBifunctor I J (tF R) (ComplexShape.up ℤ) p.1.1 p.1.2 w p.2).naturality g.op)
    exact this.symm

abbrev GX (I J : Cx R) : GradedObject (ℤ × ℤ) (PSh1 R) :=
  ((((tF R).mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj I).obj J).toGradedObject

def hcol (I J : Cx R) (U : Scheme.{0}) (w : ℤ) :
    IsColimit (((evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj (op U)).mapCocone
      ((GX I J).cofanMapObj (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) w)) :=
  isColimitOfPreserves _ ((GX I J).isColimitCofanMapObj _ w)

def dsCocone (I J : Cx R) (U : Scheme.{0}) (w : ℤ) :
    Cocone (Discrete.functor ((GX I J).mapObjFun (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) w) ⋙
      (evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj (op U)) where
  pt := ModuleCat.of (ULift.{1} R) (Tens I J U w)
  ι := Discrete.natTrans fun k => ModuleCat.ofHom (DirectSum.lof (ULift.{1} R) _
    (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨k.as.1, k.as.2⟩)

theorem Phi_bij (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Function.Bijective (Phi I J U w) := by
  classical
  let hc := hcol I J U w
  let Ψ := hc.desc (dsCocone I J U w)
  have h1 : ∀ x, Ψ.hom (Phi I J U w x) = x := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => erw [map_zero]; first | rfl | exact map_zero Ψ.hom
    | add x y hx hy => erw [map_add, map_add, hx, hy]; rfl
    | of p t =>
      rw [Phi_lof]
      have := congrArg (fun f => f.hom t) (hc.fac (dsCocone I J U w) ⟨⟨p.1, p.2⟩⟩)
      exact this
  have h2 : ∀ y, Phi I J U w (Ψ.hom y) = y := by
    let PhiH : (dsCocone I J U w).pt ⟶ (((evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj (op U)).mapCocone
      ((GX I J).cofanMapObj (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) w)).pt :=
      ModuleCat.ofHom (Phi I J U w)
    have : Ψ ≫ PhiH = 𝟙 _ := by
      apply hc.hom_ext
      rintro ⟨k⟩
      rw [← Category.assoc, hc.fac, Category.comp_id]
      ext t
      exact Phi_lof I J U w ⟨k.1, k.2⟩ t
    intro y
    exact congrArg (fun f => f.hom y) this
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem tau_isTensor (I J : Cx R) : (tau I J).IsTensor := by
  constructor
  · intro U w y
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology ((P I J).X w)) y, ?_⟩
    rintro V g ⟨t, ht⟩
    obtain ⟨x, rfl⟩ := (Phi_bij I J V w).2 t
    exact ⟨x, by rw [lift_eq]; exact ht⟩
  · intro U w x hx
    rw [lift_eq] at hx
    have hm := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology ((P I J).X w))
      (X := op U) (Phi I J U w x) 0 (by rw [map_zero]; exact hx)
    refine ⟨_, hm, ?_⟩
    intro V g hg
    apply (Phi_bij I J V w).1
    rw [map_zero, ← Phi_nat]
    have hg' : ((P I J).X w |>.map g.op).hom (Phi I J U w x) = ((P I J).X w |>.map g.op).hom 0 := hg
    rw [hg', map_zero]

theorem tens_exists (I J : Cx R) : ∃ (K : Cx R) (τ : Pair I J K), τ.IsTensor := ⟨_, tau I J, tau_isTensor I J⟩

end LateralTheory.E.LeafTwTensExistsPf

theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists_of : LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists := by
  intro q _ i j
  exact LateralTheory.E.LeafTwTensExistsPf.tens_exists _ _
