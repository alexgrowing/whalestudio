import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.USt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis

open CategoryTheory.Limits

section Fibre

variable {R : Type} [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Sp R) (g : Y ⟶ Sp R)

instance affPt_isOpenImmersion {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) : IsOpenImmersion (affPt s U) :=
  IsAffineOpen.isOpenImmersion_fromSpec U.2

def tensPt (U : X.affineOpens) (V : Y.affineOpens) :
    Sp (Sec f U.1 ⊗[R] Sec g V.1) ⟶ pullback f g :=
  (pullbackSpecIso R (Sec f U.1) (Sec g V.1)).inv ≫
    pullback.map _ _ f g (affPt f U) (affPt g V) (𝟙 _)
      (by rw [affPt_w, Category.comp_id]) (by rw [affPt_w, Category.comp_id])

instance tensPt_isOpenImmersion (U : X.affineOpens) (V : Y.affineOpens) : IsOpenImmersion (tensPt f g U V) := by
  unfold tensPt; infer_instance

theorem tensPt_fst (U : X.affineOpens) (V : Y.affineOpens) :
    tensPt f g U V ≫ pullback.fst f g =
      spMap (Algebra.TensorProduct.includeLeftRingHom : Sec f U.1 →+* Sec f U.1 ⊗[R] Sec g V.1) ≫ affPt f U := by
  simp only [tensPt, Category.assoc, pullback.lift_fst, pullback.map]
  rw [pullbackSpecIso_inv_fst_assoc]

theorem tensPt_snd (U : X.affineOpens) (V : Y.affineOpens) :
    tensPt f g U V ≫ pullback.snd f g =
      spMap ((Algebra.TensorProduct.includeRight : Sec g V.1 →ₐ[R] Sec f U.1 ⊗[R] Sec g V.1) : Sec g V.1 →+* _) ≫ affPt g V := by
  simp only [tensPt, Category.assoc, pullback.lift_snd, pullback.map]
  rw [pullbackSpecIso_inv_snd_assoc]

theorem range_tensPt (U : X.affineOpens) (V : Y.affineOpens) :
    Set.range (tensPt f g U V) = (pullback.fst f g) ⁻¹' (U.1 : Set X) ∩ (pullback.snd f g) ⁻¹' (V.1 : Set Y) := by
  have e := Scheme.Pullback.range_map _ _ f g (affPt f U) (affPt g V) (𝟙 _)
      (by rw [affPt_w, Category.comp_id]) (by rw [affPt_w, Category.comp_id])
  have hU : Set.range (affPt f U) = (U.1 : Set X) := U.2.range_fromSpec
  have hV : Set.range (affPt g V) = (V.1 : Set Y) := V.2.range_fromSpec
  rw [hU, hV] at e
  rw [← e, tensPt, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, (pullbackSpecIso R _ _).inv.surjective.range_eq, Set.image_univ]

end Fibre

section Fibre2

variable {R : Type} [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Sp R) (g : Y ⟶ Sp R)

theorem isAffineOpen_inf_preimage (U : X.affineOpens) (V : Y.affineOpens) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U.1 ⊓ pullback.snd f g ⁻¹ᵁ V.1) := by
  have h := isAffineOpen_opensRange (tensPt f g U V)
  convert h using 1
  refine TopologicalSpace.Opens.ext ?_
  exact (range_tensPt f g U V).symm

theorem bijective_tens (U : X.affineOpens) (V : Y.affineOpens) (W : (pullback f g).affineOpens)
    (hW : W.1 = pullback.fst f g ⁻¹ᵁ U.1 ⊓ pullback.snd f g ⁻¹ᵁ V.1) (s' : pullback f g ⟶ Sp R)
    (hU : W.1 ≤ pullback.fst f g ⁻¹ᵁ U.1) (hV : W.1 ≤ pullback.snd f g ⁻¹ᵁ V.1)
    (α : Sec f U.1 ⊗[R] Sec g V.1 →+* Sec s' W.1)
    (hα : ∀ b c, α (b ⊗ₜ c) = secPull (φ := pullback.fst f g) f s' ⟨(W, U), hU⟩ b *
      secPull (φ := pullback.snd f g) g s' ⟨(W, V), hV⟩ c) : Function.Bijective α := by
  haveI : Mono (affPt f U) := IsOpenImmersion.mono _
  haveI : Mono (affPt g V) := IsOpenImmersion.mono _
  have hr : Set.range (affPt s' W) = Set.range (tensPt f g U V) := by
    rw [range_tensPt]
    refine (W.2.range_fromSpec).trans ?_
    rw [hW]; rfl
  let e := IsOpenImmersion.isoOfRangeEq (affPt s' W) (tensPt f g U V) hr
  have he : e.hom ≫ tensPt f g U V = affPt s' W := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let a : CommRingCat.of (Sec f U.1 ⊗[R] Sec g V.1) ⟶ CommRingCat.of (Sec s' W.1) := Spec.preimage e.hom
  have ha : spMap a.hom = e.hom := Spec.map_preimage e.hom
  have hL : a.hom.comp Algebra.TensorProduct.includeLeftRingHom = secPull (φ := pullback.fst f g) f s' ⟨(W, U), hU⟩ := by
    have k : spMap (a.hom.comp Algebra.TensorProduct.includeLeftRingHom) ≫ affPt f U =
        spMap (secPull (φ := pullback.fst f g) f s' ⟨(W, U), hU⟩) ≫ affPt f U := by
      rw [secPull_affPt (φ := pullback.fst f g) f s' ⟨(W, U), hU⟩, spMap_comp, Category.assoc, ha, ← tensPt_fst, ← Category.assoc, he]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono (affPt f U)).1 k))
  have hR : a.hom.comp ((Algebra.TensorProduct.includeRight : Sec g V.1 →ₐ[R] Sec f U.1 ⊗[R] Sec g V.1) : Sec g V.1 →+* _) =
      secPull (φ := pullback.snd f g) g s' ⟨(W, V), hV⟩ := by
    have k : spMap (a.hom.comp ((Algebra.TensorProduct.includeRight : Sec g V.1 →ₐ[R] Sec f U.1 ⊗[R] Sec g V.1) : Sec g V.1 →+* _)) ≫ affPt g V =
        spMap (secPull (φ := pullback.snd f g) g s' ⟨(W, V), hV⟩) ≫ affPt g V := by
      rw [secPull_affPt (φ := pullback.snd f g) g s' ⟨(W, V), hV⟩, spMap_comp, Category.assoc, ha, ← tensPt_snd, ← Category.assoc, he]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono (affPt g V)).1 k))
  have hEq : ∀ t, α t = a.hom t := fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul b c =>
      rw [hα, ← hL, ← hR, RingHom.comp_apply, RingHom.comp_apply, ← map_mul]
      congr 1
      simp
  have hI : IsIso (Spec.map a) := by rw [Spec.map_preimage]; infer_instance
  have hb : Function.Bijective a.hom := isIso_SpecMap_iff.1 hI
  exact (funext hEq : ⇑α = ⇑a.hom) ▸ hb

end Fibre2

section Cochain

variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]

def Bx (P : Type) : Type := P × P

instance : SemilatticeInf (Bx P) := inferInstanceAs (SemilatticeInf (P × P))

theorem Bx.le_fst {x y : Bx P} (h : x ≤ y) : x.1 ≤ y.1 := (Prod.le_def.1 h).1

theorem Bx.le_snd {x y : Bx P} (h : x ≤ y) : x.2 ≤ y.2 := (Prod.le_def.1 h).2

def boxG (P : Type) [SemilatticeInf P] : (Bx P)ᵒᵖ ⥤ Pᵒᵖ × Pᵒᵖ where
  obj T := (op T.unop.1, op T.unop.2)
  map φ := ((homOfLE (Bx.le_fst (leOfHom φ.unop))).op, (homOfLE (Bx.le_snd (leOfHom φ.unop))).op)
  map_id _ := Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  map_comp _ _ := Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

def boxGi (P : Type) [SemilatticeInf P] : Pᵒᵖ × Pᵒᵖ ⥤ (Bx P)ᵒᵖ where
  obj T := op (T.1.unop, T.2.unop)
  map φ := (homOfLE (Prod.le_def.2 ⟨leOfHom φ.1.unop, leOfHom φ.2.unop⟩)).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem pull1_surjective_of_bijective (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (F' : (Bx P)ᵒᵖ ⥤ CommAlgCat.{0} R)
    (m : CoefMap (RingHom.id R) (box F) F') (hG : m.G = boxG P) (hb : ∀ T, Function.Bijective (m.α T)) :
    Function.Surjective m.pull1 := by
  obtain ⟨G, α, nat, sm⟩ := m
  obtain rfl : G = boxG P := hG
  intro c
  obtain ⟨f', rfl⟩ := H1.mk_surjective _ c
  let e : ∀ T, (box F).obj ((boxG P).obj T) ≃+* F'.obj T := fun T ↦ RingEquiv.ofBijective (α T) (hb T)
  have he : ∀ T x, α T ((e T).symm x) = x := fun T x ↦ (e T).apply_symm_apply x
  let f : C1 (box F) := fun T T' φ ↦ (e ((boxGi P).obj T')).symm (f'.1 _ _ ((boxGi P).map φ))
  have hf : f ∈ Z1 (box F) := by
    intro T T' T'' φ ψ
    refine (hb ((boxGi P).obj T'')).1 ?_
    have h1 : α ((boxGi P).obj T'') (f T T'' (φ ≫ ψ)) = f'.1 _ _ ((boxGi P).map (φ ≫ ψ)) := he _ _
    have h2 : α ((boxGi P).obj T') (f T T' φ) = f'.1 _ _ ((boxGi P).map φ) := he _ _
    have h3 : α ((boxGi P).obj T'') (f T' T'' ψ) = f'.1 _ _ ((boxGi P).map ψ) := he _ _
    have n : α ((boxGi P).obj T'') (mp (box F) ψ (f T T' φ)) =
        mp F' ((boxGi P).map ψ) (α ((boxGi P).obj T') (f T T' φ)) := nat ((boxGi P).map ψ) (f T T' φ)
    refine h1.trans ?_
    refine Eq.trans ?_ (map_add (α ((boxGi P).obj T'')) (mp (box F) ψ (f T T' φ)) (f T' T'' ψ)).symm
    have c : f'.1 _ _ ((boxGi P).map (φ ≫ ψ)) = mp F' ((boxGi P).map ψ) (f'.1 _ _ ((boxGi P).map φ)) +
        f'.1 _ _ ((boxGi P).map ψ) := by
      rw [Functor.map_comp]; exact f'.2 _ _
    exact c.trans (congrArg₂ (· + ·) ((congrArg (mp F' ((boxGi P).map ψ)) h2.symm).trans n.symm) h3.symm)
  refine ⟨H1.mk _ ⟨f, hf⟩, ?_⟩
  refine congrArg (H1.mk F') (Subtype.ext ?_)
  funext T T' φ
  exact he T' _

end Cochain

section Sys

variable {R : Type} [CommRing R] {A : Over (Sp R)} {P : Type} [SemilatticeInf P]

def boxSys (S : Sys A.left P) : Sys (A ⊗ A).left (Bx P) where
  u q := ⟨(fst A A).left ⁻¹ᵁ (S.u q.1).1 ⊓ (snd A A).left ⁻¹ᵁ (S.u q.2).1,
    isAffineOpen_inf_preimage A.hom A.hom (S.u q.1) (S.u q.2)⟩
  map_inf x y := by
    have h1 : (S.u (x ⊓ y).1).1 = (S.u x.1).1 ⊓ (S.u y.1).1 := S.map_inf x.1 y.1
    have h2 : (S.u (x ⊓ y).2).1 = (S.u x.2).1 ⊓ (S.u y.2).1 := S.map_inf x.2 y.2
    change (fst A A).left ⁻¹ᵁ (S.u (x ⊓ y).1).1 ⊓ (snd A A).left ⁻¹ᵁ (S.u (x ⊓ y).2).1 = _
    rw [h1, h2]
    ext z
    simp only [TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_preimage, Set.mem_inter_iff, Set.mem_preimage,
      SetLike.mem_coe]
    tauto
  cover := by
    refine eq_top_iff.2 fun z _ ↦ ?_
    have h : ∀ w : A.left, ∃ a, w ∈ (S.u a).1 := fun w ↦ by
      have : w ∈ ⨆ a, (S.u a).1 := by rw [S.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    obtain ⟨a, ha⟩ := h ((fst A A).left z)
    obtain ⟨b, hb⟩ := h ((snd A A).left z)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨((a, b) : Bx P), ha, hb⟩

def pairL (S : Sys A.left P) (q : Bx P) : Pair (fst A A).left := ⟨((boxSys S).u q, S.u q.1), inf_le_left⟩

def pairR (S : Sys A.left P) (q : Bx P) : Pair (snd A A).left := ⟨((boxSys S).u q, S.u q.2), inf_le_right⟩

def gL (S : Sys A.left P) : (Bx P)ᵒᵖ ⥤ (Pair (fst A A).left)ᵒᵖ :=
  (Monotone.functor (f := pairL S) fun _ _ h ↦
    Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(boxSys S).mono h, S.mono (Bx.le_fst h)⟩)).op

def gR (S : Sys A.left P) : (Bx P)ᵒᵖ ⥤ (Pair (snd A A).left)ᵒᵖ :=
  (Monotone.functor (f := pairR S) fun _ _ h ↦
    Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(boxSys S).mono h, S.mono (Bx.le_snd h)⟩)).op

def kL (S : Sys A.left P) :
    CoefMap (RingHom.id R) (OPair (fst A A).left (A ⊗ A).hom) (OSys (A ⊗ A).hom (boxSys S)) where
  G := gL S
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def kR (S : Sys A.left P) :
    CoefMap (RingHom.id R) (OPair (snd A A).left (A ⊗ A).hom) (OSys (A ⊗ A).hom (boxSys S)) where
  G := gR S
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def algOfSemi {B B' : Type} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (a : B →+* B')
    (h : SemiHom (RingHom.id R) a) : B →ₐ[R] B' :=
  { a with
    commutes' := fun r ↦ by
      have k := h r 1
      simpa [Algebra.algebraMap_eq_smul_one] using k }

def algL (S : Sys A.left P) (T : (Bx P)ᵒᵖ) :
    (OSys A.hom S).obj (op T.unop.1) →ₐ[R] (OSys (A ⊗ A).hom (boxSys S)).obj T :=
  algOfSemi (secPull A.hom (A ⊗ A).hom (pairL S T.unop)) (semiHom_secPull (wOver (fst A A)) (pairL S T.unop))

def algR (S : Sys A.left P) (T : (Bx P)ᵒᵖ) :
    (OSys A.hom S).obj (op T.unop.2) →ₐ[R] (OSys (A ⊗ A).hom (boxSys S)).obj T :=
  algOfSemi (secPull A.hom (A ⊗ A).hom (pairR S T.unop)) (semiHom_secPull (wOver (snd A A)) (pairR S T.unop))

theorem algL_nat (S : Sys A.left P) {T T' : (Bx P)ᵒᵖ} (φ : T ⟶ T') (b : (OSys A.hom S).obj (op T.unop.1)) :
    algL S T' (mp (OSys A.hom S) ((boxG P).map φ).1 b) = mp (OSys (A ⊗ A).hom (boxSys S)) φ (algL S T b) :=
  ((pairPull (wOver (fst A A))).comp (kL S)).naturality φ b

theorem algR_nat (S : Sys A.left P) {T T' : (Bx P)ᵒᵖ} (φ : T ⟶ T') (b : (OSys A.hom S).obj (op T.unop.2)) :
    algR S T' (mp (OSys A.hom S) ((boxG P).map φ).2 b) = mp (OSys (A ⊗ A).hom (boxSys S)) φ (algR S T b) :=
  ((pairPull (wOver (snd A A))).comp (kR S)).naturality φ b

def boxCoef (S : Sys A.left P) :
    CoefMap (RingHom.id R) (box (OSys A.hom S)) (OSys (A ⊗ A).hom (boxSys S)) where
  G := boxG P
  α T := (Algebra.TensorProduct.productMap (algL S T) (algR S T)).toRingHom
  naturality {T T'} φ b := by
    have e : (Algebra.TensorProduct.productMap (algL S T') (algR S T')).comp
        (Algebra.TensorProduct.map (mp (OSys A.hom S) ((boxG P).map φ).1) (mp (OSys A.hom S) ((boxG P).map φ).2)) =
        (mp (OSys (A ⊗ A).hom (boxSys S)) φ).comp (Algebra.TensorProduct.productMap (algL S T) (algR S T)) :=
      Algebra.TensorProduct.ext' fun x y ↦
        (Algebra.TensorProduct.productMap_apply_tmul _ _ _ _).trans
          ((congrArg₂ (· * ·) (algL_nat S φ x) (algR_nat S φ y)).trans
            ((map_mul (mp (OSys (A ⊗ A).hom (boxSys S)) φ) _ _).symm.trans
              (congrArg (mp (OSys (A ⊗ A).hom (boxSys S)) φ)
                (Algebra.TensorProduct.productMap_apply_tmul _ _ _ _).symm)))
    exact congrArg (fun t ↦ t b) e
  smul T r b := map_smul (Algebra.TensorProduct.productMap (algL S T) (algR S T)) r b

end Sys

section Main

variable {R : Type} [CommRing R] {A : Over (Sp R)} {P : Type} [SemilatticeInf P]

theorem boxCoef_bijective (S : Sys A.left P) (T : (Bx P)ᵒᵖ) : Function.Bijective ((boxCoef S).α T) :=
  bijective_tens A.hom A.hom (S.u T.unop.1) (S.u T.unop.2) ((boxSys S).u T.unop) rfl (A ⊗ A).hom inf_le_left inf_le_right
    ((boxCoef S).α T) fun b c ↦ Algebra.TensorProduct.productMap_apply_tmul (algL S T) (algR S T) b c

theorem boxCoef_pull1_surjective (S : Sys A.left P) : Function.Surjective (boxCoef S).pull1 :=
  pull1_surjective_of_bijective _ _ (boxCoef S) rfl (boxCoef_bijective S)

theorem boxCoef_tmul_one (S : Sys A.left P) (T : (Bx P)ᵒᵖ) (b : (OSys A.hom S).obj (op T.unop.1)) :
    (Algebra.TensorProduct.productMap (algL S T) (algR S T)) (b ⊗ₜ[R] (1 : (OSys A.hom S).obj (op T.unop.2))) =
      algL S T b :=
  (Algebra.TensorProduct.productMap_apply_tmul _ _ _ _).trans
    ((congrArg (algL S T b * ·) (map_one (algR S T))).trans (mul_one _))

theorem boxCoef_one_tmul (S : Sys A.left P) (T : (Bx P)ᵒᵖ) (b : (OSys A.hom S).obj (op T.unop.2)) :
    (Algebra.TensorProduct.productMap (algL S T) (algR S T)) ((1 : (OSys A.hom S).obj (op T.unop.1)) ⊗ₜ[R] b) =
      algR S T b :=
  (Algebra.TensorProduct.productMap_apply_tmul _ _ _ _).trans
    ((congrArg (· * algR S T b) (map_one (algL S T))).trans (one_mul _))

theorem boxCoef_left (S : Sys A.left P) (x : HO1 A.hom) (c : HO1 (A ⊗ A).hom) (h : IsPullO (wOver (fst A A)) x c) :
    (resSys _ (boxSys S)).pull1 c = (boxCoef S).pull1 ((boxL _).pull1 ((resSys _ S).pull1 x)) := by
  have e := congrArg (kL S).pull1 h
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ x
  obtain ⟨g, rfl⟩ := H1.mk_surjective _ c
  refine Eq.trans ?_ (e.symm.trans ?_)
  · rfl
  · refine congrArg (H1.mk _) (Subtype.ext ?_)
    funext T T' φ
    exact (boxCoef_tmul_one S T' _).symm

theorem boxCoef_right (S : Sys A.left P) (x : HO1 A.hom) (c : HO1 (A ⊗ A).hom) (h : IsPullO (wOver (snd A A)) x c) :
    (resSys _ (boxSys S)).pull1 c = (boxCoef S).pull1 ((boxR _).pull1 ((resSys _ S).pull1 x)) := by
  have e := congrArg (kR S).pull1 h
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ x
  obtain ⟨g, rfl⟩ := H1.mk_surjective _ c
  refine Eq.trans ?_ (e.symm.trans ?_)
  · rfl
  · refine congrArg (H1.mk _) (Subtype.ext ?_)
    funext T T' φ
    exact (boxCoef_one_tmul S T' _).symm

theorem exists_boxSys : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (P : Type) [SemilatticeInf P] (S : Sys A.left P),
    ∃ (Q : Type) (_ : SemilatticeInf Q) (S' : Sys (A ⊗ A).left Q)
      (m : CoefMap (RingHom.id R) (box (OSys A.hom S)) (OSys (A ⊗ A).hom S')),
      Function.Surjective m.pull1 ∧
      (∀ x c, IsPullO (wOver (fst A A)) x c →
        (resSys _ S').pull1 c = m.pull1 ((boxL _).pull1 ((resSys _ S).pull1 x))) ∧
      (∀ x c, IsPullO (wOver (snd A A)) x c →
        (resSys _ S').pull1 c = m.pull1 ((boxR _).pull1 ((resSys _ S).pull1 x))) :=
  fun _ _ _ P _ S ↦ ⟨Bx P, inferInstance, boxSys S, boxCoef S, boxCoef_pull1_surjective S, boxCoef_left S,
    boxCoef_right S⟩

end Main

end GlobalTheory.CompanionTheory.Axis
