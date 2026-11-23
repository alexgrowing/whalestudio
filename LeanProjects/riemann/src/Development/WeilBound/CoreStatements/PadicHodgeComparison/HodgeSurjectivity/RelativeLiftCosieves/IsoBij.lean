import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FirstChernCoboundary
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.AffRelOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.SiteLaws

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

universe w w'

namespace CrystallineSemistableComparison.Onto

open Pb HT

namespace IsoBijectionLift

section Abstract

variable {R : Type} [CommRing R]

theorem upTo_one_iff {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) : UpTo (1 : R) f ↔ Function.Bijective f :=
  (CrystallineSemistableComparison.P.upTo_alg f (LinearMap.id : N →ₗ[R] N) 1 1).2.2.2.2

variable {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R}

theorem rel_bij (m : CH.Mor F F' (RingHom.id R)) {U Q : ObjectProperty C} {U' Q' : ObjectProperty C'}
    (hQ : Cosieve Q) (hQ' : Cosieve Q') (h : ∀ T, U' T → U (m.G.obj T)) (h' : ∀ T, Q' T → Q (m.G.obj T))
    (hb : ∀ n, Function.Bijective ((morU m h).pull n))
    (hc : ∀ n, Function.Bijective ((morU m (U := U ⊓ Q) (U' := U' ⊓ Q')
      (fun T hT => ⟨h T hT.1, h' T hT.2⟩)).pull n)) (n : ℕ) :
    Function.Bijective ((RC.mor m hQ hQ' h h').mapH n) := by
  have hle : U ⊓ Q ≤ U := fun T hT => hT.1
  have hle' : U' ⊓ Q' ≤ U' := fun T hT => hT.1
  let ι0 : Cx.Hom (RC F U hQ) (CH.cx (U.ι ⋙ F)) (RingHom.id R) :=
    ⟨fun n => (relS (U.ι ⋙ F) (fun T => Q T.obj) n).subtype, fun n x => rfl⟩
  let ι1 : Cx.Hom (RC F' U' hQ') (CH.cx (U'.ι ⋙ F')) (RingHom.id R) :=
    ⟨fun n => (relS (U'.ι ⋙ F') (fun T => Q' T.obj) n).subtype, fun n x => rfl⟩
  have key := (CrystallineSemistableComparison.P.five ι0 (resU F hle).hom
    (fun n x y hxy => Subtype.ext hxy)
    (fun n => AffineRelativeForms.res_exact F U Q hQ hle ι0 (fun _ _ => rfl) n)
    (fun n => AffineRelativeForms.res_surj F U Q hQ hle n)
    ι1 (resU F' hle').hom
    (fun n x y hxy => Subtype.ext hxy)
    (fun n => AffineRelativeForms.res_exact F' U' Q' hQ' hle' ι1 (fun _ _ => rfl) n)
    (fun n => AffineRelativeForms.res_surj F' U' Q' hQ' hle' n)
    (RC.mor m hQ hQ' h h') (morU m h).hom
    (morU m (U := U ⊓ Q) (U' := U' ⊓ Q') (fun T hT => ⟨h T hT.1, h' T hT.2⟩)).hom
    (fun n x => rfl) (fun n x => rfl) 1).2.1
  have := key (fun n => (upTo_one_iff _).2 (hb n)) (fun n => (upTo_one_iff _).2 (hc n)) n
  rw [one_pow] at this
  exact (upTo_one_iff _).1 this

end Abstract

section Geo

variable {K : Type} [CommRing K] {Z Y : Scheme.{0}}

theorem range_sub {S X : Scheme.{0}} (z : S ⟶ X) (V : X.Opens) (hz : ⊤ ≤ z ⁻¹ᵁ V) :
    Set.range z ⊆ Set.range V.ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  exact hz (show x ∈ (⊤ : S.Opens) from trivial)

variable (π : Y ⟶ Z) (U : Z.Opens) [IsIso (π ∣_ U)]

def liftPt {S : Scheme.{0}} (z : S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ U) : S ⟶ Y :=
  IsOpenImmersion.lift U.ι z (range_sub z U hz) ≫ inv (π ∣_ U) ≫ (π ⁻¹ᵁ U).ι

theorem liftPt_fac {S : Scheme.{0}} (z : S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ U) : liftPt π U z hz ≫ π = z := by
  unfold liftPt
  rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]

theorem liftPt_self {S : Scheme.{0}} (a : S ⟶ Y) (ha : ⊤ ≤ a ⁻¹ᵁ (π ⁻¹ᵁ U)) (hz : ⊤ ≤ (a ≫ π) ⁻¹ᵁ U) :
    liftPt π U (a ≫ π) hz = a := by
  have e : IsOpenImmersion.lift (π ⁻¹ᵁ U).ι a (range_sub a _ ha) ≫ (π ⁻¹ᵁ U).ι = a := IsOpenImmersion.lift_fac _ _ _
  have e2 : IsOpenImmersion.lift U.ι (a ≫ π) (range_sub _ U hz) =
      IsOpenImmersion.lift (π ⁻¹ᵁ U).ι a (range_sub a _ ha) ≫ (π ∣_ U) := by
    symm
    apply IsOpenImmersion.lift_uniq
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, e]
  unfold liftPt
  rw [e2, Category.assoc, IsIso.hom_inv_id_assoc, e]

theorem liftPt_congr {S : Scheme.{0}} (z z' : S ⟶ Z) (e : z = z') (hz : ⊤ ≤ z ⁻¹ᵁ U) (hz' : ⊤ ≤ z' ⁻¹ᵁ U) :
    liftPt π U z hz = liftPt π U z' hz' := by
  subst e; rfl

theorem pt_mono {S : Scheme.{0}} (a b : S ⟶ Y) (ha : ⊤ ≤ a ⁻¹ᵁ (π ⁻¹ᵁ U)) (hb : ⊤ ≤ b ⁻¹ᵁ (π ⁻¹ᵁ U))
    (h : a ≫ π = b ≫ π) : a = b := by
  have hz : ⊤ ≤ (a ≫ π) ⁻¹ᵁ U := by rwa [Scheme.Hom.comp_preimage]
  have hz' : ⊤ ≤ (b ≫ π) ⁻¹ᵁ U := by rwa [Scheme.Hom.comp_preimage]
  rw [← liftPt_self π U a ha hz, ← liftPt_self π U b hb hz']
  exact liftPt_congr π U _ _ h hz hz'

variable (q : Z ⟶ Spec (CommRingCat.of K))

theorem inU_mono {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of K)) {V V' : X.Opens} (h : V ≤ V')
    (T : Thick (smFun X p)) : inU p V T → inU p V' T := fun hT x hx => h (hT hx)

def liftT (T : Thick (smFun Z q)) (hT : ⊤ ≤ CosieveSiteLaws.ptZ q T ⁻¹ᵁ U) : Thick (smFun Y (π ≫ q)) :=
  mkT (γ := dividedPowersBot K) (p := 0) (X := Y) (q := π ≫ q) (κ := Ideal.Quotient.mk ⊥) T.B T.i T.J T.δ T.adm T.compat
    ⟨((show PtOver Z q (Ideal.Quotient.mk (⊥ : Ideal K)) (T.B ⧸ T.J) from T.y).1.1, liftPt π U _ hT), by
      rw [← Category.assoc, liftPt_fac]
      exact (show PtOver Z q (Ideal.Quotient.mk (⊥ : Ideal K)) (T.B ⧸ T.J) from T.y).2⟩ T.w

theorem ptMap_id {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of K)) {B : Type} [CommRing B] (J : Ideal B) (h)
    (z : PtOver X p (Ideal.Quotient.mk (⊥ : Ideal K)) (B ⧸ J)) :
    (ptFun X p (Ideal.Quotient.mk (⊥ : Ideal K))).map (CommRingCat.ofHom (Ideal.quotientMap J (RingHom.id B) h)) z = z := by
  have hq : Ideal.quotientMap J (RingHom.id B) h = RingHom.id _ := by ext; rfl
  rw [hq, CommRingCat.ofHom_id, CategoryTheory.Functor.map_id]
  rfl

theorem comp_eq_id {X : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of K)} {T0 T1 : Thick (smFun X p)} (f : T0 ⟶ T1)
    (g : T1 ⟶ T0) (h : ∀ x, g.φ (f.φ x) = x) : f ≫ g = 𝟙 T0 :=
  Thick.Hom.ext (RingHom.ext h) (funext fun j => j.elim)

theorem liftT_y (T : Thick (smFun Z q)) (hT : ⊤ ≤ CosieveSiteLaws.ptZ q T ⁻¹ᵁ U) :
    ((smS π rfl).G.obj (liftT π U q T hT)).y = T.y :=
  Subtype.ext (Prod.ext rfl (liftPt_fac π U _ hT))

def liftHom (T : Thick (smFun Z q)) (hT : ⊤ ≤ CosieveSiteLaws.ptZ q T ⁻¹ᵁ U) :
    (smS π rfl).G.obj (liftT π U q T hT) ⟶ T :=
  mkH (γ := dividedPowersBot K) (p := 0) (X := Z) (q := q) (κ := Ideal.Quotient.mk ⊥)
    (T := (smS π rfl).G.obj (liftT π U q T hT)) (T' := T) (RingHom.id T.B) (fun _ => rfl)
    (DPMorphism.id T.δ).isDPMorphism (fun _ h => h) ((ptMap_id q T.J _ _).trans (liftT_y π U q T hT))

set_option maxHeartbeats 2000000 in

def liftInv (T : Thick (smFun Z q)) (hT : ⊤ ≤ CosieveSiteLaws.ptZ q T ⁻¹ᵁ U) :
    T ⟶ (smS π rfl).G.obj (liftT π U q T hT) :=
  mkH (γ := dividedPowersBot K) (p := 0) (X := Z) (q := q) (κ := Ideal.Quotient.mk ⊥)
    (T := T) (T' := (smS π rfl).G.obj (liftT π U q T hT))
    (RingHom.id T.B)
    (by exact fun _ => rfl)
    (by exact (DPMorphism.id T.δ).isDPMorphism)
    (by exact fun _ h => h)
    (by exact (ptMap_id q T.J _ _).trans (liftT_y π U q T hT).symm)

theorem liftHom_φ (T : Thick (smFun Z q)) (hT : ⊤ ≤ CosieveSiteLaws.ptZ q T ⁻¹ᵁ U) (x : T.B) :
    (liftHom π U q T hT).φ x = x := rfl

set_option maxHeartbeats 2000000 in
theorem liftInv_φ (T : Thick (smFun Z q)) (hT : ⊤ ≤ CosieveSiteLaws.ptZ q T ⁻¹ᵁ U) (x : T.B) :
    (liftInv π U q T hT).φ x = x := rfl

set_option maxHeartbeats 2000000 in

def liftIso (T : Thick (smFun Z q)) (hT : ⊤ ≤ CosieveSiteLaws.ptZ q T ⁻¹ᵁ U) :
    (smS π rfl).G.obj (liftT π U q T hT) ≅ T where
  hom := liftHom π U q T hT
  inv := liftInv π U q T hT
  hom_inv_id := comp_eq_id _ _ fun x => (congrArg _ (liftHom_φ π U q T hT x)).trans (liftInv_φ π U q T hT x)
  inv_hom_id := comp_eq_id _ _ fun x => (congrArg _ (liftInv_φ π U q T hT x)).trans (liftHom_φ π U q T hT x)

def pre {T T' : Thick (smFun Y (π ≫ q))} (hT : inU (π ≫ q) (π ⁻¹ᵁ U) T) (hT' : inU (π ≫ q) (π ⁻¹ᵁ U) T')
    (g : (smS π rfl).G.obj T ⟶ (smS π rfl).G.obj T') : T ⟶ T' :=
  mkH (γ := dividedPowersBot K) (p := 0) (X := Y) (q := π ≫ q) (κ := Ideal.Quotient.mk ⊥) (T := T) (T' := T')
    g.φ g.comm g.dp g.hle (by
      have e := g.pt
      have hh : CosieveSiteLaws.ptZ (π ≫ q) T' ≫ π = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J g.φ g.hle)) ≫
          (CosieveSiteLaws.ptZ (π ≫ q) T ≫ π) := CosieveSiteLaws.pt_hom q g
      refine Subtype.ext (Prod.ext ?_ ?_)
      · exact congrArg (fun z : (smFun Z q).Pt.obj (CommRingCat.of (T'.B ⧸ T'.J)) =>
          (show PtOver Z q (Ideal.Quotient.mk (⊥ : Ideal K)) (T'.B ⧸ T'.J) from z).1.1) e
      · refine pt_mono π U _ _ ?_ hT' ?_
        · change ⊤ ≤ CosieveSiteLaws.ptZ (π ≫ q) T ⁻¹ᵁ (π ⁻¹ᵁ U) at hT
          rw [top_le_iff] at hT ⊢
          change Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J g.φ g.hle)) ⁻¹ᵁ
            (CosieveSiteLaws.ptZ (π ≫ q) T ⁻¹ᵁ (π ⁻¹ᵁ U)) = ⊤
          rw [hT, Scheme.Hom.preimage_top]
        · change (Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J g.φ g.hle)) ≫ CosieveSiteLaws.ptZ (π ≫ q) T) ≫ π =
            CosieveSiteLaws.ptZ (π ≫ q) T' ≫ π
          rw [Category.assoc]
          exact hh.symm)

variable (V : Z.Opens) (hV : V ≤ U)

include hV in

theorem isEquiv (P : ObjectProperty (Thick (smFun Z q))) (P' : ObjectProperty (Thick (smFun Y (π ≫ q))))
    (hP : Cosieve P) (hPV : ∀ T, P T → inU q V T) (hP' : ∀ T, P' T → P ((smS π rfl).G.obj T))
    (hP'' : ∀ T, P ((smS π rfl).G.obj T) → P' T) :
    (P.lift (P'.ι ⋙ (smS π rfl).G) fun T => hP' _ T.property).IsEquivalence := by
  have hY : ∀ T, P' T → inU (π ≫ q) (π ⁻¹ᵁ U) T := fun T hT =>
    inU_mono (π ≫ q) (Scheme.Hom.preimage_mono π hV) T ((CosieveSiteLaws.inU_pull q π V T).2 (hPV _ (hP' T hT)))
  refine { faithful := ⟨fun {X X'} f f' hf => ?_⟩, full := ⟨fun {X X'} g => ?_⟩, essSurj := ⟨fun X => ?_⟩ }
  · apply ObjectProperty.hom_ext
    exact Thick.Hom.ext (congrArg (fun k => k.hom.φ) hf) (funext fun j => j.elim)
  · refine ⟨ObjectProperty.homMk (pre π U q (hY _ X.property) (hY _ X'.property) g.hom), ?_⟩
    apply ObjectProperty.hom_ext
    exact Thick.Hom.ext rfl (funext fun j => j.elim)
  · obtain ⟨T, hT⟩ := X
    have hTU : ⊤ ≤ CosieveSiteLaws.ptZ q T ⁻¹ᵁ U := inU_mono q hV T (hPV T hT)
    have hL : P' (liftT π U q T hTU) := hP'' _ (hP (liftIso π U q T hTU).inv hT)
    exact ⟨⟨liftT π U q T hTU, hL⟩, ⟨P.isoMk (liftIso π U q T hTU)⟩⟩

theorem tau_bij (a : ℕ) (T : Thick (smFun Y (π ≫ q))) : Function.Bijective ((morG π rfl a).τ T) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := congrArg Subtype.val hxy
    exact Subtype.ext this
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
    exact ⟨⟨Ideal.Quotient.mk _ z, Ideal.mem_map_of_mem _ hz⟩, rfl⟩

end Geo

end IsoBijectionLift

open IsoBijectionLift in
theorem isoBij_pf : IsoBij := by
  intro K _ Z Y q π U V hiso hV Q Q' hQ hQ' hQQ a h h' n
  have := hiso
  have hb : ∀ n, Function.Bijective ((morU (morG π rfl a) h).pull n) := by
    have : (morU (morG π rfl a) h).G.IsEquivalence :=
      isEquiv π U q V hV (inU q V) (inU (π ≫ q) (π ⁻¹ᵁ V)) (CosieveSiteLaws.inU_cosieve q V) (fun T hT => hT) h
        (fun T hT => (CosieveSiteLaws.inU_pull q π V T).2 hT)
    exact CrystallineSemistableComparison.P.adj_mor _ (fun T => tau_bij π q a T.obj)
  have hc : ∀ n, Function.Bijective ((morU (morG π rfl a) (U := inU q V ⊓ Q) (U' := inU (π ≫ q) (π ⁻¹ᵁ V) ⊓ Q')
      (fun T hT => ⟨h T hT.1, h' T hT.2⟩)).pull n) := by
    have : (morU (morG π rfl a) (U := inU q V ⊓ Q) (U' := inU (π ≫ q) (π ⁻¹ᵁ V) ⊓ Q')
        (fun T hT => ⟨h T hT.1, h' T hT.2⟩)).G.IsEquivalence :=
      isEquiv π U q V hV (inU q V ⊓ Q) (inU (π ≫ q) (π ⁻¹ᵁ V) ⊓ Q')
        (fun T T' f hT => ⟨CosieveSiteLaws.inU_cosieve q V f hT.1, hQ f hT.2⟩) (fun T hT => hT.1)
        (fun T hT => ⟨h T hT.1, h' T hT.2⟩)
        (fun T hT => ⟨(CosieveSiteLaws.inU_pull q π V T).2 hT.1, hQQ T hT.2⟩)
    exact CrystallineSemistableComparison.P.adj_mor _ (fun T => tau_bij π q a T.obj)
  exact rel_bij (morG π rfl a) hQ hQ' h h' hb hc n

end CrystallineSemistableComparison.Onto

end
