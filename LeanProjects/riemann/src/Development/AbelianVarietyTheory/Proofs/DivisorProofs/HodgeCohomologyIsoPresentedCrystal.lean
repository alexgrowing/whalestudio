import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open Opposite

namespace GlobalTheory.LiftSys.Coh

theorem surjective_spMap_of_sq {A A₀ : Type} [CommRing A] [CommRing A₀] (f : A →+* A₀)
    (hf : Function.Surjective f) (hk : ∀ a, f a = 0 → a ^ 2 = 0) : Surjective (spMap f) := by
  refine ⟨fun (x : PrimeSpectrum A) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap f) := by
    rw [range_comap_of_surjective _ _ hf]
    intro a ha
    apply x.isPrime.mem_of_pow_mem 2
    rw [hk a ha]
    exact zero_mem _
  exact this

theorem ringHom_eq_of_spMap {A B : Type} [CommRing A] [CommRing B] {Y : Scheme.{0}} (z : Sp A ⟶ Y) [Mono z]
    {g g' : A →+* B} (h : spMap g ≫ z = spMap g' ≫ z) : g = g' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono z).1 h))

instance isOpenImmersion_affPt {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (V : X.affineOpens) :
    IsOpenImmersion (affPt s V) :=
  IsAffineOpen.isOpenImmersion_fromSpec V.2

theorem range_affPt {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (V : X.affineOpens) :
    Set.range (affPt s V) = V.1 :=
  V.2.range_fromSpec

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀} {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X}

def W (P : S.Presents s i) (U : AffOp X₀) : X.affineOpens :=
  haveI := P.isOpen U
  ⟨(P.y U).opensRange, isAffineOpen_opensRange _⟩

theorem range_y (P : S.Presents s i) (U : AffOp X₀) : Set.range (P.y U) = (W P U).1 := by
  haveI := P.isOpen U
  exact (Scheme.Hom.coe_opensRange _).symm

theorem y_apply_red (P : S.Presents s i) (U : AffOp X₀) (z : Sp (Sec s₀ U.unop.1)) :
    P.y U (spMap (S.p U) z) = i (affPt s₀ U.unop z) := by
  have e := congrArg (fun f : Sp (Sec s₀ U.unop.1) ⟶ X ↦ f z) (P.red U)
  simpa only [Scheme.Hom.comp_apply] using e

theorem mem_W (P : S.Presents s i) (U : AffOp X₀) {x : X₀} (hx : x ∈ U.unop.1) : i x ∈ (W P U).1 := by
  rw [← SetLike.mem_coe, ← range_y]
  rw [← SetLike.mem_coe, ← range_affPt s₀] at hx
  obtain ⟨z, rfl⟩ := hx
  exact ⟨_, y_apply_red P U z⟩

theorem exists_mem_affineOpen_of_mem_liftSystemChartImage (hI : I ^ 2 = 0) (P : S.Presents s i) (U : AffOp X₀) {w : X} (hw : w ∈ (W P U).1) :
    ∃ x ∈ U.unop.1, i x = w := by
  rw [← SetLike.mem_coe, ← range_y] at hw
  obtain ⟨t, rfl⟩ := hw
  have hs := (surjective_spMap_of_sq (S.p U) (S.surj U) fun b hb ↦ by
    have hb' : b ∈ I.map (algebraMap R (S.F.obj U)) := (S.ker U b).1 hb
    have h2 : b ^ 2 ∈ I.map (algebraMap R (S.F.obj U)) ^ 2 := Ideal.pow_mem_pow hb' 2
    rwa [map_sq hI] at h2).surj
  obtain ⟨z, rfl⟩ := hs t
  refine ⟨affPt s₀ U.unop z, ?_, (y_apply_red P U z).symm⟩
  rw [← SetLike.mem_coe, ← range_affPt s₀]
  exact ⟨z, rfl⟩

theorem W_le (P : S.Presents s i) {U V : AffOp X₀} (a : U ⟶ V) : W P V ≤ W P U := by
  change (W P V).1 ≤ (W P U).1
  rw [← SetLike.coe_subset_coe, ← range_y, ← range_y, ← P.nat a]
  rintro _ ⟨z, rfl⟩
  exact ⟨_, (Scheme.Hom.comp_apply _ _ z).symm⟩

end GlobalTheory.LiftSys.Coh

namespace GlobalTheory.LiftSys.Coh

open Opposite

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀} {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X}

def toW (P : S.Presents s i) (U : AffOp X₀) : Sp (S.F.obj U) ⟶ Sp (Sec s (W P U).1) :=
  IsOpenImmersion.lift (affPt s (W P U)) (P.y U) (by rw [range_affPt, range_y])

def ofW (P : S.Presents s i) (U : AffOp X₀) : Sp (Sec s (W P U).1) ⟶ Sp (S.F.obj U) :=
  haveI := P.isOpen U
  IsOpenImmersion.lift (P.y U) (affPt s (W P U)) (by rw [range_affPt, range_y])

def fwd (P : S.Presents s i) (U : AffOp X₀) : Sec s (W P U).1 →+* S.F.obj U := (Spec.preimage (toW P U)).hom

def bwd (P : S.Presents s i) (U : AffOp X₀) : S.F.obj U →+* Sec s (W P U).1 := (Spec.preimage (ofW P U)).hom

theorem spMap_fwd (P : S.Presents s i) (U : AffOp X₀) : spMap (fwd P U) ≫ affPt s (W P U) = P.y U := by
  change Spec.map (Spec.preimage (toW P U)) ≫ _ = _
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

theorem spMap_bwd (P : S.Presents s i) (U : AffOp X₀) : spMap (bwd P U) ≫ P.y U = affPt s (W P U) := by
  haveI := P.isOpen U
  change Spec.map (Spec.preimage (ofW P U)) ≫ _ = _
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

theorem fwd_bwd (P : S.Presents s i) (U : AffOp X₀) : (fwd P U).comp (bwd P U) = RingHom.id _ := by
  haveI := P.isOpen U
  refine ringHom_eq_of_spMap (P.y U) ?_
  rw [Cris.spMap_comp, Category.assoc, spMap_bwd, spMap_fwd, Cris.spMap_id, Category.id_comp]

theorem bwd_fwd (P : S.Presents s i) (U : AffOp X₀) : (bwd P U).comp (fwd P U) = RingHom.id _ := by
  refine ringHom_eq_of_spMap (affPt s (W P U)) ?_
  rw [Cris.spMap_comp, Category.assoc, spMap_fwd, spMap_bwd, Cris.spMap_id, Category.id_comp]

theorem fwd_algebraMap (P : S.Presents s i) (U : AffOp X₀) :
    (fwd P U).comp (algebraMap R (Sec s (W P U).1)) = algebraMap R (S.F.obj U) := by
  have h : spMap ((fwd P U).comp (algebraMap R (Sec s (W P U).1))) = spMap (algebraMap R (S.F.obj U)) := by
    rw [Cris.spMap_comp, ← affPt_w, ← Category.assoc, spMap_fwd, P.base]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

def e (P : S.Presents s i) (U : AffOp X₀) : Sec s (W P U).1 ≃ₐ[R] S.F.obj U :=
  { fwd P U with
    invFun := bwd P U
    left_inv := fun b ↦ RingHom.congr_fun (bwd_fwd P U) b
    right_inv := fun b ↦ RingHom.congr_fun (fwd_bwd P U) b
    commutes' := fun r ↦ RingHom.congr_fun (fwd_algebraMap P U) r }

theorem e_apply (P : S.Presents s i) (U : AffOp X₀) (b : Sec s (W P U).1) : e P U b = fwd P U b := rfl

theorem e_res (P : S.Presents s i) {U V : AffOp X₀} (a : U ⟶ V) (b : Sec s (W P U).1) :
    e P V (Sec.res s (W_le P a) b) = mp S.F a (e P U b) := by
  have : (fwd P V).comp (Sec.res s (W_le P a) : Sec s (W P U).1 →+* Sec s (W P V).1) =
      (mp S.F a : S.F.obj U →+* S.F.obj V).comp (fwd P U) := by
    refine ringHom_eq_of_spMap (affPt s (W P U)) ?_
    rw [Cris.spMap_comp, Cris.spMap_comp, Category.assoc, Category.assoc, affPt_res, spMap_fwd, spMap_fwd, P.nat a]
  rw [e_apply, e_apply]
  exact RingHom.congr_fun this b

end GlobalTheory.LiftSys.Coh

namespace GlobalTheory.LiftSys.Coh

open Opposite

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀} {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X}

def imgF (P : S.Presents s i) : AffOp X₀ ⥤ AffOp X :=
  (Monotone.functor (f := fun U : X₀.affineOpens ↦ W P (op U)) fun _ _ h ↦ W_le P (homOfLE h).op).op

def toSys (P : S.Presents s i) : CoefMap (RingHom.id R) (OAff s) S.F where
  G := imgF P
  α U := ((e P U : Sec s (W P U).1 →ₐ[R] S.F.obj U) : Sec s (W P U).1 →+* S.F.obj U)
  naturality a b := e_res P a b
  smul U r b := map_smul (e P U) r b

def pre (i : X₀ ⟶ X) [IsAffineHom i] (V : X.affineOpens) : X₀.affineOpens := ⟨i ⁻¹ᵁ V.1, V.2.preimage i⟩

theorem pre_mono (i : X₀ ⟶ X) [IsAffineHom i] {V V' : X.affineOpens} (h : V ≤ V') : pre i V ≤ pre i V' :=
  fun x hx ↦ show i x ∈ V'.1 from Subtype.coe_le_coe.2 h hx

def preF (i : X₀ ⟶ X) [IsAffineHom i] : AffOp X ⥤ AffOp X₀ :=
  (Monotone.functor (f := pre i) fun _ _ h ↦ pre_mono i h).op

theorem le_W_pre [IsAffineHom i] (P : S.Presents s i) (hi : Function.Surjective i) (V : X.affineOpens) :
    V ≤ W P (op (pre i V)) := by
  intro x hx
  obtain ⟨x₀, rfl⟩ := hi x
  exact mem_W P (op (pre i V)) hx

def back [IsAffineHom i] (P : S.Presents s i) (hi : Function.Surjective i) (V : X.affineOpens) :
    S.F.obj (op (pre i V)) →ₐ[R] Sec s V.1 :=
  (Sec.res s (le_W_pre P hi V)).comp (e P (op (pre i V))).symm.toAlgHom

theorem back_e [IsAffineHom i] (P : S.Presents s i) (hi : Function.Surjective i) (V : X.affineOpens)
    (c : Sec s (W P (op (pre i V))).1) : back P hi V (e P _ c) = Sec.res s (le_W_pre P hi V) c := by
  simp [back]

theorem back_naturality [IsAffineHom i] (P : S.Presents s i) (hi : Function.Surjective i) {V V' : X.affineOpens}
    (h : V' ≤ V) (b : S.F.obj (op (pre i V))) :
    back P hi V' (mp S.F (homOfLE (pre_mono i h)).op b) = Sec.res s h (back P hi V b) := by
  obtain ⟨c, rfl⟩ := (e P (op (pre i V))).surjective b
  rw [← e_res P (homOfLE (pre_mono i h)).op c, back_e, back_e, ← Sec.res_res, ← Sec.res_res]

def ofSys [IsAffineHom i] (P : S.Presents s i) (hi : Function.Surjective i) :
    CoefMap (RingHom.id R) S.F (OAff s) where
  G := preF i
  α V := (back P hi V.unop : S.F.obj (op (pre i V.unop)) →+* Sec s V.unop.1)
  naturality a b := back_naturality P hi (leOfHom a.unop) b
  smul V r b := map_smul (back P hi V.unop) r b

theorem ofSys_toSys [IsAffineHom i] (P : S.Presents s i) (hi : Function.Surjective i) (c : HO1 s) :
    (ofSys P hi).pull1 ((toSys P).pull1 c) = c := by
  rw [← CoefMap.pullCohomologyOne_comp]
  refine ((toSys P).comp (ofSys P hi)).pullCohomologyOne_eq_of_natTrans (CoefMap.id _)
    { app := fun V ↦ (homOfLE (le_W_pre P hi V.unop)).op, naturality := fun _ _ _ ↦ rfl }
    (fun V b ↦ (back_e P hi V.unop b).symm) c |>.trans (CoefMap.pullCohomologyOne_id c)

theorem toSys_ofSys [IsAffineHom i] (P : S.Presents s i) (hi : Function.Surjective i) (c : CatCoh.H1 S.F) :
    (toSys P).pull1 ((ofSys P hi).pull1 c) = c := by
  rw [← CoefMap.pullCohomologyOne_comp]
  refine ((ofSys P hi).comp (toSys P)).pullCohomologyOne_eq_of_natTrans (CoefMap.id _)
    { app := fun U ↦ (homOfLE (show U.unop ≤ pre i (W P U) from fun _ hx ↦ mem_W P U hx)).op,
      naturality := fun _ _ _ ↦ rfl } (fun U b ↦ ?_) c |>.trans (CoefMap.pullCohomologyOne_id c)
  obtain ⟨c, rfl⟩ := (e P (op (pre i (W P U)))).surjective b
  exact (e_res P _ c).symm.trans (congrArg (e P U) (back_e P hi (W P U) c).symm)

end GlobalTheory.LiftSys.Coh

namespace GlobalTheory.LiftSys.Coh

open Opposite

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀} {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X}

theorem W_le_snd (hI : I ^ 2 = 0) (P : S.Presents s i) (p : Pair i) : W P (op p.1.1) ≤ p.1.2 := by
  intro w hw
  obtain ⟨x, hx, rfl⟩ := exists_mem_affineOpen_of_mem_liftSystemChartImage hI P (op p.1.1) hw
  exact p.2 hx

theorem p_e_res (P : S.Presents s i) (p : Pair i) (hle : W P (op p.1.1) ≤ p.1.2) (b : Sec s p.1.2.1) :
    S.p (op p.1.1) (e P (op p.1.1) (Sec.res s hle b)) = GlobalTheory.CechDR.secPull s s₀ p b := by
  have : (S.p (op p.1.1)).comp ((fwd P (op p.1.1)).comp (Sec.res s hle : Sec s p.1.2.1 →+* Sec s (W P (op p.1.1)).1)) =
      GlobalTheory.CechDR.secPull s s₀ p := by
    refine ringHom_eq_of_spMap (affPt s p.1.2) ?_
    rw [Cris.spMap_comp, Cris.spMap_comp, Category.assoc, Category.assoc, affPt_res, spMap_fwd, P.red,
      GlobalTheory.CechDR.secPull_affPt]
  exact RingHom.congr_fun this b

end GlobalTheory.LiftSys.Coh

open Opposite in

theorem GlobalTheory.LiftSys.cohomology_presents : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (h : IsPullback i s₀ s (spMap π)), S.Presents s i → ∃ e : HO1 s ≃ₗ[R] GlobalTheory.CatCoh.H1 S.F, (∀ (m : IsMor (dp0 R) s (divided₂ hI) (s₀ ≫ spMap π) (RingHom.id R) i) (c : FirstDeRham s), e (toHO1 s (cmp1 s c)) = S.r hI (m.pull1 c)) ∧ ∀ c : HO1 s, IsPullO h.w c (S.redO.pull1 (e c)) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S X s i h P
  haveI : IsClosedImmersion i :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip (IsClosedImmersion.spec_of_surjective _ hπ)
  have hsurj : Surjective i := MorphismProperty.of_isPullback (P := @Surjective) h.flip
    (Coh.surjective_spMap_of_sq π hπ fun a ha ↦ by
      have ha' : a ∈ I := hk ▸ RingHom.mem_ker.2 ha
      have h2 : a ^ 2 ∈ I ^ 2 := Ideal.pow_mem_pow ha' 2
      rw [hI, Ideal.zero_eq_bot, Ideal.mem_bot] at h2
      exact h2)
  refine ⟨LinearEquiv.ofLinear (Coh.toSys P).pull1 (Coh.ofSys P hsurj.surj).pull1
    (LinearMap.ext fun c ↦ Coh.toSys_ofSys P hsurj.surj c) (LinearMap.ext fun c ↦ Coh.ofSys_toSys P hsurj.surj c),
    fun m c ↦ ?_, fun c ↦ ?_⟩
  · rw [LinearEquiv.ofLinear_apply, structureSheaf_comparison_comm, cmpO, toH1O, Sys.r, IsMor.pull1, ← CoefMap.pullCohomologyOne_comp,
      ← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    refine CoefMap.pullCohomologyOne_eq_of_natTrans _ _
      { app := fun U ↦ Thick.trivHom (T := m.obj (S.thickObj hI U))
          { Coh.fwd P U with commutes' := fun r ↦ RingHom.congr_fun (Coh.fwd_algebraMap P U) r } (by
            change spMap ((S.p U).comp (Coh.fwd P U)) ≫ affPt s (Coh.W P U) = affPt s₀ U.unop ≫ i
            rw [Cris.spMap_comp, Category.assoc, Coh.spMap_fwd, P.red])
        naturality := fun U U' a ↦ Thick.hom_ext fun b ↦ Coh.e_res P a b } (fun _ _ ↦ rfl) c
  · rw [LinearEquiv.ofLinear_apply]
    unfold IsPullO
    rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _
      { app := fun p ↦ (homOfLE (Coh.W_le_snd hI P p.unop)).op, naturality := fun _ _ _ ↦ rfl }
      (fun p b ↦ Coh.p_e_res P p.unop _ b) c
