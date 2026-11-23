import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris
namespace GlobalTheory.CompanionTheory.ChartBijOf
open CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT

def incl {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (U : ObjectProperty C)
    {Q : ObjectProperty C} (hQ : Cosieve Q) : Cx.Hom (RC F U hQ) (CH.cx (U.ι ⋙ F)) (RingHom.id R) :=
  ⟨fun n => Submodule.subtype _, fun n x => rfl⟩

section Forms
variable {K : Type} [CommRing K] {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

theorem map_id_apply (v : Ω[A⁄K]) :
    letI : Algebra A A := (AlgHom.id K A).toRingHom.toAlgebra
    haveI : IsScalarTower K A A := IsScalarTower.of_algHom (AlgHom.id K A)
    KaehlerDifferential.map K K A A v = v := by
  have hv : v ∈ Submodule.span A (Set.range (KaehlerDifferential.D K A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    rw [KaehlerDifferential.map_D]
    rfl
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx =>
    exact ((KaehlerDifferential.map K K A A).map_smul c x).trans (congrArg (c • ·) hx)

theorem omMap_id (a : ℕ) (ω : Om K A a) : omMap (AlgHom.id K A) a ω = ω := by
  have hω : (ω : ⋀[A]^a Ω[A⁄K]) ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A a)) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    rw [GlobalTheory.CompanionTheory.SurjectionOntoH4.omMap_ιMulti]
    congr 1
    funext k
    exact map_id_apply (g k)
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [GlobalTheory.CompanionTheory.SurjectionOntoH4.omMap_smul, hx, AlgHom.id_apply]

theorem mem_of_map_eq (β : A ≃ₐ[K] B) {I : Ideal A} {J : Ideal B} (h : I.map β = J) (x : A) (hx : x ∈ I) : β x ∈ J := by
  rw [← h]
  exact Ideal.mem_map_of_mem β hx

theorem symm_mem_of_map_eq (β : A ≃ₐ[K] B) {I : Ideal A} {J : Ideal B} (h : I.map β = J) (x : B) (hx : x ∈ J) : β.symm x ∈ I := by
  rw [← h] at hx
  obtain ⟨z, hz, rfl⟩ := (Ideal.mem_map_iff_of_surjective β β.surjective).1 hx
  rwa [AlgEquiv.symm_apply_apply]

def relEquiv (β : A ≃ₐ[K] B) {I : Ideal A} {J : Ideal B} (h : I.map β = J) (a : ℕ) : relOm K I a ≃ₗ[K] relOm K J a :=
  LinearEquiv.ofLinear (GlobalTheory.CompanionTheory.SurjectionOntoH4.relMap (β : A →ₐ[K] B) (mem_of_map_eq β h) a)
    (GlobalTheory.CompanionTheory.SurjectionOntoH4.relMap (β.symm : B →ₐ[K] A) (symm_mem_of_map_eq β h) a)
    (LinearMap.ext fun ω => Subtype.ext (by
      change omMap (β : A →ₐ[K] B) a (omMap (β.symm : B →ₐ[K] A) a ω.1) = ω.1
      rw [GlobalTheory.CompanionTheory.SurjectionOntoH4.omMap_comp, show (β : A →ₐ[K] B).comp (β.symm : B →ₐ[K] A) = AlgHom.id K B from AlgHom.ext fun x => by simp,
        omMap_id]))
    (LinearMap.ext fun ω => Subtype.ext (by
      change omMap (β.symm : B →ₐ[K] A) a (omMap (β : A →ₐ[K] B) a ω.1) = ω.1
      rw [GlobalTheory.CompanionTheory.SurjectionOntoH4.omMap_comp, show (β.symm : B →ₐ[K] A).comp (β : A →ₐ[K] B) = AlgHom.id K A from AlgHom.ext fun x => by simp,
        omMap_id]))

theorem relEquiv_coe (β : A ≃ₐ[K] B) {I : Ideal A} {J : Ideal B} (h : I.map β = J) (a : ℕ) (ω : relOm K I a) :
    ((relEquiv β h a ω : relOm K J a) : Om K B a) = omMap (β : A →ₐ[K] B) a (ω : Om K A a) := rfl
end Forms

theorem rel_pm (hH : ChartFormsCechExact) (K : Type) [Field K] [CharZero K] (A : Type) [CommRing A] [Algebra K A] (n d : ℕ)
    (hd : 0 < d) (C : ChartRings K A n d) (a : ℕ) :
    ∃ (P : PM.{0} K (Fin d)) (e : ∀ S, P.M S ≃ₗ[K] relOm K (C.I S) a),
      (∀ (S T : Finset (Fin d)) (h : S ⊆ T) (y : P.M S),
        ((e T (P.res h y) : relOm K (C.I T) a) : Om K (C.R T) a) = omMap (C.res h) a ((e S y : relOm K (C.I S) a) : Om K (C.R S) a)) ∧
      P.Ex := by
  let P : PM.{0} K (Fin d) :=
    { M := fun S => relOm K (C.I S) a
      res := fun {S T} h => GlobalTheory.CompanionTheory.SurjectionOntoH4.relMap (C.res h) (GlobalTheory.CompanionTheory.SurjectionOntoH4.res_mem_I C h) a
      res_id := fun S h y => by
        apply Subtype.ext
        change omMap (C.res h) a y.1 = y.1
        rw [show C.res h = AlgHom.id K (C.R S) from AlgHom.ext fun z => C.res_id S h z, omMap_id]
      res_comp := fun {S T U} h h' y => by
        apply Subtype.ext
        change omMap (C.res h') a (omMap (C.res h) a y.1) = omMap (C.res _) a y.1
        rw [GlobalTheory.CompanionTheory.SurjectionOntoH4.omMap_comp, show (C.res h').comp (C.res h) = C.res (h.trans h') from
          AlgHom.ext fun z => C.res_comp h h' z] }
  have hc : ∀ (S T : Finset (Fin d)) (h : S ⊆ T) (y : P.M S),
      ((LinearEquiv.refl K (P.M T) (P.res h y) : relOm K (C.I T) a) : Om K (C.R T) a) =
        omMap (C.res h) a ((LinearEquiv.refl K (P.M S) y : relOm K (C.I S) a) : Om K (C.R S) a) :=
    fun S T h y => rfl
  exact ⟨P, fun S => LinearEquiv.refl K _, hc,
    hH K A n d hd C a P (fun S => LinearEquiv.refl K _) (fun h y => hc _ _ h y)⟩

theorem rel_iso (hR : AffRel) (K : Type) [Field K] [CharZero K] (W Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z)
    [IsClosedImmersion i] (hQ : Cosieve (On q i)) (V : Z.Opens) (d d' : ℕ) (c : Nonempty (Coord q V d))
    (c' : Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) d')) (a : ℕ) (e : Om K (Sec q V) a →ₗ[K] HV q V a a) (he : IsOm q V a e)
    (hb : Function.Bijective e) :
    (∀ j, j ≠ a → Subsingleton ((RC (G q a) (inU q V) hQ).H j)) ∧ Function.Injective ((incl (G q a) (inU q V) hQ).mapH a) ∧
    ∃ E : relOm K (show Ideal (Sec q V) from RingHom.ker (i.app V).hom) a ≃ₗ[K] (RC (G q a) (inU q V) hQ).H a,
      ∀ ω, (incl (G q a) (inU q V) hQ).mapH a (E ω) = e ω := by
  obtain ⟨hsub, hall⟩ := hR K W Z q i hQ V d d' c c' a
  obtain ⟨hinj, hrange⟩ := hall e he (incl (G q a) (inU q V) hQ) (fun n x => rfl)
  refine ⟨hsub, hinj, ?_⟩
  let eE : Om K (Sec q V) a ≃ₗ[K] HV q V a a := LinearEquiv.ofBijective e hb
  let ι := (incl (G q a) (inU q V) hQ).mapH a
  have hmem : ∀ x, eE.symm (ι x) ∈ relOm K (show Ideal (Sec q V) from RingHom.ker (i.app V).hom) a :=
    fun x => (hrange (eE.symm (ι x))).1 ⟨x, (eE.apply_symm_apply (ι x)).symm⟩
  let F : (RC (G q a) (inU q V) hQ).H a →ₗ[K]
      relOm K (show Ideal (Sec q V) from RingHom.ker (i.app V).hom) a :=
    LinearMap.codRestrict
      ((relOm K (show Ideal (Sec q V) from RingHom.ker (i.app V).hom) a).restrictScalars K)
      (eE.symm.toLinearMap ∘ₗ ι) hmem
  have hF : ∀ x, ((F x : relOm K (show Ideal (Sec q V) from RingHom.ker (i.app V).hom) a) :
      Om K (Sec q V) a) = eE.symm (ι x) := fun x => rfl
  have hFinj : Function.Injective F := by
    intro x y hxy
    have h1 : eE.symm (ι x) = eE.symm (ι y) := by rw [← hF, ← hF, hxy]
    exact hinj (eE.symm.injective h1)
  have hFsurj : Function.Surjective F := by
    intro ω
    obtain ⟨x, hx⟩ := (hrange ω.1).2 ω.2
    refine ⟨x, Subtype.ext ?_⟩
    rw [hF, hx]
    exact eE.symm_apply_apply ω.1
  refine ⟨(LinearEquiv.ofBijective F ⟨hFinj, hFsurj⟩).symm, fun ω => ?_⟩
  have h1 := (LinearEquiv.ofBijective F ⟨hFinj, hFsurj⟩).apply_symm_apply ω
  have h2 : eE.symm (ι ((LinearEquiv.ofBijective F ⟨hFinj, hFsurj⟩).symm ω)) = ω := by
    rw [← hF]
    exact congrArg Subtype.val h1
  exact (eE.apply_symm_apply _).symm.trans (congrArg eE h2)

section Abstract
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {Q : ObjectProperty C} (hQ : Cosieve Q)

def castH {U₀ U₁ : ObjectProperty C} (e : U₀ = U₁) (n : ℕ) : (RC F U₀ hQ).H n ≃ₗ[R] (RC F U₁ hQ).H n := by
  subst e; exact LinearEquiv.refl R _

theorem cast_res {U₀ U₁ U₀' U₁' : ObjectProperty C} (e : U₀ = U₁) (e' : U₀' = U₁') (h : U₀' ≤ U₀) (h' : U₁' ≤ U₁) (n : ℕ)
    (x : (RC F U₀ hQ).H n) :
    (RC.res F hQ h').mapH n (castH F hQ e n x) = castH F hQ e' n ((RC.res F hQ h).mapH n x) := by
  subst e
  subst e'
  rfl

theorem cast_res' {U₀ U₁ U : ObjectProperty C} (e : U₀ = U₁) (h : U₀ ≤ U) (h' : U₁ ≤ U) (n : ℕ)
    (x : (RC F U hQ).H n) :
    castH F hQ e n ((RC.res F hQ h).mapH n x) = (RC.res F hQ h').mapH n x := by
  subst e
  rfl

theorem res_res {U₀ U₁ U₂ : ObjectProperty C} (h : U₁ ≤ U₀) (h' : U₂ ≤ U₁) (h'' : U₂ ≤ U₀) (n : ℕ) (x : (RC F U₀ hQ).H n) :
    (RC.res F hQ h').mapH n ((RC.res F hQ h).mapH n x) = (RC.res F hQ h'').mapH n x := by
  induction x using Submodule.Quotient.induction_on with
  | _ z => rfl

theorem comp_mapH {X Y Z : Cx.{1} R} (f : Cx.Hom X Y (RingHom.id R)) (g : Cx.Hom Y Z (RingHom.id R)) (n : ℕ) (x : X.H n) :
    (f.comp g).mapH n x = g.mapH n (f.mapH n x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ z => rfl

theorem incl_res {U₀ U₁ : ObjectProperty C} (h : U₁ ≤ U₀) (n : ℕ) (x : (RC F U₀ hQ).H n) :
    (incl F U₁ hQ).mapH n ((RC.res F hQ h).mapH n x) = (resU F h).pull n ((incl F U₀ hQ).mapH n x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ z => rfl

end Abstract

section Geo
variable {K : Type} [Field K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {d : ℕ} {V : Z.Opens}

theorem inf_le_C (c : BChart q i π d V) {S : Finset (Fin d)} {k : Fin d} (hk : k ∈ S) : S.inf c.C ≤ c.C k := by
  exact Finset.inf_le hk

theorem inf_le_pre (c : BChart q i π d V) {S : Finset (Fin d)} (hS : S.Nonempty) : S.inf c.C ≤ π ⁻¹ᵁ V := by
  obtain ⟨k, hk⟩ := hS
  exact (Finset.inf_le hk).trans (c.C_le k)

theorem inter_eq_basicOpen (c : BChart q i π d V) (k : Fin d) (T : Finset (Fin d)) :
    c.C k ⊓ T.inf c.C = Y.basicOpen (∏ j ∈ T, c.u k j) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.inf_empty, inf_top_eq, Finset.prod_empty, Scheme.basicOpen_of_isUnit _ isUnit_one]
  | insert j T hj ih =>
    rw [Finset.inf_insert, Finset.prod_insert hj, Scheme.basicOpen_mul, ← ih, ← c.inter k j,
      inf_inf_distrib_left]

theorem inf_eq_basicOpen (c : BChart q i π d V) {S : Finset (Fin d)} {k : Fin d} (hk : k ∈ S) :
    S.inf c.C = Y.basicOpen (∏ j ∈ S, c.u k j) := by
  rw [← inter_eq_basicOpen c k S, inf_eq_right.2 (Finset.inf_le hk)]

theorem inf_affine (c : BChart q i π d V) {S : Finset (Fin d)} (hS : S.Nonempty) : IsAffineOpen (S.inf c.C) := by
  obtain ⟨k, hk⟩ := hS
  rw [inf_eq_basicOpen c hk]
  exact (c.C_aff k).basicOpen _
end Geo

section Main
theorem chart_ideal (hCL : ChartLaws) (K : Type) [Field K] (W Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z)
    [IsClosedImmersion i] (π : Y ⟶ Z) (d : ℕ) (V : Z.Opens) (c : BChart q i π d V) (C : ChartRings K (Sec q V) c.n d)
    (b : ∀ S : Finset (Fin d), S.Nonempty → (C.R S ≃ₐ[K] Sec (π ≫ q) (S.inf c.C)))
    (hb : ∀ (T : Finset (Fin d)) (hT : T.Nonempty) (g : Sec q V),
        b T hT (C.res (Finset.empty_subset T) (C.base.symm g)) = (π.appLE V (T.inf c.C) (inf_le_pre c hT)).hom g)
    (ht : ∀ j, C.t j = c.t j) :
    (∀ (S : Finset (Fin d)) (hS : S.Nonempty), (C.I S).map (b S hS) =
      (show Ideal (Sec (π ≫ q) (S.inf c.C)) from RingHom.ker ((pullback.snd i π).app (S.inf c.C)).hom)) ∧
    (C.I ∅).map C.base = (show Ideal (Sec q V) from RingHom.ker (i.app V).hom) := by
  refine ⟨fun S hS => ?_, ?_⟩
  · have hS' := hS
    obtain ⟨k, hk⟩ := hS'
    have hI : C.I S = Ideal.span {C.res (Finset.empty_subset S) (C.base.symm (C.t k))} := by
      apply le_antisymm
      · unfold ChartRings.I
        rw [Ideal.span_le]
        rintro _ ⟨j, -, rfl⟩
        rw [SetLike.mem_coe, C.t_eq S k hk j]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        unfold ChartRings.I
        exact Ideal.subset_span ⟨k, Or.inr hk, rfl⟩
    rw [hI, Ideal.map_span, Set.image_singleton, hb S hS (C.t k), ht k]
    exact ((hCL K W Z Y q i π d V c).2.2.2 k (S.inf c.C) (Finset.inf_le hk)
      (inf_affine c hS)).2.2.1.symm
  · have h2 : (C.I ∅).map C.base = Ideal.span (Set.range c.t) := by
      unfold ChartRings.I
      rw [Ideal.map_span]
      congr 1
      ext y
      constructor
      · rintro ⟨_, ⟨k, -, rfl⟩, rfl⟩
        exact ⟨k, by rw [C.res_id, AlgEquiv.apply_symm_apply, ht]⟩
      · rintro ⟨k, rfl⟩
        exact ⟨_, ⟨k, Or.inl rfl, rfl⟩, by rw [C.res_id, AlgEquiv.apply_symm_apply, ht]⟩
    rw [h2]
    exact c.ker.symm

theorem loc_iso (hA : AffOm) (hR : AffRel) (K : Type) [Field K] [CharZero K] (W Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K))
    (i : W ⟶ Z) [IsClosedImmersion i] (hQ : Cosieve (On q i)) (V : Z.Opens) (d d' : ℕ) (c : Nonempty (Coord q V d))
    (c' : Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) d')) (a : ℕ) {B : Type} [CommRing B] [Algebra K B] (I : Ideal B)
    (β : B ≃ₐ[K] Sec q V) (hI : I.map β = (show Ideal (Sec q V) from RingHom.ker (i.app V).hom))
    {M : Type} [AddCommGroup M] [Module K M] (eP : M ≃ₗ[K] relOm K I a) :
    ∃ e : Om K (Sec q V) a →ₗ[K] HV q V a a, IsOm q V a e ∧ (∀ j, j ≠ a → Subsingleton ((RC (G q a) (inU q V) hQ).H j)) ∧
      Function.Injective ((incl (G q a) (inU q V) hQ).mapH a) ∧
      ∃ E : M ≃ₗ[K] (RC (G q a) (inU q V) hQ).H a,
        ∀ y, (incl (G q a) (inU q V) hQ).mapH a (E y) = e (omMap (β : B →ₐ[K] Sec q V) a (eP y : Om K B a)) := by
  obtain ⟨-, e, he, hb⟩ := hA K Z q V d c a
  obtain ⟨hsub, hinj, E0, hE0⟩ := rel_iso hR K W Z q i hQ V d d' c c' a e he hb
  refine ⟨e, he, hsub, hinj, eP.trans ((relEquiv β hI a).trans E0), fun y => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hE0, relEquiv_coe]

theorem incl_pull {K : Type} [Field K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
    (a : ℕ) (hQ : Cosieve (On q i)) (hQ' : Cosieve (On (π ≫ q) (pullback.snd i π))) (V : Z.Opens)
    (D₀ D : Y.Opens) (hD : inU (π ≫ q) D ≤ inU (π ≫ q) D₀)
    (h : ∀ T, inU (π ≫ q) D₀ T → inU q V ((smS π rfl).G.obj T)) (h₁ : ∀ T, inU (π ≫ q) D T → inU q V ((smS π rfl).G.obj T))
    (h' : ∀ T, On (π ≫ q) (pullback.snd i π) T → On q i ((smS π rfl).G.obj T)) (x : (RC (G q a) (inU q V) hQ).H a) :
    (incl (G (π ≫ q) a) (inU (π ≫ q) D) hQ').mapH a ((RC.res (G (π ≫ q) a) hQ' hD).mapH a
      ((pullRC π rfl a (U := inU q V) (U' := inU (π ≫ q) D₀) hQ hQ' h h').mapH a x)) =
    (morV π rfl a h₁).pull a ((incl (G q a) (inU q V) hQ).mapH a x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ z => rfl

end Main

end GlobalTheory.CompanionTheory.ChartBijOf
