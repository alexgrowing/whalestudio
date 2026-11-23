import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA

namespace GlobalTheory.PDForm

def qmap {B B' M M' : Type} [Ring B] [Ring B'] [AddCommGroup M] [AddCommGroup M'] [Module B M] [Module B' M']
    (p : Submodule B M) (q : Submodule B' M') (f : M →+ M') (h : ∀ x ∈ p, f x ∈ q) : M ⧸ p →+ M' ⧸ q :=
  QuotientAddGroup.map p.toAddSubgroup q.toAddSubgroup f h

section Ring

variable (R : Type) [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

def rel : Ideal (DR R B) :=
  Ideal.span {x | ∃ n : ℕ, ∃ a ∈ J, x = ι1 (D R B (δ.dpow (n + 1) a) - δ.dpow n a • D R B a)}

private theorem dDR_dpow_succ_sub_smul_mem_rel (n : ℕ) {a : B} (ha : a ∈ J) :
    dDR R B (ι1 (D R B (δ.dpow (n + 1) a) - δ.dpow n a • D R B a)) ∈ rel R δ := by
  have key : ι1 (D R B (δ.dpow n a)) * ι1 (D R B a) ∈ rel R δ := by
    rcases n with _ | m
    · rw [δ.dpow_zero ha, Derivation.map_one_eq_zero, map_zero, zero_mul]
      exact Ideal.zero_mem _
    · have hg : ι1 (D R B (δ.dpow (m + 1) a) - δ.dpow m a • D R B a) ∈ rel R δ :=
        Ideal.subset_span ⟨m, a, ha, rfl⟩
      have e : ι1 (D R B (δ.dpow (m + 1) a)) =
          ι1 (D R B (δ.dpow (m + 1) a) - δ.dpow m a • D R B a) + δ.dpow m a • ι1 (D R B a) := by
        rw [map_sub, map_smul, sub_add_cancel]
      rw [e, add_mul, smul_mul_assoc, ExteriorAlgebra.ι_sq_zero, smul_zero, add_zero, ι_mul_ι_swap,
        ← neg_mul]
      exact Ideal.mul_mem_left _ _ hg
  rw [map_sub, map_sub, map_smul, dDR_D, dDR_smul, dDR_D, smul_zero, add_zero, zero_sub]
  exact neg_mem key

theorem dDR_mem_rel {x : DR R B} (hx : x ∈ rel R δ) : dDR R B x ∈ rel R δ := by
  refine Submodule.span_induction (p := fun y _ ↦ dDR R B y ∈ rel R δ) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨n, a, ha, rfl⟩
    exact dDR_dpow_succ_sub_smul_mem_rel R δ n ha
  · rw [map_zero]
    exact Ideal.zero_mem _
  · intro y z _ _ hy hz
    rw [map_add]
    exact Ideal.add_mem _ hy hz
  · intro c y hy' hy
    rw [smul_eq_mul, dDR_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hy')

def N1 : Submodule B Ω[B⁄R] := ((rel R δ).restrictScalars B).comap ι1

def N (j : ℕ) : Submodule B (Om R B j) := ((rel R δ).restrictScalars B).comap (⋀[B]^j Ω[B⁄R]).subtype

abbrev K1 : Type := Ω[B⁄R] ⧸ N1 R δ

abbrev K (j : ℕ) : Type := Om R B j ⧸ N R δ j

def kd0 : B →+ K1 R δ := (N1 R δ).mkQ.toAddMonoidHom.comp (D R B).toLinearMap.toAddMonoidHom

def kd1 : K1 R δ →+ K R δ 2 := qmap _ _ (dOne R B).toAddMonoidHom fun _ h ↦ dDR_mem_rel R δ h

def kd2 : K R δ 2 →+ K R δ 3 := qmap _ _ (dTwo R B).toAddMonoidHom fun _ h ↦ dDR_mem_rel R δ h

variable {R δ} {R' B' : Type} [CommRing R'] [CommRing B'] [Algebra R' B'] {J' : Ideal B'} {δ' : DividedPowers J'}
  {σ : R →+* R'} {α : B →+* B'} (h : SemiHom σ α) (hd : IsDPMorphism δ δ' α)

include hd in

theorem mDR_mem_rel {x : DR R B} (hx : x ∈ rel R δ) : h.mDR x ∈ rel R' δ' := by
  refine Submodule.span_induction (p := fun y _ ↦ h.mDR y ∈ rel R' δ') ?_ ?_ ?_ ?_ hx
  · rintro y ⟨n, a, ha, rfl⟩
    have ha' : α a ∈ J' := hd.ideal_comp (Ideal.mem_map_of_mem α ha)
    refine Ideal.subset_span ⟨n, α a, ha', ?_⟩
    rw [SemiHom.mDR_ι, map_sub, SemiHom.m1_D, SemiHom.oneFormMap_smul_semilinear, SemiHom.m1_D, hd.dpow_comp a ha,
      hd.dpow_comp a ha]
  · rw [map_zero]
    exact Ideal.zero_mem _
  · intro y z _ _ hy hz
    rw [map_add]
    exact Ideal.add_mem _ hy hz
  · intro c y _ hy
    rw [smul_eq_mul, map_mul]
    exact Ideal.mul_mem_left _ _ hy

def km1 : K1 R δ →+ K1 R' δ' := qmap _ _ h.m1.toAddMonoidHom fun x hx ↦ by
  change ι1 (h.m1 x) ∈ rel R' δ'
  rw [← h.mDR_ι]
  exact mDR_mem_rel h hd hx

def km (j : ℕ) : K R δ j →+ K R' δ' j := qmap _ _ (h.mOm j).toAddMonoidHom fun _ hx ↦ mDR_mem_rel h hd hx

theorem divPowerCompatOneFormMap_mk (x : Ω[B⁄R]) : km1 h hd (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h.m1 x) := rfl

theorem km_mk (j : ℕ) (x : Om R B j) : km h hd j (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h.mOm j x) := rfl

theorem divPowerCompatFunctionDifferential_apply (b : B) : kd0 R δ b = Submodule.Quotient.mk (D R B b) := rfl

theorem divPowerCompatOneFormDerivative_mk (x : Ω[B⁄R]) : kd1 R δ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (dOne R B x) := rfl

theorem divPowerCompatTwoFormDerivative_mk (x : Om R B 2) : kd2 R δ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (dTwo R B x) := rfl

theorem divPowerCompatOneFormMap_functionDifferential (x : B) : km1 h hd (kd0 R δ x) = kd0 R' δ' (α x) := by
  rw [divPowerCompatFunctionDifferential_apply, divPowerCompatFunctionDifferential_apply, divPowerCompatOneFormMap_mk, SemiHom.m1_D]

theorem divPowerCompatFormMap_oneFormDerivative (x : K1 R δ) : km h hd 2 (kd1 R δ x) = kd1 R' δ' (km1 h hd x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [divPowerCompatOneFormDerivative_mk, km_mk, divPowerCompatOneFormMap_mk, divPowerCompatOneFormDerivative_mk, SemiHom.mOm_dOne]

theorem divPowerCompatFormMap_twoFormDerivative (x : K R δ 2) : km h hd 3 (kd2 R δ x) = kd2 R' δ' (km h hd 2 x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [divPowerCompatTwoFormDerivative_mk, km_mk, km_mk, divPowerCompatTwoFormDerivative_mk, SemiHom.mOm_dTwo]

theorem divPowerCompatOneFormDerivative_comp_differential (x : B) : kd1 R δ (kd0 R δ x) = 0 := by
  rw [divPowerCompatFunctionDifferential_apply, divPowerCompatOneFormDerivative_mk, dOne_D, Submodule.Quotient.mk_zero]

theorem divPowerCompatTwoFormDerivative_comp_oneForm (x : K1 R δ) : kd2 R δ (kd1 R δ x) = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [divPowerCompatOneFormDerivative_mk, divPowerCompatTwoFormDerivative_mk, dTwo_dOne, Submodule.Quotient.mk_zero]

theorem divPowerCompatOneFormMap_id {τ : R →+* R} {β : B →+* B} (h : SemiHom τ β) (hd : IsDPMorphism δ δ β) (e : ∀ b, β b = b)
    (x : K1 R δ) : km1 h hd x = x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [divPowerCompatOneFormMap_mk, h.oneFormMap_eq_self_of_id e]

theorem km_id {τ : R →+* R} {β : B →+* B} (h : SemiHom τ β) (hd : IsDPMorphism δ δ β) (e : ∀ b, β b = b)
    (j : ℕ) (x : K R δ j) : km h hd j x = x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [km_mk, h.mOm_id e]

section Comp

variable {R'' B'' : Type} [CommRing R''] [CommRing B''] [Algebra R'' B''] {J'' : Ideal B''}
  {δ'' : DividedPowers J''} {τ : R' →+* R''} {β : B' →+* B''} {ρ : R →+* R''} {γ : B →+* B''}
  (h' : SemiHom τ β) (hd' : IsDPMorphism δ' δ'' β) (h'' : SemiHom ρ γ) (hd'' : IsDPMorphism δ δ'' γ)

theorem divPowerCompatOneFormMap_comp (e : ∀ b, β (α b) = γ b) (x : K1 R δ) : km1 h' hd' (km1 h hd x) = km1 h'' hd'' x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, h.oneFormMap_comp_oneFormMap h' h'' e]

theorem km_km (e : ∀ b, β (α b) = γ b) (j : ℕ) (x : K R δ j) : km h' hd' j (km h hd j x) = km h'' hd'' j x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [km_mk, km_mk, km_mk, h.mOm_mOm h' h'' e]

end Comp

def RQ : Prop := IsQ (kd0 R δ) (kd1 R δ) (kd2 R δ) (kd0 R' δ') (kd1 R' δ') (kd2 R' δ') α.toAddMonoidHom
  (km1 h hd) (km h hd 2)

def ctr (v : Derivation R B B) : DR R B →ₗ[B] DR R B := CliffordAlgebra.contractLeft v.liftKaehlerDifferential

def lie (v : Derivation R B B) : DR R B →ₗ[R] DR R B :=
  dDR R B ∘ₗ (ctr v).restrictScalars R + (ctr v).restrictScalars R ∘ₗ dDR R B

def hot (v : Derivation R B B) (e : ℕ → B) (n : ℕ) (x : DR R B) : DR R B :=
  ∑ k ∈ Finset.range n, ((-1) ^ k * e (k + 1)) • (lie v ^ k) (ctr v x)

variable (R δ) in

def filDR (n : ℕ) : Ideal (DR R B) := Ideal.span (algebraMap B (DR R B) '' fil δ n) ⊔ rel R δ

end Ring

section Site

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'} {X X' : Scheme.{0}}

@[reducible] def KK (κ : DividedPowers I) (t : X ⟶ Sp R) : Cx (Thick κ t) where
  M0 := Coef.ofAlg (O κ t)
  M1 := ⟨fun T ↦ K1 R T.δ, fun φ ↦ km1 (SemiHom.of_algHom φ.φ) φ.dp,
    fun T x ↦ divPowerCompatOneFormMap_id (SemiHom.of_algHom (Thick.Hom.φ (𝟙 T))) (Thick.Hom.dp (𝟙 T)) (fun _ ↦ rfl) x,
    fun φ ψ x ↦ (divPowerCompatOneFormMap_comp (SemiHom.of_algHom φ.φ) φ.dp (SemiHom.of_algHom ψ.φ) ψ.dp (SemiHom.of_algHom (φ ≫ ψ).φ) (φ ≫ ψ).dp (fun _ ↦ rfl) x).symm⟩
  M2 := ⟨fun T ↦ K R T.δ 2, fun φ ↦ km (SemiHom.of_algHom φ.φ) φ.dp 2,
    fun T x ↦ km_id (SemiHom.of_algHom (Thick.Hom.φ (𝟙 T))) (Thick.Hom.dp (𝟙 T)) (fun _ ↦ rfl) 2 x,
    fun φ ψ x ↦ (km_km (SemiHom.of_algHom φ.φ) φ.dp (SemiHom.of_algHom ψ.φ) ψ.dp (SemiHom.of_algHom (φ ≫ ψ).φ) (φ ≫ ψ).dp (fun _ ↦ rfl) 2 x).symm⟩
  M3 := ⟨fun T ↦ K R T.δ 3, fun φ ↦ km (SemiHom.of_algHom φ.φ) φ.dp 3,
    fun T x ↦ km_id (SemiHom.of_algHom (Thick.Hom.φ (𝟙 T))) (Thick.Hom.dp (𝟙 T)) (fun _ ↦ rfl) 3 x,
    fun φ ψ x ↦ (km_km (SemiHom.of_algHom φ.φ) φ.dp (SemiHom.of_algHom ψ.φ) ψ.dp (SemiHom.of_algHom (φ ≫ ψ).φ) (φ ≫ ψ).dp (fun _ ↦ rfl) 3 x).symm⟩
  d0 T := kd0 R T.δ
  d1 T := kd1 R T.δ
  d2 T := kd2 R T.δ
  diffZero_natural φ x := (divPowerCompatOneFormMap_functionDifferential (SemiHom.of_algHom φ.φ) φ.dp x).symm
  diffOne_natural φ x := (divPowerCompatFormMap_oneFormDerivative (SemiHom.of_algHom φ.φ) φ.dp x).symm
  diffTwo_natural φ x := (divPowerCompatFormMap_twoFormDerivative (SemiHom.of_algHom φ.φ) φ.dp x).symm
  diffOne_diffZero _ x := divPowerCompatOneFormDerivative_comp_differential x
  diffTwo_comp_diffOne _ x := divPowerCompatTwoFormDerivative_comp_oneForm x

section Mor

variable {κ : DividedPowers I} {t : X ⟶ Sp R} {κ' : DividedPowers I'} {t' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
  (m : IsMor κ t κ' t' σ φ)

theorem morSemi (T : Thick κ' t') : SemiHom (B := (m.obj T).B) (B' := T.B) σ (RingHom.id T.B) := fun r b ↦ (Algebra.smul_def (A := T.B) (σ r) b).symm

theorem morDP (T : Thick κ' t') : IsDPMorphism (m.obj T).δ T.δ (RingHom.id T.B) := (DPMorphism.id T.δ).isDPMorphism

def morMap : CxMap (KK κ t) (KK κ' t') where
  G := m.functor
  a0 T := AddMonoidHom.id T.B
  a1 T := km1 (morSemi m T) (morDP m T)
  a2 T := km (morSemi m T) (morDP m T) 2
  a3 T := km (morSemi m T) (morDP m T) 3
  compDegreeZero_natural _ _ := rfl
  compDegreeOne_natural {T T'} f x := (divPowerCompatOneFormMap_comp _ (m.functor.map f).dp (morSemi m T') (morDP m T') ((morSemi m T).comp (SemiHom.of_algHom f.φ))
      (IsDPMorphism.comp _ f.dp (morDP m T)) (fun _ ↦ rfl) x).trans
    (divPowerCompatOneFormMap_comp (morSemi m T) (morDP m T) (SemiHom.of_algHom f.φ) f.dp _ _ (fun _ ↦ rfl) x).symm
  compDegreeTwo_natural {T T'} f x := (km_km _ (m.functor.map f).dp (morSemi m T') (morDP m T') ((morSemi m T).comp (SemiHom.of_algHom f.φ))
      (IsDPMorphism.comp _ f.dp (morDP m T)) (fun _ ↦ rfl) 2 x).trans
    (km_km (morSemi m T) (morDP m T) (SemiHom.of_algHom f.φ) f.dp _ _ (fun _ ↦ rfl) 2 x).symm
  comp_commutes_diffZero T x := divPowerCompatOneFormMap_functionDifferential (morSemi m T) (morDP m T) x
  comp_commutes_diffOne T x := divPowerCompatFormMap_oneFormDerivative (morSemi m T) (morDP m T) x
  comp_commutes_diffTwo T x := divPowerCompatFormMap_twoFormDerivative (morSemi m T) (morDP m T) x

end Mor

variable {κ : DividedPowers I} {t : X ⟶ Sp R}

def IsCop (n : ℕ) {T A G : Thick κ t} (l : T ⟶ G) (r : A ⟶ G) : Prop :=
  IsLev G.δ n ∧ ∀ S : Thick κ t, IsLev S.δ n → ∀ (a : T ⟶ S) (b : A ⟶ S), ∃! c : G ⟶ S, l ≫ c = a ∧ r ≫ c = b

def IsFree (n : ℕ) {T F : Thick κ t} (u : T ⟶ F) {ι : Type} (τ : ι → F.B) : Prop :=
  IsLev F.δ n ∧ (∀ i, τ i ∈ F.J) ∧ ∀ S : Thick κ t, IsLev S.δ n → ∀ (a : T ⟶ S) (c : ι → S.B), (∀ i, c i ∈ S.J) →
    ∃! g : F ⟶ S, u ≫ g = a ∧ ∀ i, g.φ (τ i) = c i

structure Pr (κ : DividedPowers I) (t : X ⟶ Sp R) {Y : Scheme.{0}} (i : X ⟶ Y) : Type 1 where

  T : Thick κ t

  U : Y.Opens
  hU : IsAffineOpen U ∨ U = ⊤
  mem : ⊤ ≤ (T.x ≫ i) ⁻¹ᵁ U

variable {Y : Scheme.{0}} {i : X ⟶ Y}

def Pr.top (i : X ⟶ Y) (T : Thick κ t) : Pr κ t i := ⟨T, ⊤, Or.inr rfl, le_rfl⟩

instance : Category.{0} (Pr κ t i) where
  Hom a b := {_φ : a.T ⟶ b.T // b.U ≤ a.U}
  id a := ⟨𝟙 a.T, le_rfl⟩
  comp f g := ⟨f.1 ≫ g.1, g.2.trans f.2⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

variable (κ t i)

def Pr.fgt : Pr κ t i ⥤ Thick κ t where
  obj a := a.T
  map f := f.1

def IsAff : ObjectProperty (Pr κ t i) := fun a ↦ IsAffineOpen a.U

def IsSm : ObjectProperty (Pr κ t i) := fun a ↦ ∃ V : Y.affineOpens, ⊤ ≤ (a.T.x ≫ i) ⁻¹ᵁ V.1

abbrev EE : Type 1 := (IsAff κ t i).FullSubcategory

abbrev pE : EE κ t i ⥤ Thick κ t := (IsAff κ t i).ι ⋙ Pr.fgt κ t i

def LevE (n : ℕ) : ObjectProperty (EE κ t i) := fun a ↦ IsLev a.obj.T.δ n

end Site

open GlobalTheory.SmoothLift

structure Lift (D : Data) : Type 1 where

  L : AffOp D.X ⥤ Thick D.κ D.t

  e : ∀ U : AffOp D.X, Sec D.s U.unop.1 ≃ₐ[D.R] (L.obj U).B
  nat : ∀ {U V : AffOp D.X} (a : U ⟶ V) b, e V (mp (OAff D.s) a b) = (L.map a).φ (e U b)
  gen : ∀ U, (L.obj U).J = D.I.map (algebraMap D.R (L.obj U).B)
  pt : ∀ U, spMap ((L.obj U).π.comp (e U : Sec D.s U.unop.1 →+* (L.obj U).B)) ≫ affPt D.s U.unop = (L.obj U).x ≫ D.i
  mem : ∀ U, ⊤ ≤ ((L.obj U).x ≫ D.i) ⁻¹ᵁ U.unop.1

namespace Inhab

section Sections

variable (D : Data) (δ : ∀ U : D.X.affineOpens, DividedPowers (D.I.map (algebraMap D.R (Sec D.s U.1))))
  (hn : ∀ U, IsNilDP (δ U)) (hd : ∀ U, IsDPMorphism D.κ (δ U) (algebraMap D.R (Sec D.s U.1)))

theorem t_eq : D.t = D.i ≫ D.s := by
  obtain ⟨s₀, hp, ht⟩ := D.red
  rw [ht, hp.w]

theorem mono_i : Mono D.i := by
  obtain ⟨s₀, hp, -⟩ := D.red
  haveI : IsClosedImmersion (spMap (Ideal.Quotient.mk D.I)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact Limits.PullbackCone.mono_fst_of_is_pullback_of_mono hp.isLimit

def pt (U : D.X.affineOpens) : Sp (Sec D.s U.1 ⧸ D.I.map (algebraMap D.R (Sec D.s U.1))) ⟶ D.X₀ :=
  D.red.choose_spec.1.lift (spMap (Ideal.Quotient.mk _) ≫ affPt D.s U)
    (spMap (Ideal.quotientMap _ (algebraMap D.R (Sec D.s U.1)) Ideal.le_comap_map)) (by
      rw [Category.assoc, affPt_w, ← Cris.spMap_comp, ← Cris.spMap_comp]; rfl)

theorem pt_i (U : D.X.affineOpens) : pt D U ≫ D.i = spMap (Ideal.Quotient.mk _) ≫ affPt D.s U := IsPullback.lift_fst _ _ _ _

private theorem sec_res_comp_algebraMap {U V : D.X.affineOpens} (h : V.1 ≤ U.1) :
    (Sec.res D.s h : Sec D.s U.1 →+* Sec D.s V.1).comp (algebraMap D.R (Sec D.s U.1)) =
      algebraMap D.R (Sec D.s V.1) := by
  ext r
  exact AlgHom.commutes _ r

def thick (U : D.X.affineOpens) : Thick D.κ D.t where
  B := Sec D.s U.1
  J := D.I.map (algebraMap D.R (Sec D.s U.1))
  δ := δ U
  nil := hn U
  dp := hd U
  B₀ := Sec D.s U.1 ⧸ D.I.map (algebraMap D.R (Sec D.s U.1))
  π := Ideal.Quotient.mk _
  surj := Ideal.Quotient.mk_surjective
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := pt D U
  w := by rw [t_eq, ← Category.assoc, pt_i, Category.assoc, affPt_w, ← Cris.spMap_comp]

theorem res_le {U V : D.X.affineOpens} (h : V.1 ≤ U.1) : D.I.map (algebraMap D.R (Sec D.s U.1)) ≤
    (D.I.map (algebraMap D.R (Sec D.s V.1))).comap (Sec.res D.s h : Sec D.s U.1 →+* Sec D.s V.1) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, sec_res_comp_algebraMap]

include hd in

theorem res_dp {U V : D.X.affineOpens} (h : V.1 ≤ U.1) :
    IsDPMorphism (δ U) (δ V) (Sec.res D.s h : Sec D.s U.1 →+* Sec D.s V.1) := by
  refine IsDPMorphism.of_comp D.κ (δ U) (δ V) (algebraMap D.R (Sec D.s U.1)) _ rfl (hd U) ?_
  rw [sec_res_comp_algebraMap]
  exact hd V

theorem res_pt {U V : D.X.affineOpens} (h : V.1 ≤ U.1) :
    spMap (Ideal.quotientMap _ (Sec.res D.s h : Sec D.s U.1 →+* Sec D.s V.1) (res_le D h)) ≫ pt D U = pt D V := by
  have hP := D.red.choose_spec.1
  refine hP.hom_ext ?_ ?_
  · rw [Category.assoc, pt_i, pt_i, ← Category.assoc, ← Cris.spMap_comp, Ideal.quotientMap_comp_mk,
      Cris.spMap_comp, Category.assoc]
    congr 1
    exact U.2.map_fromSpec V.2 (homOfLE h).op
  · simp only [Category.assoc, pt, IsPullback.lift_snd]
    rw [← Cris.spMap_comp]
    congr 1
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r ↦ ?_)
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
    exact congrArg _ (RingHom.congr_fun (sec_res_comp_algebraMap D h) r)

def thickHom {U V : D.X.affineOpens} (h : V.1 ≤ U.1) : thick D δ hn hd U ⟶ thick D δ hn hd V where
  φ := Sec.res D.s h
  φ₀ := Ideal.quotientMap _ (Sec.res D.s h : Sec D.s U.1 →+* Sec D.s V.1) (res_le D h)
  comm _ := rfl
  dp := res_dp D δ hd h
  pt := res_pt D h

def _root_.GlobalTheory.PDForm.Lift.ofDP : Lift D where
  L := { obj U := thick D δ hn hd U.unop
         map a := thickHom D δ hn hd (leOfHom a.unop)
         map_id U := Thick.hom_ext (mp_id (OAff D.s) U)
         map_comp a b := Thick.hom_ext (mp_comp (OAff D.s) a b) }
  e _ := AlgEquiv.refl
  nat _ _ := rfl
  gen _ := rfl
  pt U := (pt_i D U.unop).symm
  mem U := by
    change ⊤ ≤ (pt D U.unop ≫ D.i) ⁻¹ᵁ U.unop.1
    have e : affPt D.s U.unop ⁻¹ᵁ U.unop.1 = ⊤ := U.unop.2.fromSpec_preimage_self
    rw [pt_i, Scheme.Hom.comp_preimage, e]
    exact le_rfl

end Sections

theorem map_sq {R A : Type} [CommRing R] [CommRing A] {I : Ideal R} (h : I ^ 2 = 0) (f : R →+* A) :
    I.map f ^ 2 = 0 := by
  simp [← Ideal.map_pow, h]

end Inhab

def Lift.ofSq (D : Data) (h : D.I ^ 2 = 0) (hκ : D.κ = divided₂ h) : Lift D :=
  Lift.ofDP D (fun _ ↦ divided₂ (Inhab.map_sq h _)) (fun _ ↦ isDPNilpotent_squareZero _)
    fun _ ↦ hκ ▸ isDPMorphism_sqDP h _ _ fun _ ha ↦ Ideal.mem_map_of_mem _ ha

theorem Inhab.span_two_sq : Ideal.span {(2 : ZMod 4)} ^ 2 = 0 := by
  rw [Ideal.span_singleton_pow, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  decide

def Lift.lineModFour : Lift Data.lineModFour := Lift.ofSq _ Inhab.span_two_sq rfl

def Inhab.wholeLine : AffOp Data.lineModFour.X := Opposite.op ⟨⊤, isAffineOpen_top (Sp (Polynomial (ZMod 4)))⟩

open Polynomial in

theorem Lift.lineModFour_ideal : (Lift.lineModFour.L.obj Inhab.wholeLine).J ≠ ⊥ ∧
    (Lift.lineModFour.L.obj Inhab.wholeLine).J ≠ ⊤ := by
  have h2 : algebraMap Data.lineModFour.R (Sec Data.lineModFour.s Inhab.wholeLine.unop.1) 2 ≠ 0 := by
    intro h0
    rw [map_ofNat] at h0
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of (Polynomial (ZMod 4)))).hom.hom 2 =
        (Scheme.ΓSpecIso (CommRingCat.of (Polynomial (ZMod 4)))).hom.hom 0 := congrArg _ h0
    rw [map_ofNat, map_zero] at h1
    have h3 : (2 : Polynomial (ZMod 4)) ≠ 0 := by
      rw [← map_ofNat Polynomial.C 2, Ne, Polynomial.C_eq_zero]
      decide
    exact h3 h1
  have hJ : (Lift.lineModFour.L.obj Inhab.wholeLine).J =
      Ideal.span {algebraMap Data.lineModFour.R (Sec Data.lineModFour.s Inhab.wholeLine.unop.1) 2} := by
    show Ideal.map (algebraMap Data.lineModFour.R _) Data.lineModFour.I = _
    rw [show Data.lineModFour.I = Ideal.span {(2 : Data.lineModFour.R)} from rfl, Ideal.map_span,
      Set.image_singleton]
  have h4 : algebraMap Data.lineModFour.R (Sec Data.lineModFour.s Inhab.wholeLine.unop.1) 2 *
      algebraMap Data.lineModFour.R (Sec Data.lineModFour.s Inhab.wholeLine.unop.1) 2 = 0 := by
    rw [← map_mul, show (2 : Data.lineModFour.R) * 2 = 0 from (by decide : (2 : ZMod 4) * 2 = 0),
      map_zero]
  rw [hJ]
  exact ⟨fun hb ↦ h2 (Ideal.span_singleton_eq_bot.mp hb),
    fun ht ↦ h2 ((Ideal.span_singleton_eq_top.mp ht).mul_left_eq_zero.mp h4)⟩

variable {D : Data} (Λ : Lift D)

def Lift.toE : AffOp D.X ⥤ EE D.κ D.t D.i where
  obj U := ⟨⟨Λ.L.obj U, U.unop.1, Or.inl U.unop.2, Λ.mem U⟩, U.unop.2⟩
  map a := ⟨⟨Λ.L.map a, leOfHom a.unop⟩⟩
  map_id U := ObjectProperty.hom_ext _ (Subtype.ext (Λ.L.map_id U))
  map_comp a b := ObjectProperty.hom_ext _ (Subtype.ext (Λ.L.map_comp a b))

theorem Lift.semi (U : AffOp D.X) : SemiHom (RingHom.id D.R) (Λ.e U : Sec D.s U.unop.1 →+* (Λ.L.obj U).B) := fun r b ↦ map_smul (Λ.e U) r b

def Lift.Res1 (k : ((KK D.κ D.t).res Λ.L).T1) (w : Tot1 (OAff D.s)) : Prop :=
  (∀ U V a, k.1 U V a = Λ.e V (w.1 U V a)) ∧ ∀ U, k.2 U = Submodule.Quotient.mk ((Λ.semi U).m1 (w.2 U))

def Lift.Res2 (k : ((KK D.κ D.t).res Λ.L).T2) (w : Tot2 (OAff D.s)) : Prop :=
  (∀ U V W a b, k.1 U V W a b = Λ.e W (w.1 U V W a b)) ∧
    (∀ U V a, k.2.1 U V a = Submodule.Quotient.mk ((Λ.semi V).m1 (w.2.1 U V a))) ∧
    ∀ U, k.2.2 U = Submodule.Quotient.mk ((Λ.semi U).mOm 2 (w.2.2 U))

def Lift.Rel1 (c : CatCoh.H1 (O D.κ D.t)) (h : HH1 D.s) : Prop :=
  ∃ (k : (KK D.κ D.t).Z1) (f : Z1 (O D.κ D.t)) (w : cechDeRhamTotalCocyclesOne (OAff D.s)), H1.mk _ f = c ∧ Hyp1.mk _ w = h ∧
    k.1.1 = f.1 ∧ Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k.1) w.1

def Lift.Rel2 (c : CatCoh.H2 (O D.κ D.t)) (h : HH2 D.s) : Prop :=
  ∃ (k : (KK D.κ D.t).Z2) (f : Z2 (O D.κ D.t)) (w : cechDeRhamTotalCocyclesTwo (OAff D.s)), H2.mk _ f = c ∧ Hyp2.mk _ w = h ∧
    k.1.1 = f.1 ∧ Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k.1) w.1

def eeLineModFour : EE Data.lineModFour.κ Data.lineModFour.t Data.lineModFour.i :=
  Lift.lineModFour.toE.obj Inhab.wholeLine

def Pr.lineModFour : Pr Data.lineModFour.κ Data.lineModFour.t Data.lineModFour.i := eeLineModFour.obj

theorem Pr.lineModFour_ideal : Pr.lineModFour.T.J ≠ ⊥ ∧ Pr.lineModFour.T.J ≠ ⊤ := Lift.lineModFour_ideal

theorem levE_eeLineModFour : LevE _ _ _ 2 eeLineModFour := isLev_sqDP (Inhab.map_sq Inhab.span_two_sq _)

theorem Inhab.isFree_id {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}
    {n : ℕ} {T : Thick κ t} (h : IsLev T.δ n) : IsFree n (𝟙 T) (Empty.elim : Empty → T.B) :=
  ⟨h, fun i ↦ i.elim, fun _ _ a _ _ ↦ ⟨a, ⟨Category.id_comp a, fun i ↦ i.elim⟩,
    fun g hg ↦ (Category.id_comp g).symm.trans hg.1⟩⟩

theorem Inhab.rel_bot (R B : Type) [CommRing R] [CommRing B] [Algebra R B] : rel R (dp0 B) = ⊥ := by
  unfold rel
  refine Ideal.span_eq_bot.mpr ?_
  rintro x ⟨n, a, ha, rfl⟩
  rw [Ideal.mem_bot] at ha
  subst ha
  simp [(dp0 B).dpow_eval_zero n.succ_ne_zero]

theorem Inhab.rel_dual_ne_bot : rel (ZMod 2) (divided₂ (SqExt.dual (ZMod 2)).sq) ≠ ⊥ := by
  intro hbot
  have hε : (TrivSqZeroExt.inr 1 : (SqExt.dual (ZMod 2)).C) ∈
      RingHom.ker ((SqExt.dual (ZMod 2)).π : (SqExt.dual (ZMod 2)).C →+* (SqExt.dual (ZMod 2)).B) := by
    rw [RingHom.mem_ker]
    rfl
  have hg : ι1 (D (ZMod 2) (SqExt.dual (ZMod 2)).C
      ((divided₂ (SqExt.dual (ZMod 2)).sq).dpow (1 + 1) (TrivSqZeroExt.inr 1)) -
      (divided₂ (SqExt.dual (ZMod 2)).sq).dpow 1 (TrivSqZeroExt.inr 1) •
        D (ZMod 2) (SqExt.dual (ZMod 2)).C (TrivSqZeroExt.inr 1)) ∈
      rel (ZMod 2) (divided₂ (SqExt.dual (ZMod 2)).sq) := Ideal.subset_span ⟨1, _, hε, rfl⟩
  rw [hbot, Ideal.mem_bot, squareZeroDividedPowers_dpow _ (le_refl (1 + 1)), (divided₂ _).dpow_one hε, map_zero, zero_sub,
    map_neg, neg_eq_zero, ExteriorAlgebra.ι_eq_zero_iff] at hg
  have h2 : ∀ u v : ZMod 2, u * v + u * v = 0 := by decide
  let d : Derivation (ZMod 2) (SqExt.dual (ZMod 2)).C (SqExt.dual (ZMod 2)).C := Derivation.mk'
    { toFun := fun x ↦ TrivSqZeroExt.inl x.snd
      map_add' := fun x y ↦ by ext <;> simp
      map_smul' := fun r x ↦ by ext <;> simp }
    (fun a b ↦ by ext <;> simp [h2, mul_comm])
  have h3 := congrArg d.liftKaehlerDifferential hg
  rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, map_zero] at h3
  have h4 := congrArg TrivSqZeroExt.snd h3
  simp [d] at h4

end GlobalTheory.PDForm
