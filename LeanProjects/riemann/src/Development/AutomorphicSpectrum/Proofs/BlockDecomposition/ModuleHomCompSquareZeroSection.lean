import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.AxForm

section Pair

variable {R S S' B M N : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S'] [CommRing B]
  [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
  [AddCommGroup N] [Module B N] [Module Bᵐᵒᵖ N] [IsCentralScalar B N]

theorem lift_smul_D {R S M : Type} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (d : Derivation R S M) (a b : S) :
    d.liftKaehlerDifferential (a • D R S b) = a • d b := by
  rw [map_smul, Derivation.liftKaehlerDifferential_comp_D]

abbrev OverR (R : Type) [CommRing R] {S B M : Type} [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (t : S →+* TrivSqZeroExt B M) : Prop :=
  t.comp (algebraMap R S) = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B)

theorem tower_pair (t : S →+* TrivSqZeroExt B M) (ht : OverR R t) :
    letI : Module S M := Module.compHom M ((TrivSqZeroExt.fstHom B B M).toRingHom.comp t)
    letI : Module R M := Module.compHom M (algebraMap R B)
    IsScalarTower R S M :=
  letI : Module S M := Module.compHom M ((TrivSqZeroExt.fstHom B B M).toRingHom.comp t)
  letI : Module R M := Module.compHom M (algebraMap R B)
  ⟨fun r a m ↦ by
    change (TrivSqZeroExt.fst (t (r • a))) • m = algebraMap R B r • (TrivSqZeroExt.fst (t a)) • m
    have e : (t (algebraMap R S r)).fst = algebraMap R B r := by
      have := congrArg (fun q ↦ (q r).fst) ht
      simpa using this
    rw [Algebra.smul_def, map_mul, TrivSqZeroExt.fst_mul, e, mul_smul]⟩

def pair (t : S →+* TrivSqZeroExt B M) (ht : OverR R t) : Ω[S⁄R] →+ M :=
  letI : Module S M := Module.compHom M ((TrivSqZeroExt.fstHom B B M).toRingHom.comp t)
  letI : Module R M := Module.compHom M (algebraMap R B)
  haveI : IsScalarTower R S M := tower_pair t ht
  let d : Derivation R S M := Derivation.mk'
    { toFun := fun a ↦ (t a).snd
      map_add' := fun a b ↦ by simp
      map_smul' := fun r a ↦ by
        have e : t (algebraMap R S r) = TrivSqZeroExt.inl (algebraMap R B r) :=
          congrArg (fun q ↦ q r) ht
        change (t (r • a)).snd = algebraMap R B r • (t a).snd
        rw [Algebra.smul_def, map_mul, e]
        simp }
    fun a b ↦ by
      change (t (a * b)).snd = (t a).fst • (t b).snd + (t b).fst • (t a).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul]
  d.liftKaehlerDifferential.toAddMonoidHom

theorem pair_smul_D (t : S →+* TrivSqZeroExt B M) (ht : OverR R t) (a b : S) :
    pair t ht (a • D R S b) = (t a).fst • (t b).snd := by
  letI : Module S M := Module.compHom M ((TrivSqZeroExt.fstHom B B M).toRingHom.comp t)
  letI : Module R M := Module.compHom M (algebraMap R B)
  haveI : IsScalarTower R S M := tower_pair t ht
  exact lift_smul_D _ a b

theorem pairing_differential_pullback (ψ : S →+* S') (hψ : SemiHom (RingHom.id R) ψ) (t : S' →+* TrivSqZeroExt B M) (ht : OverR R t)
    (ht' : OverR R (t.comp ψ)) (ω : Ω[S⁄R]) : pair t ht (hψ.m1 ω) = pair (t.comp ψ) ht' ω := by
  induction ω using ind1 with
  | h a b => rw [SemiHom.oneFormMap_smul_semilinear, SemiHom.m1_D, pair_smul_D, pair_smul_D]; rfl
  | h0 => simp
  | ha x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem pair_map (u : M →ₗ[B] N) (t : S →+* TrivSqZeroExt B M) (ht : OverR R t)
    (ht' : OverR R ((TrivSqZeroExt.map u).toRingHom.comp t)) (ω : Ω[S⁄R]) :
    pair ((TrivSqZeroExt.map u).toRingHom.comp t) ht' ω = u (pair t ht ω) := by
  induction ω using ind1 with
  | h a b =>
    rw [pair_smul_D, pair_smul_D, map_smul]
    simp
  | h0 => simp
  | ha x y hx hy => rw [map_add, map_add, map_add, hx, hy]

def mkT (ε : S →+* B) (l : Ω[S⁄R] →+ M) (hl : ∀ a ω, l (a • ω) = ε a • l ω) : S →+* TrivSqZeroExt B M where
  toFun a := TrivSqZeroExt.inl (ε a) + TrivSqZeroExt.inr (l (D R S a))
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Derivation.leibniz, hl, add_comm]

theorem overR_mkT (ε : S →+* B) (l : Ω[S⁄R] →+ M) (hl : ∀ a ω, l (a • ω) = ε a • l ω)
    (he : ε.comp (algebraMap R S) = algebraMap R B) : OverR R (mkT ε l hl) := by
  ext r
  · simpa [mkT] using congrArg (fun q ↦ q r) he
  · simp [mkT]

theorem pair_mkT (ε : S →+* B) (l : Ω[S⁄R] →+ M) (hl : ∀ a ω, l (a • ω) = ε a • l ω)
    (ht : OverR R (mkT ε l hl)) (ω : Ω[S⁄R]) : pair (mkT ε l hl) ht ω = l ω := by
  induction ω using ind1 with
  | h a b => rw [pair_smul_D, hl]; simp [mkT]
  | h0 => simp
  | ha x y hx hy => rw [map_add, map_add, hx, hy]

end Pair

section Pts

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem exists_factor (s : X ⟶ Sp R) (U : X.affineOpens) {C : Type} [CommRing C] (y : Sp C ⟶ X)
    (hy : ∀ z, y z ∈ U.1) : ∃ t : Sec s U.1 →+* C, spMap t ≫ affPt s U = y := by
  haveI : IsOpenImmersion (affPt s U) := U.2.isOpenImmersion_fromSpec
  have hr : Set.range y ⊆ Set.range (affPt s U) := by
    rintro _ ⟨z, rfl⟩
    have := U.2.range_fromSpec
    change _ ∈ Set.range U.2.fromSpec
    rw [this]
    exact hy z
  refine ⟨(Spec.preimage (IsOpenImmersion.lift (affPt s U) y hr)).hom, ?_⟩
  have e : spMap (Spec.preimage (IsOpenImmersion.lift (affPt s U) y hr)).hom =
      IsOpenImmersion.lift (affPt s U) y hr := Spec.map_preimage _
  rw [e]
  exact IsOpenImmersion.lift_fac _ _ _

theorem factor_unique (s : X ⟶ Sp R) (U : X.affineOpens) {C : Type} [CommRing C] {t t' : Sec s U.1 →+* C}
    (h : spMap t ≫ affPt s U = spMap t' ≫ affPt s U) : t = t' := by
  haveI : IsOpenImmersion (affPt s U) := U.2.isOpenImmersion_fromSpec
  have := Spec.map_injective ((cancel_mono (affPt s U)).1 h)
  exact congrArg CommRingCat.Hom.hom this

theorem factor_over (s : X ⟶ Sp R) (U : X.affineOpens) {C : Type} [CommRing C] (t : Sec s U.1 →+* C)
    (ρ : R →+* C) (h : (spMap t ≫ affPt s U) ≫ s = spMap ρ) : t.comp (algebraMap R (Sec s U.1)) = ρ := by
  have e : spMap (t.comp (algebraMap R (Sec s U.1))) = spMap ρ := by
    rw [spMap_comp, ← h, Category.assoc, affPt_w]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem mem_of_closedPoint {B : Type} [CommRing B] [IsLocalRing B] (w : Sp B ⟶ X) (W : X.Opens)
    (h : w (IsLocalRing.closedPoint B) ∈ W) (z : Sp B) : w z ∈ W := by
  have hz : (z : PrimeSpectrum B) ⤳ IsLocalRing.closedPoint B :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (PrimeSpectrum.asIdeal_le_asIdeal _ _ |>.1 (IsLocalRing.le_maximalIdeal z.isPrime.ne_top))
  exact (hz.map w.continuous).mem_open W.isOpen h

theorem mem_of_fst {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (y : Sp (TrivSqZeroExt B M) ⟶ X) (W : X.Opens)
    (h : ∀ z, (spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ y) z ∈ W) (z : Sp (TrivSqZeroExt B M)) :
    y z ∈ W := by
  have hz : ∀ m : M, TrivSqZeroExt.inr m ∈ (z : PrimeSpectrum _).asIdeal := fun m ↦
    (z : PrimeSpectrum _).isPrime.mem_of_pow_mem 2 (by rw [sq, TrivSqZeroExt.inr_mul_inr]; exact Ideal.zero_mem _)
  let z' : PrimeSpectrum B := PrimeSpectrum.comap (TrivSqZeroExt.inlHom B M) z
  have e : (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) z' = z := by
    change PrimeSpectrum.comap (TrivSqZeroExt.fstHom B B M).toRingHom z' = z
    ext a
    have ea := TrivSqZeroExt.inl_fst_add_inr_snd_eq a
    change TrivSqZeroExt.inl a.fst ∈ (z : PrimeSpectrum _).asIdeal ↔ a ∈ (z : PrimeSpectrum _).asIdeal
    constructor
    · intro h1
      rw [← ea]
      exact Ideal.add_mem _ h1 (hz _)
    · intro h1
      rw [eq_sub_of_add_eq ea]
      exact Ideal.sub_mem _ h1 (hz a.snd)
  have h2 : y ((spMap (TrivSqZeroExt.fstHom B B M).toRingHom) z') ∈ W := h z'
  rwa [e] at h2

end Pts

section Axis

variable {R : Type} [CommRing R] {X X' : Scheme.{0}}

theorem pair_axis {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap (RingHom.id R))
    (ω : GlobForm s) (hω : IsPullForm h ω 0) (U : X.affineOpens) {B M : Type} [CommRing B] [Algebra R B]
    [IsLocalRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (t : Sec s U.1 →+* TrivSqZeroExt B M) (ht : OverR R t) (y : Sp (TrivSqZeroExt B M) ⟶ X')
    (hy : y ≫ s' = spMap ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)))
    (e : spMap t ≫ affPt s U = y ≫ φ) : pair t ht (ω.1 (op U)) = 0 := by
  have hU : ∀ z, (y ≫ φ) z ∈ U.1 := fun z ↦ by
    rw [← e]
    change affPt s U _ ∈ U.1
    have := U.2.range_fromSpec
    rw [← SetLike.mem_coe, ← this]
    exact ⟨_, rfl⟩
  let w : Sp B ⟶ X' := spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ y
  have hz : w (IsLocalRing.closedPoint B) ∈ φ ⁻¹ᵁ U.1 := hU _
  obtain ⟨V, hV, hzV, hVU⟩ := exists_isAffineOpen_mem_and_subset hz
  have hyV : ∀ z, y z ∈ V := mem_of_fst y V (mem_of_closedPoint w V hzV)
  obtain ⟨t', et'⟩ := exists_factor s' ⟨V, hV⟩ y hyV
  have ht' : OverR R t' := factor_over s' ⟨V, hV⟩ t' _ (by rw [et', hy])
  let p : Pair φ := ⟨(⟨V, hV⟩, U), hVU⟩
  have et : t = t'.comp (secPull s s' p) := factor_unique s U (by
    rw [e, spMap_comp, Category.assoc, secPull_affPt, ← Category.assoc, et'])
  subst et
  have k := isPullForm_iff.1 hω p
  rw [← pairing_differential_pullback _ (semiHom_secPull h p) t' ht' ht]
  have k' : (semiHom_secPull h p).m1 (ω.1 (op U)) = 0 := k
  rw [k', map_zero]

end Axis

section Split

variable {R : Type} [CommRing R]

abbrev TT {C : Type} [CommRing C] (ρ : R →+* C) : Over (Sp R) := Over.mk (spMap ρ)

def pt {C C' : Type} [CommRing C] [CommRing C'] {ρ : R →+* C} {ρ' : R →+* C'} (f : C →+* C')
    (h : f.comp ρ = ρ') : TT ρ' ⟶ TT ρ :=
  Over.homMk (spMap f) (by change spMap f ≫ spMap ρ = spMap ρ'; rw [← h, spMap_comp])

theorem pt_comp {C C' C'' : Type} [CommRing C] [CommRing C'] [CommRing C''] {ρ : R →+* C} {ρ' : R →+* C'}
    {ρ'' : R →+* C''} (f : C →+* C') (h : f.comp ρ = ρ') (g : C' →+* C'') (h' : g.comp ρ' = ρ'')
    (k : C →+* C'') (hk : g.comp f = k) (h'' : k.comp ρ = ρ'') : pt g h' ≫ pt f h = pt k h'' := by
  subst hk
  ext1
  exact (spMap_comp f g).symm

theorem pt_id {C : Type} [CommRing C] {ρ : R →+* C} (f : C →+* C) (hf : f = RingHom.id C) (h : f.comp ρ = ρ) :
    pt f h = 𝟙 _ := by
  subst hf
  ext1
  exact spMap_id C

variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M]

abbrev r1 (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] : R →+* TrivSqZeroExt B M :=
  (TrivSqZeroExt.inlHom B M).comp (algebraMap R B)

abbrev mH {N : Type} [AddCommGroup N] [Module B N] [Module Bᵐᵒᵖ N] [IsCentralScalar B N] (u : M →ₗ[B] N) :
    TrivSqZeroExt B M →+* TrivSqZeroExt B N := (TrivSqZeroExt.map u).toRingHom

theorem module_hom_comp_square_zero_section {N : Type} [AddCommGroup N] [Module B N] [Module Bᵐᵒᵖ N] [IsCentralScalar B N] (u : M →ₗ[B] N) :
    (mH u).comp (r1 R B M) = r1 R B N := by
  ext r <;> simp

theorem fst_comp_square_zero_section : (TrivSqZeroExt.fstHom B B M).toRingHom.comp (r1 R B M) = algebraMap R B := by
  ext r; simp

abbrev x0 (A : Over (Sp R)) [MonObj A] (B : Type) [CommRing B] [Algebra R B] : TT (algebraMap R B) ⟶ A :=
  toUnit _ ≫ η[A]

theorem exists_split (A : Over (Sp R)) [GrpObj A] (y : TT (r1 R B M) ⟶ A ⊗ A)
    (hy : pt (ρ := r1 R B M) (TrivSqZeroExt.fstHom B B M).toRingHom fst_comp_square_zero_section ≫ y = lift (x0 A B) (x0 A B)) :
    ∃ Y : TT (r1 R B (M × M)) ⟶ A ⊗ A,
      pt (ρ := r1 R B (M × M)) (TrivSqZeroExt.fstHom B B (M × M)).toRingHom fst_comp_square_zero_section ≫ Y = lift (x0 A B) (x0 A B) ∧
      pt (mH (LinearMap.fst B M M + LinearMap.snd B M M)) (module_hom_comp_square_zero_section _) ≫ Y = y ∧
      pt (mH (LinearMap.fst B M M)) (module_hom_comp_square_zero_section _) ≫ Y =
        (y ≫ CartesianMonoidalCategory.fst A A) ≫ lift (𝟙 A) (1 : A ⟶ A) ∧
      pt (mH (LinearMap.snd B M M)) (module_hom_comp_square_zero_section _) ≫ Y =
        (y ≫ CartesianMonoidalCategory.snd A A) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
  let i₁ := pt (mH (LinearMap.inl B M M)) (module_hom_comp_square_zero_section (R := R) _)
  let i₂ := pt (mH (LinearMap.inr B M M)) (module_hom_comp_square_zero_section (R := R) _)
  have hf : ∀ (u : M →ₗ[B] M × M), pt (ρ := r1 R B (M × M)) (TrivSqZeroExt.fstHom B B (M × M)).toRingHom fst_comp_square_zero_section ≫
      pt (mH u) (module_hom_comp_square_zero_section _) = pt (ρ := r1 R B M) (TrivSqZeroExt.fstHom B B M).toRingHom fst_comp_square_zero_section := fun u ↦
    pt_comp _ _ _ _ _ (by ext a <;> simp) _
  have hz : ∀ (u : M × M →ₗ[B] M) (v : M →ₗ[B] M × M), u ∘ₗ v = 0 →
      pt (mH u) (module_hom_comp_square_zero_section _) ≫ pt (mH v) (module_hom_comp_square_zero_section _) =
        pt (ρ := algebraMap R B) (TrivSqZeroExt.inlHom B M) rfl ≫
          pt (ρ := r1 R B M) (TrivSqZeroExt.fstHom B B M).toRingHom fst_comp_square_zero_section := fun u v huv ↦ by
    have hK : (mH u).comp (mH v) =
        (TrivSqZeroExt.inlHom B M).comp (TrivSqZeroExt.fstHom B B M).toRingHom :=
      RingHom.ext fun a ↦ TrivSqZeroExt.ext (by simp) (by simpa using LinearMap.congr_fun huv a.snd)
    have h3 : ((TrivSqZeroExt.inlHom B M).comp (TrivSqZeroExt.fstHom B B M).toRingHom).comp (r1 R B M) =
        r1 R B M := by ext r <;> simp
    exact (pt_comp _ _ _ _ _ hK h3).trans (pt_comp _ _ _ _ _ rfl h3).symm
  have hi : ∀ (u : M × M →ₗ[B] M) (v : M →ₗ[B] M × M), u ∘ₗ v = LinearMap.id →
      pt (mH u) (module_hom_comp_square_zero_section _) ≫ pt (mH v) (module_hom_comp_square_zero_section (R := R) _) = 𝟙 _ := fun u v huv ↦ by
    have hK : (mH u).comp (mH v) = RingHom.id _ :=
      RingHom.ext fun a ↦ TrivSqZeroExt.ext (by simp) (by simpa using LinearMap.congr_fun huv a.snd)
    exact (pt_comp _ _ _ _ _ rfl (by rw [hK]; rfl)).trans (pt_id _ hK _)
  have f1 : pt (ρ := r1 R B M) (TrivSqZeroExt.fstHom B B M).toRingHom fst_comp_square_zero_section ≫ y ≫
      CartesianMonoidalCategory.fst A A = x0 A B := by
    rw [← Category.assoc, hy, lift_fst]
  have s1 : pt (ρ := r1 R B M) (TrivSqZeroExt.fstHom B B M).toRingHom fst_comp_square_zero_section ≫ y ≫
      CartesianMonoidalCategory.snd A A = x0 A B := by
    rw [← Category.assoc, hy, lift_snd]
  have hx : ∀ {Z : Over (Sp R)} (a : Z ⟶ TT (algebraMap R B)), a ≫ x0 A B = toUnit Z ≫ η[A] := fun a ↦ by
    rw [← Category.assoc, toUnit_unique (a ≫ toUnit _) (toUnit _)]
  have h1 : ∀ {Z : Over (Sp R)} (a : Z ⟶ A), a ≫ (1 : A ⟶ A) = toUnit Z ≫ η[A] := fun a ↦ by
    rw [Hom.one_def, ← Category.assoc, toUnit_unique (a ≫ toUnit _) (toUnit _)]
  refine ⟨lift (i₁ ≫ y ≫ CartesianMonoidalCategory.fst A A) (i₂ ≫ y ≫ CartesianMonoidalCategory.snd A A),
    ?_, ?_, ?_, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst, ← Category.assoc, hf, f1]
    · rw [Category.assoc, lift_snd, lift_snd, ← Category.assoc, hf, s1]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, ← Category.assoc, hi _ _ (by ext <;> simp), Category.id_comp]
    · rw [Category.assoc, lift_snd, ← Category.assoc, hi _ _ (by ext <;> simp), Category.id_comp]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.assoc, lift_fst, ← Category.assoc, hi _ _ (by ext <;> simp),
        Category.id_comp, Category.comp_id]
    · rw [Category.assoc, lift_snd, Category.assoc, lift_snd, ← Category.assoc, hz _ _ (by ext <;> simp),
        Category.assoc, s1, hx, h1]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.assoc, lift_fst, ← Category.assoc, hz _ _ (by ext <;> simp),
        Category.assoc, f1, hx, h1]
    · rw [Category.assoc, lift_snd, Category.assoc, lift_snd, ← Category.assoc, hi _ _ (by ext <;> simp),
        Category.id_comp, Category.comp_id]

end Split

section Core

variable {R : Type} [CommRing R]

theorem core (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [IsLocalRing B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (c : GlobForm (A ⊗ A).hom)
    (h1 : IsPullForm (wOver (lift (𝟙 A) (1 : A ⟶ A))) c 0) (h2 : IsPullForm (wOver (lift (1 : A ⟶ A) (𝟙 A))) c 0)
    (U : (A ⊗ A).left.affineOpens) (ε : Sec (A ⊗ A).hom U.1 →+* B)
    (hε : spMap ε ≫ affPt (A ⊗ A).hom U = (lift (x0 A B) (x0 A B)).left)
    (l : Ω[Sec (A ⊗ A).hom U.1⁄R] →+ M) (hl : ∀ a ω, l (a • ω) = ε a • l ω) : l (c.1 (op U)) = 0 := by
  have he : ε.comp (algebraMap R _) = algebraMap R B :=
    factor_over _ U ε _ (by rw [hε]; exact Over.w (lift (x0 A B) (x0 A B)))
  have ht := overR_mkT ε l hl he
  let t := mkT ε l hl
  have hU : ∀ z, (spMap ε ≫ affPt (A ⊗ A).hom U) z ∈ U.1 := fun z ↦ by
    change affPt _ U _ ∈ U.1
    have := U.2.range_fromSpec
    rw [← SetLike.mem_coe, ← this]
    exact ⟨_, rfl⟩
  let y : TT (r1 R B M) ⟶ A ⊗ A := Over.homMk (spMap t ≫ affPt (A ⊗ A).hom U) (by
    change (spMap t ≫ affPt (A ⊗ A).hom U) ≫ (A ⊗ A).hom = spMap (r1 R B M)
    rw [Category.assoc, affPt_w, ← spMap_comp]
    exact congrArg spMap ht)
  have hft : (TrivSqZeroExt.fstHom B B M).toRingHom.comp t = ε := by
    ext a; simp [t, mkT]
  have hy : pt (ρ := r1 R B M) (TrivSqZeroExt.fstHom B B M).toRingHom fst_comp_square_zero_section ≫ y =
      lift (x0 A B) (x0 A B) := by
    apply Over.OverMorphism.ext
    rw [← hε, ← hft, spMap_comp]
    exact (Category.assoc _ _ _).symm
  obtain ⟨Y, hY0, hYs, hY1, hY2⟩ := exists_split A y hy
  have hYU : ∀ z, Y.left z ∈ U.1 := mem_of_fst Y.left U.1 fun z ↦ by
    have e : spMap (TrivSqZeroExt.fstHom B B (M × M)).toRingHom ≫ Y.left = spMap ε ≫ affPt (A ⊗ A).hom U :=
      (congrArg (fun q ↦ q.left) hY0).trans hε.symm
    rw [e]
    exact hU z
  obtain ⟨t₂, et₂⟩ := exists_factor (A ⊗ A).hom U Y.left hYU
  have ht₂ : OverR R t₂ := factor_over _ U t₂ _ (by rw [et₂]; exact Over.w Y)
  have cmpU : ∀ (u : M × M →ₗ[B] M), spMap ((mH u).comp t₂) ≫ affPt (A ⊗ A).hom U =
      (pt (mH u) (module_hom_comp_square_zero_section (R := R) _) ≫ Y).left := fun u ↦ by
    rw [spMap_comp, Category.assoc, et₂]; rfl
  have ovr : ∀ (u : M × M →ₗ[B] M), OverR R ((mH u).comp t₂) := fun u ↦ by
    change ((mH u).comp t₂).comp _ = _
    rw [RingHom.comp_assoc, ht₂]
    exact module_hom_comp_square_zero_section (R := R) u
  have es : (mH (LinearMap.fst B M M + LinearMap.snd B M M)).comp t₂ = t := factor_unique _ U (by
    rw [cmpU, hYs]; rfl)
  have k1 : pair ((mH (LinearMap.fst B M M)).comp t₂) (ovr _) (c.1 (op U)) = 0 :=
    pair_axis (wOver (lift (𝟙 A) (1 : A ⟶ A))) c h1 U _ _ (y ≫ CartesianMonoidalCategory.fst A A).left
      (Over.w (y ≫ CartesianMonoidalCategory.fst A A)) (by
        rw [cmpU, hY1]; rfl)
  have k2 : pair ((mH (LinearMap.snd B M M)).comp t₂) (ovr _) (c.1 (op U)) = 0 :=
    pair_axis (wOver (lift (1 : A ⟶ A) (𝟙 A))) c h2 U _ _ (y ≫ CartesianMonoidalCategory.snd A A).left
      (Over.w (y ≫ CartesianMonoidalCategory.snd A A)) (by
        rw [cmpU, hY2]; rfl)
  rw [pair_map _ t₂ ht₂] at k1 k2
  have k3 := pair_map (LinearMap.fst B M M + LinearMap.snd B M M) t₂ ht₂ (ovr _) (c.1 (op U))
  rw [LinearMap.add_apply, k1, k2, add_zero] at k3
  have k4 : ∀ (t' : _ →+* TrivSqZeroExt B M) (e : t' = t) (h : OverR R t'), pair t' h (c.1 (op U)) = l (c.1 (op U)) := by
    intro t' e h
    subst e
    exact pair_mkT ε l hl _ _
  rw [← k4 _ es (ovr _), k3]

end Core

section Final

variable {R : Type} [CommRing R]

theorem vanish_map (A : Over (Sp R)) [GrpObj A] (hPar : Par (OAff (A ⊗ A).hom)) (c : GlobForm (A ⊗ A).hom)
    (h1 : IsPullForm (wOver (lift (𝟙 A) (1 : A ⟶ A))) c 0) (h2 : IsPullForm (wOver (lift (1 : A ⟶ A) (𝟙 A))) c 0)
    (B : Type) [CommRing B] [Algebra R B] [IsLocalRing B] (M : Type) [AddCommGroup M] [Module R M] [Module B M]
    [IsScalarTower R B M] (g : GlobForm (A ⊗ A).hom →ₗ[R] M) : g c = 0 := by
  let x : TT (algebraMap R B) ⟶ A ⊗ A := lift (x0 A B) (x0 A B)
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x.left (IsLocalRing.closedPoint B))
    (U := ⊤) trivial
  let U : (A ⊗ A).left.affineOpens := ⟨V, hV⟩
  obtain ⟨ε, hε⟩ := exists_factor (A ⊗ A).hom U x.left (mem_of_closedPoint x.left V hzV)
  have he : ε.comp (algebraMap R _) = algebraMap R B :=
    factor_over _ U ε _ (by rw [hε]; exact Over.w x)
  have hb := hPar (op U)
  letI : Module Bᵐᵒᵖ M := Module.compHom M ((RingHom.id B).fromOpposite fun x y ↦ Commute.all x y)
  haveI : IsCentralScalar B M := ⟨fun _ _ ↦ rfl⟩
  letI : Module (Sec (A ⊗ A).hom U.1) M := Module.compHom M ε
  haveI : IsScalarTower R (Sec (A ⊗ A).hom U.1) M := ⟨fun r a m ↦ by
    change ε (r • a) • m = r • (ε a • m)
    have e : ε (algebraMap R _ r) = algebraMap R B r := congrArg (fun q ↦ q r) he
    rw [Algebra.smul_def, map_mul, e, mul_smul, algebraMap_smul]⟩
  let l := hb.lift g
  have k := core A c h1 h2 U ε hε l.toAddMonoidHom (fun a ω ↦ l.map_smul a ω)
  exact (hb.lift_eq g c).symm.trans k

theorem vanish_at (A : Over (Sp R)) [GrpObj A] (hPar : Par (OAff (A ⊗ A).hom)) (c : GlobForm (A ⊗ A).hom)
    (h1 : IsPullForm (wOver (lift (𝟙 A) (1 : A ⟶ A))) c 0) (h2 : IsPullForm (wOver (lift (1 : A ⟶ A) (𝟙 A))) c 0)
    (p : Ideal R) [p.IsPrime] : ∃ r : R, r ∉ p ∧ r • c = 0 := by
  let B := Localization.AtPrime p
  let G := GlobForm (A ⊗ A).hom
  have k' := vanish_map A hPar c h1 h2 B (B ⊗[R] G) (TensorProduct.mk R B G 1)
  have hl : IsLocalizedModule p.primeCompl (TensorProduct.mk R B G 1) :=
    (isLocalizedModule_iff_isBaseChange p.primeCompl B _).2 (TensorProduct.isBaseChange R G B)
  obtain ⟨r, hr⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl (TensorProduct.mk R B G 1)).1 k'
  exact ⟨r.1, r.2, hr⟩

theorem smooth_sq (A : Over (Sp R)) (g : ℕ) (hs : SmoothOfRelativeDimension g A.hom) :
    SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
  have h₁ : SmoothOfRelativeDimension g (Limits.pullback.snd A.hom A.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hs
  rw [Over.tensorObj_hom, Limits.pullback.condition]
  exact smoothOfRelativeDimension_comp g g _ _

end Final

theorem axFormSt : CotSt → SteinSt → ParSt → AxFormSt := by
  intro _ _ hP R _ A _ g hA hs c h1 h2
  have hPar := (hP R (A ⊗ A) (g + g) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_sq A g hs)).1
  by_contra hc
  have hI : (R ∙ c).annihilator ≠ ⊤ := fun h ↦ hc (by
    have := (Submodule.mem_annihilator_span_singleton c 1).1 (h ▸ Submodule.mem_top)
    simpa using this)
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨r, hr, hrc⟩ := vanish_at A hPar c h1 h2 p
  exact hr (hle ((Submodule.mem_annihilator_span_singleton c r).2 hrc))

end GlobalTheory.CompanionTheory.AxForm
