import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPolAVFiniteTypeSubring

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

section Rat

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def ratHull (R : Subalgebra o Ω) : Subalgebra o Ω :=
  R.saturation (Algebra.algebraMapSubmonoid Ω (nonZeroDivisors ℤ)) (by
    rintro _ ⟨n, -, rfl⟩
    exact intCast_mem R n)

theorem mem_ratHull {R : Subalgebra o Ω} {x : Ω} : x ∈ ratHull R ↔ ∃ n : ℤ, n ≠ 0 ∧ (n : Ω) * x ∈ R :=
  ⟨fun ⟨_, ⟨n, hn, rfl⟩, h⟩ => ⟨n, nonZeroDivisors.ne_zero hn, h⟩,
    fun ⟨n, hn, h⟩ => ⟨_, ⟨n, mem_nonZeroDivisors_of_ne_zero hn, rfl⟩, h⟩⟩

theorem le_ratHull (R : Subalgebra o Ω) : R ≤ ratHull R := Subalgebra.le_saturation

theorem ratHull_mono {R R' : Subalgebra o Ω} (h : R ≤ R') : ratHull R ≤ ratHull R' := fun _ hx =>
  let ⟨n, hn, hx⟩ := mem_ratHull.1 hx
  mem_ratHull.2 ⟨n, hn, h hx⟩

abbrev toRat (R : Subalgebra o Ω) : R →+* ratHull R := (Subalgebra.inclusion (le_ratHull R)).toRingHom

theorem isUnit_intCast_ratHull [CharZero Ω] (R : Subalgebra o Ω) {n : ℤ} (hn : n ≠ 0) : IsUnit (n : ratHull R) := by
  have h0 : (n : Ω) ≠ 0 := Int.cast_ne_zero.2 hn
  refine IsUnit.of_mul_eq_one ⟨(n : Ω)⁻¹, mem_ratHull.2 ⟨n, hn, by rw [mul_inv_cancel₀ h0]; exact one_mem _⟩⟩
    (Subtype.ext ?_)
  simpa using mul_inv_cancel₀ h0

theorem isLocalization_ratHull [CharZero Ω] (R : Subalgebra o Ω) :
    letI := (toRat R).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ)) (ratHull R) := by
  letI := (toRat R).toAlgebra
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, hn, rfl⟩
    simpa using isUnit_intCast_ratHull R (nonZeroDivisors.ne_zero hn)
  · rintro ⟨x, hx⟩
    obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
    refine ⟨⟨⟨_, h⟩, ⟨_, n, mem_nonZeroDivisors_of_ne_zero hn, rfl⟩⟩, Subtype.ext ?_⟩
    show x * ((algebraMap ℤ R n : R) : Ω) = n * x
    simp [mul_comm]
  · intro a b h
    exact ⟨1, by rw [Subalgebra.inclusion_injective (le_ratHull R) h]⟩

theorem existsUnique_ratLift [CharZero Ω] (R : Subalgebra o Ω) {K : Type} [CommRing K]
    (hK : ∀ n : ℤ, n ≠ 0 → IsUnit (n : K)) (f : R →+* K) : ∃! g : ratHull R →+* K, g.comp (toRat R) = f := by
  letI := (toRat R).toAlgebra
  haveI := isLocalization_ratHull R
  have hf : ∀ y : Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ), IsUnit (f y) := by
    rintro ⟨_, n, hn, rfl⟩
    simpa using hK n (nonZeroDivisors.ne_zero hn)
  exact ⟨IsLocalization.lift (S := ratHull R) hf, IsLocalization.lift_comp (S := ratHull R) hf, fun g hg =>
    (IsLocalization.lift_unique (S := ratHull R) hf fun x => RingHom.congr_fun hg x).symm⟩

theorem existsUnique_ratPoint [CharZero Ω] (R : Subalgebra o Ω) {K : Type} [Field K] [CharZero K] (x : Sp K ⟶ Sp R) :
    ∃! x' : Sp K ⟶ Sp (ratHull R), x' ≫ spMap (toRat R) = x := by
  obtain ⟨g, hg, hu⟩ := existsUnique_ratLift R (K := K) (fun n hn => IsUnit.mk0 _ (Int.cast_ne_zero.2 hn))
    (Spec.preimage x).hom
  refine ⟨spMap g, ?_, fun y hy => ?_⟩
  · show spMap g ≫ _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg, CommRingCat.ofHom_hom, Spec.map_preimage]
  · rw [← hu (Spec.preimage y).hom (by rw [← hy, Spec.preimage_comp, Spec.preimage_map]; rfl)]
    exact (Spec.map_preimage y).symm

theorem spMap_val_toRat (R : Subalgebra o Ω) :
    spMap (ratHull R).val.toRingHom ≫ spMap (toRat R) = spMap R.val.toRingHom := by
  rw [← Spec.map_comp]; rfl

example : ratHull (⊥ : Subalgebra ℤ ℚ) = ⊤ := top_unique fun x _ =>
  mem_ratHull.2 ⟨x.den, by simp, Algebra.mem_bot.2 ⟨x.num, by simp [Rat.den_mul_eq_num]⟩⟩

end Rat

theorem exists_ratPoint_of_finiteType {X : Scheme.{0}} (s : X ⟶ Sp ℚ) [LocallyOfFiniteType s] (x : X) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : ArithBase ℤ Ω) (R : Subalgebra ℤ Ω), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ b ∈ R, z = a / b) ∧
      ∃ u : Sp (ratHull R) ⟶ X, ∀ w, (spMap (ratHull R).val.toRingHom ≫ u) w = x := by
  classical
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  let φ : ℚ →+* Γ(X, U) := (s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom
  have hφ : φ.FiniteType := RingHom.FiniteType.comp
    (HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top)
    (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of ℚ)).symm.commRingCatIsoToRingEquiv.surjective)
  letI := φ.toAlgebra
  obtain ⟨t, ht⟩ : Algebra.FiniteType ℚ Γ(X, U) := hφ
  let p := hU.primeIdealOf ⟨x, hx⟩
  let Ω := p.asIdeal.ResidueField
  let ev : Γ(X, U) →+* Ω := algebraMap _ _
  haveI : CharZero Ω := (RingHom.charZero_iff (ev.comp φ).injective).1 inferInstance
  letI : Algebra ℤ Ω := Ring.toIntAlgebra Ω
  let R : Subalgebra ℤ Ω := Algebra.adjoin ℤ (t.image ev : Finset Ω)
  have hR : ∀ a, ev a ∈ ratHull R := fun a => by
    have ha : a ∈ Algebra.adjoin ℚ (t : Set Γ(X, U)) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem a ha => exact le_ratHull R (Algebra.subset_adjoin (by simpa using ⟨a, ha, rfl⟩))
    | algebraMap q =>
      refine mem_ratHull.2 ⟨q.den, by simp, ?_⟩
      have : ((q.den : ℤ) : Ω) * ev (algebraMap ℚ _ q) = (q.num : Ω) := by
        rw [show ev (algebraMap ℚ _ q) = (ev.comp φ) q from rfl, eq_ratCast]
        exact_mod_cast Rat.den_mul_eq_num q
      exact this ▸ intCast_mem R _
    | add a b _ _ ha hb => exact map_add ev a b ▸ add_mem ha hb
    | mul a b _ _ ha hb => exact map_mul ev a b ▸ mul_mem ha hb
  refine ⟨Ω, inferInstance, ⟨inferInstance, inferInstance, inferInstance, Int.cast_injective⟩, R, ⟨_, rfl⟩, fun z => ?_,
    spMap (ev.codRestrict (ratHull R) hR) ≫ hU.fromSpec, fun w => ?_⟩
  · obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (Γ(X, U) ⧸ p.asIdeal) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨n, hn, ha⟩ := mem_ratHull.1 (hR a)
    obtain ⟨m, hm, hb⟩ := mem_ratHull.1 (hR b)
    refine ⟨_, mul_mem (intCast_mem R m) ha, _, mul_mem (intCast_mem R n) hb, ?_⟩
    have hn' : (n : Ω) ≠ 0 := Int.cast_ne_zero.2 hn
    have hm' : (m : Ω) ≠ 0 := Int.cast_ne_zero.2 hm
    show ev a / ev b = _
    rw [mul_left_comm, mul_div_mul_left _ _ hn', mul_div_mul_left _ _ hm']
  · have e : spMap (ratHull R).val.toRingHom ≫ spMap (ev.codRestrict (ratHull R) hR) = spMap ev := by
      rw [← Spec.map_comp]; rfl
    have hp : spMap ev w = p := by
      refine PrimeSpectrum.ext ?_
      show Ideal.comap ev w.asIdeal = p.asIdeal
      rw [Subsingleton.elim w (⊥ : PrimeSpectrum Ω)]
      exact Ideal.ker_algebraMap_residueField _
    rw [← Category.assoc, e, Scheme.Hom.comp_apply, hp]
    exact hU.fromSpec_primeIdealOf ⟨x, hx⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

structure UTrait (Xo : Moduli D l) (c : Coeff l) where

  V : Type
  [ring : CommRing V]
  [dom : IsDomain V]
  [loc : IsLocalRing V]
  cdvr : CDvr V

  ϖ : V
  irr : Irreducible ϖ

  y : Sp (FractionRing V) ⟶ Xo.XF c

  t : SAB H (Sp V)
  gen : GenOf Xo c y t

  P : PELUnif (maximalIdeal V) t

  be : LinearMap.BilinForm ℤ P.D.toPre.X
  lev : be ∈ levelForms H 1 P.D.toPre.X
  mono : IsMonomial P.D.toPre ![ϖ] ![be]

attribute [instance] UTrait.ring UTrait.dom UTrait.loc

def UOver (Xo : Moduli D l) (c : Coeff l) {R R' : Type} [CommRing R] [CommRing R'] (P : PolAV (Sp R)) (σ : R →+* R')
    (u : Sp R' ⟶ Xo.XF c) : Prop :=
  ∃ (G : Over (Sp R')) (_ : GrpObj G) (α : G.left ⟶ P.A.left) (β : G.left ⟶ Xo.univ.t.G.left),
    IsGrpPullback G P.A (spMap σ) α ∧ IsGrpPullback G Xo.univ.t.G (u ≫ pullback.fst _ _) β ∧
      LBIso (P.L.pull α) (Xo.univ.t.PP.L.pull β)

section UOver

variable {Xo : Moduli D l} {c : Coeff l} {R R' : Type} [CommRing R] [CommRing R'] {P : PolAV (Sp R)} {σ : R →+* R'}
  {u : Sp R' ⟶ Xo.XF c}

theorem UOver.comp (h : UOver Xo c P σ u) {R'' : Type} [CommRing R''] (τ : R' →+* R'') :
    UOver Xo c P (τ.comp σ) (spMap τ ≫ u) := by
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  have hG := isGrpPullback_pullback G (spMap τ)
  exact ⟨_, _, _, _, (hG.comp hα).congr (by rw [← Spec.map_comp]; rfl) rfl,
    (hG.comp hβ).congr (Category.assoc _ _ _).symm rfl, GenSpread.lbIso_pull_comp _ rfl rfl hL⟩

theorem uOver_baseChange_iff {R₁ : Type} [CommRing R₁] {P₁ : PolAV (Sp R₁)} {τ : R →+* R₁} {φ : P₁.A.left ⟶ P.A.left}
    (hφ : IsGrpPullback P₁.A P.A (spMap τ) φ) (hL : LBIso P₁.L (P.L.pull φ)) (σ₁ : R₁ →+* R') :
    UOver Xo c P₁ σ₁ u ↔ UOver Xo c P (σ₁.comp τ) u := by
  have e : spMap σ₁ ≫ spMap τ = spMap (σ₁.comp τ) := by rw [← Spec.map_comp]; rfl
  constructor
  · rintro ⟨G, _, α, β, hα, hβ, h⟩
    exact ⟨G, _, α ≫ φ, β, (hα.comp hφ).congr e rfl, hβ, LBIso.trans (pull_isLB P.isLB _) (pull_isLB P₁.isLB _)
      (pull_isLB Xo.univ.t.PP.isLB _) (GenSpread.lbIso_pull_of_lbIso hL α rfl).symm h⟩
  · rintro ⟨G, _, α, β, hα, hβ, h⟩
    have w : α ≫ P.A.hom = (G.hom ≫ spMap σ₁) ≫ spMap τ := by rw [Category.assoc, e]; exact hα.1.w
    have e₁ := hφ.1.lift_fst _ _ w
    exact ⟨G, _, hφ.1.lift _ _ w, β, hφ.cancel (hα.congr e.symm e₁.symm) (hφ.1.lift_snd _ _ w), hβ,
      LBIso.trans (pull_isLB P₁.isLB _) (pull_isLB P.isLB _) (pull_isLB Xo.univ.t.PP.isLB _)
        (GenSpread.lbIso_pull_of_lbIso hL _ e₁.symm) h⟩

theorem exists_pol_baseChange {S S' : Scheme.{0}} (P : PolAV S) (f : S' ⟶ S) :
    ∃ (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ ∧ LBIso P'.L (P.L.pull φ) := by
  obtain ⟨P', g, hg, -, hm, t, ht⟩ := polBaseChange_holds _ _ f P
  refine ⟨P', g, ⟨hg, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ⟨t, ht⟩⟩
  obtain rfl : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
  obtain rfl : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
  exact congrArg (·.left) (hm T x y).symm

theorem exists_uOver_id (u : Sp R' ⟶ Xo.XF c) : ∃ P : PolAV (Sp R'), UOver Xo c P (RingHom.id R') u := by
  obtain ⟨P, g, hG, hL⟩ := exists_pol_baseChange (Obj.toPolAV Xo.univ) (u ≫ pullback.fst _ _)
  haveI : IsMonHom (Iso.refl P.A).hom := inferInstanceAs (IsMonHom (𝟙 P.A))
  refine ⟨P, P.A, inferInstance, 𝟙 _, g, (isGrpPullback_of_iso (Iso.refl P.A)).congr (Spec.map_id _).symm rfl, hG, ?_⟩
  exact LBIso.trans (pull_isLB P.isLB _) P.isLB (pull_isLB Xo.univ.t.PP.isLB _)
    (LBIso.chartPull (chartPullId _) (chartPullUnpull P.L _ rfl) (PolBaseChange.lbIso_refl (pull_isLB P.isLB _))) hL

theorem exists_uOver_finiteType [IsDomain R'] [IsLocalRing R'] (u : Sp R' ⟶ Xo.XF c) :
    ∃ (R : Subring R') (P : PolAV (Sp R)), Algebra.FiniteType ℤ R ∧ UOver Xo c P R.subtype u := by
  obtain ⟨P, hP⟩ := exists_uOver_id u
  obtain ⟨R, P₀, φ, hR, -, hφ, hL⟩ := KeyTf.exists_polAV_finiteType_subring R' P
  exact ⟨R, P₀, hR, (uOver_baseChange_iff hφ hL _).1 hP⟩

end UOver

theorem exists_ratPoint (Xo : Moduli D l) (c : Coeff l) (x : Xo.XF c) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : ArithBase ℤ Ω) (R : Subalgebra ℤ Ω), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ b ∈ R, z = a / b) ∧
      ∃ u : Sp (ratHull R) ⟶ Xo.XF c, ∀ w, (spMap (ratHull R).val.toRingHom ≫ u) w = x := by
  haveI := c.fin
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  haveI : LocallyOfFiniteType (spMap (algebraMap ℚ c.F)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
  exact exists_ratPoint_of_finiteType (pullback.snd _ _ ≫ spMap (algebraMap ℚ c.F)) x

section Spread

theorem exists_spread_grp {B Ω : Type} [CommRing B] [IsDomain B] [Field Ω] [Algebra B Ω] [IsFractionRing B Ω]
    {G₁ G₂ : Over (Sp B)} [GrpObj G₁] [GrpObj G₂] (a₁ : IsAbelianScheme G₁) (a₂ : IsAbelianScheme G₂) {G : Over (Sp Ω)}
    [GrpObj G] {α₁ : G.left ⟶ G₁.left} {α₂ : G.left ⟶ G₂.left} (h₁ : IsGrpPullback G G₁ (spMap (algebraMap B Ω)) α₁)
    (h₂ : IsGrpPullback G G₂ (spMap (algebraMap B Ω)) α₂) :
    ∃ a : B, a ≠ 0 ∧ ∀ (B' : Type) [CommRing B'] (g : B →+* B') (j : B' →+* Ω), IsUnit (g a) → Function.Injective j →
      j.comp g = algebraMap B Ω → ∃ (β : pullback G₁.hom (spMap g) ⟶ G₂.left) (φ : G.left ⟶ pullback G₁.hom (spMap g)),
        IsGrpPullback ((Over.pullback (spMap g)).obj G₁) G₂ (spMap g) β ∧
        IsGrpPullback G ((Over.pullback (spMap g)).obj G₁) (spMap j) φ ∧ φ ≫ pullback.fst _ _ = α₁ ∧ φ ≫ β = α₂ := by
  have := a₁.proper
  have := a₁.smooth
  have := a₂.proper
  have := a₂.smooth
  obtain ⟨b₁, hb₁, H₁⟩ := GenSpread.exists_hom G₁.hom G₂.hom h₁.1 α₂ (h₂.1.w.trans h₁.1.w.symm)
  obtain ⟨b₂, hb₂, H₂⟩ := GenSpread.exists_hom G₂.hom G₁.hom h₂.1 α₁ (h₁.1.w.trans h₂.1.w.symm)
  refine ⟨b₁ * b₂, mul_ne_zero hb₁ hb₂, fun B' _ g j hu hj e => ?_⟩
  rw [map_mul, IsUnit.mul_iff] at hu
  have e' : spMap j ≫ spMap g = spMap (algebraMap B Ω) := by rw [← Spec.map_comp, ← e]; rfl
  haveI : IsSchemeTheoreticallyDominant (spMap j) := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hj
  obtain ⟨u, hu₁, hu₂⟩ := H₁ B' g hu.1 _ (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  obtain ⟨v, hv₁, hv₂⟩ := H₂ B' g hu.2 _ (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  have p₁ := isGrpPullback_pullback G₁ (spMap g)
  have p₂ := isGrpPullback_pullback G₂ (spMap g)
  have w₁ : α₁ ≫ G₁.hom = (G.hom ≫ spMap j) ≫ spMap g := by rw [Category.assoc, e']; exact h₁.1.w
  have w₂ : α₂ ≫ G₂.hom = (G.hom ≫ spMap j) ≫ spMap g := by rw [Category.assoc, e']; exact h₂.1.w
  have q₁ := p₁.cancel (h₁.congr e'.symm (pullback.lift_fst _ _ w₁).symm) (pullback.lift_snd _ _ w₁)
  have q₂ := p₂.cancel (h₂.congr e'.symm (pullback.lift_fst _ _ w₂).symm) (pullback.lift_snd _ _ w₂)
  let U : (Over.pullback (spMap g)).obj G₁ ⟶ (Over.pullback (spMap g)).obj G₂ :=
    Over.homMk (pullback.lift u (pullback.snd _ _) (hu₁.trans pullback.condition)) (pullback.lift_snd _ _ _)
  let V : (Over.pullback (spMap g)).obj G₂ ⟶ (Over.pullback (spMap g)).obj G₁ :=
    Over.homMk (pullback.lift v (pullback.snd _ _) (hv₁.trans pullback.condition)) (pullback.lift_snd _ _ _)
  have hU : U.left ≫ pullback.fst _ _ = u := pullback.lift_fst _ _ _
  have hV : V.left ≫ pullback.fst _ _ = v := pullback.lift_fst _ _ _
  have eU : (Iso.refl G).hom.left ≫ pullback.lift _ _ w₂ = pullback.lift _ _ w₁ ≫ U.left := by
    refine (Category.id_comp _).trans (pullback.hom_ext ?_ ?_)
    · exact (pullback.lift_fst _ _ _).trans (((Category.assoc _ _ _).trans (congrArg _ hU)).trans
        (hu₂ _ (pullback.lift_fst _ _ _))).symm
    · exact (pullback.lift_snd _ _ _).trans (((Category.assoc _ _ _).trans (congrArg _ (Over.w U))).trans
        (pullback.lift_snd _ _ _)).symm
  have eV : (Iso.refl G).inv.left ≫ pullback.lift _ _ w₁ = pullback.lift _ _ w₂ ≫ V.left := by
    refine (Category.id_comp _).trans (pullback.hom_ext ?_ ?_)
    · exact (pullback.lift_fst _ _ _).trans (((Category.assoc _ _ _).trans (congrArg _ hV)).trans
        (hv₂ _ (pullback.lift_fst _ _ _))).symm
    · exact (pullback.lift_snd _ _ _).trans (((Category.assoc _ _ _).trans (congrArg _ (Over.w V))).trans
        (pullback.lift_snd _ _ _)).symm
  haveI : Flat ((Over.pullback (spMap g)).obj G₁).hom := inferInstanceAs (Flat (pullback.snd _ _))
  haveI : Flat ((Over.pullback (spMap g)).obj G₂).hom := inferInstanceAs (Flat (pullback.snd _ _))
  haveI : IsSeparated ((Over.pullback (spMap g)).obj G₁).hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
  haveI : IsSeparated ((Over.pullback (spMap g)).obj G₂).hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
  haveI : IsIso U := ExtUnique.isIso_of_isPullback q₁.1 q₂.1 (Iso.refl G) U V eU eV
  haveI : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  haveI : IsMonHom (asIso U).hom := ExtUnique.isMonHom_of_isGrpPullback q₁ q₂ (Iso.refl G).hom U eU
  exact ⟨u, _, ((isGrpPullback_of_iso (asIso U)).comp p₂).congr (Category.id_comp _) hU, q₁, pullback.lift_fst _ _ _,
    hu₂ _ (pullback.lift_fst _ _ _)⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem exists_le_isUnit {R : Subalgebra o Ω} (hR : R.FG) {a : ratHull R} (ha : a ≠ 0) :
    ∃ (R' : Subalgebra o Ω) (h : R ≤ R'), R'.FG ∧ IsUnit ((Subalgebra.inclusion (ratHull_mono h)).toRingHom a) :=
  ⟨R ⊔ Algebra.adjoin o {(a : Ω)⁻¹}, le_sup_left, hR.sup (Subalgebra.fg_def.2 ⟨_, Set.finite_singleton _, rfl⟩),
    IsUnit.of_mul_eq_one ⟨_, le_ratHull _ ((le_sup_right : _ ≤ R ⊔ _) (Algebra.subset_adjoin rfl))⟩
      (Subtype.ext (mul_inv_cancel₀ fun h => ha (Subtype.ext h)))⟩

theorem UOver.exists_spread {Xo : Moduli D l} {c : Coeff l} {R : Subalgebra o Ω} (hR : R.FG)
    (hfr : ∀ z : Ω, ∃ a ∈ R, ∃ b ∈ R, z = a / b) {P : PolAV (Sp R)} {u : Sp (ratHull R) ⟶ Xo.XF c}
    (h : UOver Xo c P R.val.toRingHom (spMap (ratHull R).val.toRingHom ≫ u)) :
    ∃ (R' : Subalgebra o Ω) (hle : R ≤ R'), R'.FG ∧ UOver Xo c P ((toRat R').comp (Subalgebra.inclusion hle).toRingHom)
      (spMap (Subalgebra.inclusion (ratHull_mono hle)).toRingHom ≫ u) := by
  have fr : ∀ R' : Subalgebra o Ω, R ≤ R' → IsFractionRing (ratHull R') Ω := fun R' h =>
    IsFractionRing.of_field _ _ fun z =>
      let ⟨a, ha, b, hb, e⟩ := hfr z
      ⟨⟨a, le_ratHull _ (h ha)⟩, ⟨b, le_ratHull _ (h hb)⟩, e⟩
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  have p₁ := isGrpPullback_pullback P.A (spMap (toRat R))
  have p₂ := isGrpPullback_pullback Xo.univ.t.G (u ≫ pullback.fst _ _)
  have w₁ : α ≫ P.A.hom = (G.hom ≫ spMap (ratHull R).val.toRingHom) ≫ spMap (toRat R) := by
    rw [Category.assoc, spMap_val_toRat]; exact hα.1.w
  have w₂ : β ≫ Xo.univ.t.G.hom = (G.hom ≫ spMap (ratHull R).val.toRingHom) ≫ u ≫ pullback.fst _ _ := by
    rw [hβ.1.w]; simp only [Category.assoc]
  have q₁ := p₁.cancel (hα.congr (spMap_val_toRat R).symm (pullback.lift_fst _ _ w₁).symm) (pullback.lift_snd _ _ w₁)
  have q₂ := p₂.cancel (hβ.congr (Category.assoc _ _ _) (pullback.lift_fst _ _ w₂).symm) (pullback.lift_snd _ _ w₂)
  haveI := fr R le_rfl
  have a₁ := PolPull.isAbelianScheme_of_isGrpPullback P.isAb p₁
  obtain ⟨a, ha, H₁⟩ := exists_spread_grp (B := ratHull R) (Ω := Ω) a₁
    (PolPull.isAbelianScheme_of_isGrpPullback (Obj.toPolAV Xo.univ).isAb p₂) q₁ q₂
  obtain ⟨R₁, h₁, f₁, u₁⟩ := exists_le_isUnit hR ha
  obtain ⟨β₁, φ, g₂, gφ, e₁, e₂⟩ := H₁ _ _ (ratHull R₁).val.toRingHom u₁ Subtype.val_injective rfl
  have g₁ := isGrpPullback_pullback ((Over.pullback (spMap (toRat R))).obj P.A)
    (spMap (Subalgebra.inclusion (ratHull_mono h₁)).toRingHom)
  haveI := fr R₁ h₁
  haveI := (PolPull.isAbelianScheme_of_isGrpPullback a₁ g₁).proper
  have eα : φ ≫ pullback.fst _ _ ≫ pullback.fst P.A.hom (spMap (toRat R)) = α :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₁).trans (pullback.lift_fst _ _ _))
  have eβ : φ ≫ β₁ ≫ pullback.fst Xo.univ.t.G.hom (u ≫ pullback.fst _ _) = β :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₂).trans (pullback.lift_fst _ _ _))
  have hP := P.isLB
  have hU := Xo.univ.t.PP.isLB
  obtain ⟨a', ha', H₂⟩ := GenSpread.exists_lbIso (R := ratHull R₁) (K := Ω) _ gφ.1 (pull_isLB hP _) (pull_isLB hU _)
    (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hU _) _)
      (GenSpread.lbIso_pull_pull hP φ eα.symm).symm
      (LBIso.trans (pull_isLB hP _) (pull_isLB hU _) (pull_isLB (pull_isLB hU _) _) hL
        (GenSpread.lbIso_pull_pull hU φ eβ.symm)))
  obtain ⟨R₂, h₂, f₂, u₂⟩ := exists_le_isUnit f₁ ha'
  have g₃ := isGrpPullback_pullback ((Over.pullback (spMap (Subalgebra.inclusion (ratHull_mono h₁)).toRingHom)).obj
    ((Over.pullback (spMap (toRat R))).obj P.A)) (spMap (Subalgebra.inclusion (ratHull_mono h₂)).toRingHom)
  refine ⟨R₂, h₁.trans h₂, f₂, _, _, _, _, (g₃.comp (g₁.comp p₁)).congr ?_ rfl, (g₃.comp (g₂.comp p₂)).congr ?_ rfl, ?_⟩
  · rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  · rw [← Category.assoc, ← Spec.map_comp, Category.assoc]; rfl
  · exact LBIso.trans (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hU _)
      (GenSpread.lbIso_pull_pull hP _ rfl) (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB (pull_isLB hU _) _)
        (pull_isLB hU _) (H₂ _ _ u₂ _ _ _ g₃.1.w) (GenSpread.lbIso_pull_pull hU _ rfl).symm)

end Spread

theorem exists_uOver_ratPoint (Xo : Moduli D l) (c : Coeff l) (x : Xo.XF c) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : ArithBase ℤ Ω) (R : Subalgebra ℤ Ω), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ b ∈ R, z = a / b) ∧
      ∃ (P : PolAV (Sp R)) (u : Sp (ratHull R) ⟶ Xo.XF c), UOver Xo c P (toRat R) u ∧
        ∀ w, (spMap (ratHull R).val.toRingHom ≫ u) w = x := by
  obtain ⟨Ω, _, hb, R₀, f₀, fr, u, hu⟩ := exists_ratPoint Xo c x
  obtain ⟨R₁, P₁, f₁, h₁⟩ := exists_uOver_finiteType (spMap (ratHull R₀).val.toRingHom ≫ u)
  have f₁' : (subalgebraOfSubring R₁).FG := (Subalgebra.fg_iff_finiteType _).2 f₁
  let R := R₀ ⊔ subalgebraOfSubring R₁
  have frR : ∀ R' : Subalgebra ℤ Ω, R₀ ≤ R' → ∀ z : Ω, ∃ a ∈ R', ∃ b ∈ R', z = a / b := fun R' h z =>
    let ⟨a, ha, b, hb, e⟩ := fr z
    ⟨a, h ha, b, h hb, e⟩
  have pt : ∀ (R' : Subalgebra ℤ Ω) (h : R₀ ≤ R'), spMap (ratHull R').val.toRingHom ≫
      spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫ u = spMap (ratHull R₀).val.toRingHom ≫ u := fun R' h => by
    rw [← Category.assoc, ← Spec.map_comp]; rfl
  let τ : R₁ →+* R := (Subalgebra.inclusion (le_sup_right : subalgebraOfSubring R₁ ≤ R)).toRingHom
  obtain ⟨P, φ, hφ, hL⟩ := exists_pol_baseChange P₁ (spMap τ)
  obtain ⟨R', hle, f', h'⟩ := UOver.exists_spread (f₀.sup f₁') (frR R le_sup_left) (P := P)
    (u := spMap (Subalgebra.inclusion (ratHull_mono (le_sup_left : R₀ ≤ R))).toRingHom ≫ u)
    (by rw [pt R le_sup_left]; exact (uOver_baseChange_iff hφ hL _).2 h₁)
  obtain ⟨P', φ', hφ', hL'⟩ := exists_pol_baseChange P (spMap (Subalgebra.inclusion hle).toRingHom)
  refine ⟨Ω, _, hb, R', f', frR R' (le_sup_left.trans hle), P', _, (uOver_baseChange_iff hφ' hL' _).2 h', fun w => ?_⟩
  rw [← hu w, ← pt R le_sup_left, ← Category.assoc, ← Spec.map_comp]
  rfl

structure UCompact (Xo : Moduli D l) (c : Coeff l) where

  o : Type
  [ring : CommRing o]

  b : o →+* c.F
  inj : Function.Injective b
  frac : ∀ x : c.F, ∃ a a' : o, x = b a / b a'
  ded : IsDedekindDomain o
  ft : Algebra.FiniteType ℤ o
  unit_level : IsUnit (l.M' : o)
  unit_d : IsUnit (H.d : o)
  unit_discr : IsUnit ((NumberField.discr E : ℤ) : o)

  Z : Scheme.{0}

  z : Z ⟶ Sp o
  proj : IsProjOver z
  normal : IsNormalScheme Z

  iF : Xo.XF c ⟶ pullback z (spMap b)
  iF_open : IsOpenImmersion iF
  iF_dense : Dense (Set.range iF)
  iF_over : iF ≫ pullback.snd _ _ = pullback.snd _ _
  i_dense : Dense (Set.range (iF ≫ pullback.fst z (spMap b) :))

  OZ : LB Z
  OZ_lb : OZ.IsLB
  OZ_ample : IsAmpleLB OZ

  N : ℕ
  N_pos : 1 ≤ N
  omega : ∀ (Y : Model Xo c (RingHom.id c.F)) (f : Y.X ⟶ pullback z (spMap b)), Y.j ≫ f = iF →
    (GlobalTheory.FlagMod.detOm Y).IsLB → LBIso (OZ.pull (f ≫ pullback.fst _ _)) (lbPow (GlobalTheory.FlagMod.detOm Y) N)
  ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)),
    Nonempty (PELUnif (maximalIdeal R) t) → ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, GenOf Xo c y t →
      ∀ σ : Sp R ⟶ Sp o, jK R ≫ σ = y ≫ pullback.snd _ _ ≫ spMap b →
        ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ≫ iF ≫ pullback.fst _ _ ∧ ξ ≫ z = σ
  thetaInt : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real)
    (u : Sp (ratHull S.R) ⟶ Xo.XF c), UOver Xo c ρ.P (toRat S.R) u →
    (∀ w, (spMap (ratHull S.R).val.toRingHom ≫ u) w ∈ genericPoints (Xo.XF c)) →
    ∀ (M : RatModel o' Ω) (π : M.Z ⟶ Z), IsNormalScheme M.Z →
      M.pt ≫ π = spMap (ratHull S.R).val.toRingHom ≫ u ≫ iF ≫ pullback.fst _ _ → M.HasDiv S.th

attribute [instance] UCompact.ring

abbrev UCompact.i {Xo : Moduli D l} {c : Coeff l} (C : UCompact Xo c) : Xo.XF c ⟶ C.Z := C.iF ≫ pullback.fst _ _

theorem UCompact.isFractionRing {Xo : Moduli D l} {c : Coeff l} (C : UCompact Xo c) :
    letI := C.b.toAlgebra
    IsFractionRing C.o c.F := by
  letI := C.b.toAlgebra
  haveI := C.ded
  haveI : FaithfulSMul C.o c.F := (faithfulSMul_iff_algebraMap_injective _ _).2 C.inj
  exact IsFractionRing.of_field _ _ C.frac

theorem UCompact.isPreimmersion_i {Xo : Moduli D l} {c : Coeff l} (C : UCompact Xo c) : IsPreimmersion C.i := by
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.iF_open
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  infer_instance

theorem UCompact.exists_odd_prime_isUnit {Xo : Moduli D l} {c : Coeff l} (C : UCompact Xo c) :
    ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : C.o) :=
  ⟨H.d, H.d_prime, by have := H.d_mod; exact Nat.odd_iff.2 (by omega), C.unit_d⟩

structure USetup {Xo : Moduli D l} {c : Coeff l} (C : UCompact Xo c) where

  o₁ : Type

  Ω₁ : Type
  [ring : CommRing o₁]
  [field : Field Ω₁]
  [alg : Algebra o₁ Ω₁]
  [ar : ArithBase o₁ Ω₁]

  S : ThetaSys o₁ Ω₁

  ρ : S.Real
  big : S.Big

  u : Sp (ratHull S.R) ⟶ Xo.XF c
  pulled : UOver Xo c ρ.P (toRat S.R) u
  gen : ∀ w, (spMap (ratHull S.R).val.toRingHom ≫ u) w ∈ genericPoints (Xo.XF c)

  M : RatModel o₁ Ω₁
  normal : IsNormalScheme M.Z

  π : M.Z ⟶ C.Z
  fin : IsFinite π
  comp : M.pt ≫ π = spMap (ratHull S.R).val.toRingHom ≫ u ≫ C.i

attribute [instance] USetup.ring USetup.field USetup.alg USetup.ar

section Setup

variable {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c} (X₁ : USetup C)

abbrev USetup.uΩ : Sp X₁.Ω₁ ⟶ Xo.XF c := spMap (ratHull X₁.S.R).val.toRingHom ≫ X₁.u

theorem USetup.pulled_uΩ : UOver Xo c X₁.ρ.P X₁.S.R.val.toRingHom X₁.uΩ :=
  X₁.pulled.comp (ratHull X₁.S.R).val.toRingHom

theorem USetup.hasDiv : X₁.M.HasDiv X₁.S.th :=
  C.thetaInt _ _ X₁.S X₁.ρ X₁.u X₁.pulled X₁.gen X₁.M X₁.π X₁.normal X₁.comp

def USetup.Lies {K : Type} [CommRing K] (x : Sp K ⟶ Sp X₁.S.R) (y : Sp K ⟶ Xo.XF c) : Prop :=
  ∃ x' : Sp K ⟶ Sp (ratHull X₁.S.R), x' ≫ spMap (toRat X₁.S.R) = x ∧ x' ≫ X₁.u = y

theorem USetup.existsUnique_lies {K : Type} [Field K] [CharZero K] (x : Sp K ⟶ Sp X₁.S.R) : ∃! y, X₁.Lies x y := by
  haveI := X₁.ar.char
  obtain ⟨x', hx, hu⟩ := existsUnique_ratPoint X₁.S.R x
  exact ⟨_, ⟨x', hx, rfl⟩, fun _ ⟨x'', h, e⟩ => e ▸ hu x'' h ▸ rfl⟩

theorem USetup.lies_uΩ : X₁.Lies (spMap X₁.S.R.val.toRingHom) X₁.uΩ := ⟨_, spMap_val_toRat _, rfl⟩

theorem USetup.Lies.uOver {X₁ : USetup C} {K : Type} [CommRing K] {f : X₁.S.R →+* K} {y : Sp K ⟶ Xo.XF c}
    (h : X₁.Lies (spMap f) y) : UOver Xo c X₁.ρ.P f y := by
  obtain ⟨x', hx, rfl⟩ := h
  obtain ⟨g, rfl⟩ := Spec.map_surjective x'
  obtain rfl : g.hom.comp (toRat X₁.S.R) = f :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective ((Spec.map_comp _ _).trans hx))
  exact X₁.pulled.comp g.hom

end Setup

structure UCTrait {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c} (X₁ : USetup C) (p : ℕ) [Fact p.Prime]
    (z₁ : X₁.M.Z) where

  y : Sp (OO p) ⟶ X₁.M.Z
  cen : y (cPt p) = z₁

  T : UTrait Xo c

  ι : FractionRing T.V →+* PadicAlgCl p
  int : ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))
  comm : gPt p ≫ y ≫ X₁.π = spMap ι ≫ T.y ≫ C.i

variable {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c}

def UCTrait.sc {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (t : UCTrait X₁ p z₁) : ℝ :=
  -Real.log ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)‖

def UCTrait.val {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (t : UCTrait X₁ p z₁)
    (a : X₁.M.Z.presheaf.stalk z₁) : PadicAlgCl p :=
  X₁.M.val (gPt p ≫ t.y) (X₁.M.stalkHom z₁ a)

def UMatches {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}
    (Φ : GlobalTheory.Poinc.FPre (H.bar : 𝓞 E → 𝓞 E) (min D.p D.q) p (X₁.M.Z.presheaf.stalk z₁)) : Prop :=
  ∀ t : UCTrait X₁ p z₁, ∃ y : Φ.Y, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X,
    ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)

def UApproxAt (X₁ : USetup C) (φ : InvFun (𝓞 E)) (d : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (t₀ : UCTrait X₁ p z₁) (e : ℕ), ∃ f : X₁.M.Z.presheaf.stalk z₁,
    ‖t₀.val f‖ = Real.exp (-(t₀.sc * (d * φ.evalZ t₀.T.be))) ∧ ∀ t : UCTrait X₁ p z₁,
      ‖t.val f‖ ≤ Real.exp (-(t.sc * (d * φ.evalZ t.T.be))) ∨
        ∃ h ∈ IsLocalRing.maximalIdeal (X₁.M.Z.presheaf.stalk z₁), ‖t.val f‖ ≤ ‖t.val h‖ ^ e

def UMinSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), Nonempty (UCompact Xo c)

def UIdealSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ →
      ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c),
        ∃ (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range C.i) ∧ UValOn Xo c C.i φ J d

end GlobalTheory.UPoinc
