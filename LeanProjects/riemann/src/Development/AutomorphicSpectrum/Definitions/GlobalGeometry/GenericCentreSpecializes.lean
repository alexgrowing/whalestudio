import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ProjectiveLinePlaceTrivialOnConstants

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

structure FibreCurve (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ϖ : Ω) where

  k : Type

  κ : Type
  [fk : Field k]
  [fκ : Field κ]
  [alg : Algebra k κ]
  fg : (⊤ : IntermediateField k κ).FG
  trdeg : Algebra.trdeg k κ = 1

  C : Crv.ACurve κ
  w_pos : ∀ i, 0 < C.w i
  triv : ∀ i (a : k), a ≠ 0 → C.v i (algebraMap k κ a) = 1
  all : ∀ W : ValuationSubring κ, W ≠ ⊤ → (∀ a : k, algebraMap k κ a ∈ W) → ∃! i, (C.v i).valuationSubring = W

  η : Spec (CommRingCat.of κ) ⟶ X
  η_spec : genPt ξ ⤳ centre η
  η_zero : ValAt ξ η ϖ 0

  z : ∀ i, Spec (CommRingCat.of (C.v i).valuationSubring) ⟶ X
  z_gen : ∀ i, Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype) ≫ z i = η

attribute [instance] FibreCurve.fk FibreCurve.fκ FibreCurve.alg

def FibreCurve.HasDeg {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ϖ : Ω} (Γ : FibreCurve ξ ϖ) (L : Lat ξ Ω) (d : ℤ) : Prop :=
  ∃ (e : Ω) (f : Γ.C.I → Ω) (r : Γ.C.I → Γ.κ), L.IsGenAt ⟨centre Γ.η, Γ.η_spec⟩ e ∧
    (∀ i, ∃ h : genPt ξ ⤳ centre (Γ.z i), L.IsGenAt ⟨centre (Γ.z i), h⟩ (f i)) ∧
    (∀ i, r i ≠ 0 ∧ ValAt ξ Γ.η (e / f i) (r i)) ∧ {i | Γ.C.v i (r i) ≠ 1}.Finite ∧
    ∑ᶠ i, (Γ.C.w i : ℤ) * (-WithZero.log (Γ.C.v i (r i))) = d

def NumTrivMod {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ Ω) (ϖ : Ω) : Prop :=
  ∀ Γ : FibreCurve ξ ϖ, Γ.HasDeg L 0

namespace FibreCurve

open ProjectiveLinePlaces

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ϖ : Ω} (Γ : FibreCurve ξ ϖ) {L L' M : Lat ξ Ω} {d d' : ℤ}

theorem generic_centre_specializes (i : Γ.C.I) : centre Γ.η ⤳ centre (Γ.z i) := by
  have := centre_specializes (Γ.z i) (Γ.C.v i).valuationSubring.subtype
  rwa [Γ.z_gen i] at this

theorem z_spec (i : Γ.C.I) : genPt ξ ⤳ centre (Γ.z i) := Γ.η_spec.trans (Γ.generic_centre_specializes i)

theorem finite_support {g : Γ.C.I → Γ.κ} (hg : {i | Γ.C.v i (g i) ≠ 1}.Finite) :
    Function.HasFiniteSupport fun i => (Γ.C.w i : ℤ) * (-WithZero.log (Γ.C.v i (g i))) :=
  hg.subset fun i hi h1 => hi (by simp [h1])

theorem exists_val_of_unitAt (i : Γ.C.I) {a : Ω} (ha : unitAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩ a) :
    ∃ t : Γ.κ, ValAt ξ Γ.η a t ∧ Γ.C.v i t = 1 := by
  obtain ⟨t, ht⟩ := valAt_of_unit _ ha
  refine ⟨_, valAt_restrict _ (Γ.z_gen i) Γ.η_spec ht, ?_⟩
  have a1 : Γ.C.v i ((Γ.C.v i).valuationSubring.subtype t) ≤ 1 := t.1.2
  have a2 : Γ.C.v i ((Γ.C.v i).valuationSubring.subtype ↑t⁻¹) ≤ 1 := (t⁻¹).1.2
  have a3 : Γ.C.v i ((Γ.C.v i).valuationSubring.subtype t) *
      Γ.C.v i ((Γ.C.v i).valuationSubring.subtype ↑t⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm a1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := a3.symm
    _ ≤ _ * 1 := by gcongr
    _ = _ := mul_one _

variable {Γ}

theorem HasDeg.of_generators (hξ : IsCptGen ξ) (h : Γ.HasDeg L d) (e' : Ω) (f' : Γ.C.I → Ω) (r' : Γ.C.I → Γ.κ)
    (he' : L.IsGenAt ⟨centre Γ.η, Γ.η_spec⟩ e')
    (hf' : ∀ i, ∃ h : genPt ξ ⤳ centre (Γ.z i), L.IsGenAt ⟨centre (Γ.z i), h⟩ (f' i))
    (hr' : ∀ i, ValAt ξ Γ.η (e' / f' i) (r' i)) :
    (∀ i, r' i ≠ 0) ∧ {i | Γ.C.v i (r' i) ≠ 1}.Finite ∧
      ∑ᶠ i, (Γ.C.w i : ℤ) * (-WithZero.log (Γ.C.v i (r' i))) = d := by
  obtain ⟨e, f, r, he, hf, hr, hfin, hd⟩ := h
  obtain ⟨u, hu⟩ := valAt_of_unit Γ.η_spec (unitAt_div he' he)
  have key : ∀ i, Γ.C.v i (r' i) = Γ.C.v i (u : Γ.κ) * Γ.C.v i (r i) := by
    intro i
    obtain ⟨h, hi⟩ := hf i
    obtain ⟨h', hi'⟩ := hf' i
    obtain ⟨t, ht, hv⟩ := Γ.exists_val_of_unitAt i (unitAt_div hi hi')
    have h2 := CoordModel.valAt_mul (CoordModel.valAt_mul hu (hr i).2) ht
    have e0 := he.1
    have e1 := hi.1
    rw [show e' / e * (e / f i) * (f i / f' i) = e' / f' i by field_simp] at h2
    rw [CoordModel.valAt_unique hξ (hr' i) h2, map_mul, map_mul, hv, mul_one]
  have hu0 : ∀ i, Γ.C.v i (u : Γ.κ) ≠ 0 := fun i => by simp
  have hr0 : ∀ i, Γ.C.v i (r i) ≠ 0 := fun i => by simpa using (hr i).1
  refine ⟨fun i h0 => ?_, ((Γ.C.fin _ u.ne_zero).union hfin).subset fun i hi => ?_, ?_⟩
  · exact mul_ne_zero (hu0 i) (hr0 i) (by rw [← key, h0, map_zero])
  · by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    exact hi (by rw [key, hc.1, hc.2, mul_one])
  · simp_rw [key, fun i => WithZero.log_mul (hu0 i) (hr0 i), neg_add, mul_add]
    rw [finsum_add_distrib (Γ.finite_support (Γ.C.fin _ u.ne_zero)) (Γ.finite_support hfin), hd]
    simp_rw [mul_neg]
    rw [finsum_neg_distrib, Γ.C.prod _ u.ne_zero, neg_zero, zero_add]

theorem HasDeg.unique (hξ : IsCptGen ξ) (h : Γ.HasDeg L d) (h' : Γ.HasDeg L d') : d = d' := by
  obtain ⟨e, f, r, he, hf, hr, -, hd⟩ := h'
  exact (h.of_generators hξ e f r he hf fun i => (hr i).2).2.2.symm.trans hd

theorem HasDeg.mul (hM : ∀ p e e', L.IsGenAt p e → L'.IsGenAt p e' → M.IsGenAt p (e * e'))
    (h : Γ.HasDeg L d) (h' : Γ.HasDeg L' d') : Γ.HasDeg M (d + d') := by
  obtain ⟨e, f, r, he, hf, hr, hfin, hd⟩ := h
  obtain ⟨e', f', r', he', hf', hr', hfin', hd'⟩ := h'
  refine ⟨e * e', fun i => f i * f' i, fun i => r i * r' i, hM _ _ _ he he', fun i => ?_, fun i => ⟨?_, ?_⟩,
    (hfin.union hfin').subset fun i hi => ?_, ?_⟩
  · obtain ⟨h, hi⟩ := hf i
    obtain ⟨_, hi'⟩ := hf' i
    exact ⟨h, hM _ _ _ hi hi'⟩
  · exact mul_ne_zero (hr i).1 (hr' i).1
  · rw [mul_div_mul_comm]
    exact CoordModel.valAt_mul (hr i).2 (hr' i).2
  · by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    exact hi (by rw [map_mul, hc.1, hc.2, mul_one])
  · have : ∀ i, WithZero.log (Γ.C.v i (r i * r' i)) =
        WithZero.log (Γ.C.v i (r i)) + WithZero.log (Γ.C.v i (r' i)) := fun i => by
      rw [map_mul, WithZero.log_mul (by simpa using (hr i).1) (by simpa using (hr' i).1)]
    simp_rw [this, neg_add, mul_add]
    rw [finsum_add_distrib (Γ.finite_support hfin) (Γ.finite_support hfin'), hd, hd']

variable (Γ)

theorem hasDeg_iff_of_witness (hξ : IsCptGen ξ) (e : Ω) (f : Γ.C.I → Ω) (r : Γ.C.I → Γ.κ)
    (he : L.IsGenAt ⟨centre Γ.η, Γ.η_spec⟩ e)
    (hf : ∀ i, ∃ h : genPt ξ ⤳ centre (Γ.z i), L.IsGenAt ⟨centre (Γ.z i), h⟩ (f i))
    (hr : ∀ i, ValAt ξ Γ.η (e / f i) (r i)) (h0 : ∀ i, r i ≠ 0) (hfin : {i | Γ.C.v i (r i) ≠ 1}.Finite) (d : ℤ) :
    Γ.HasDeg L d ↔ ∑ᶠ i, (Γ.C.w i : ℤ) * (-WithZero.log (Γ.C.v i (r i))) = d :=
  ⟨fun h => (h.of_generators hξ e f r he hf hr).2.2, fun h => ⟨e, f, r, he, hf, fun i => ⟨h0 i, hr i⟩, hfin, h⟩⟩

theorem hasDeg_zero_of_gen {e : Ω} (he : L.IsGenAt ⟨centre Γ.η, Γ.η_spec⟩ e)
    (hf : ∀ i, L.IsGenAt ⟨centre (Γ.z i), Γ.z_spec i⟩ e) : Γ.HasDeg L 0 :=
  ⟨e, fun _ => e, fun _ => 1, he, fun i => ⟨_, hf i⟩,
    fun _ => ⟨one_ne_zero, Γ.η_spec, 1, by rw [map_one, div_self he.1], map_one _⟩, by simp, by simp⟩

theorem hasDeg_zero_of_isClosed (hc : IsClosed ({centre Γ.η} : Set X)) {e : Ω}
    (he : L.IsGenAt ⟨centre Γ.η, Γ.η_spec⟩ e) : Γ.HasDeg L 0 :=
  Γ.hasDeg_zero_of_gen he fun i => by
    have h : (⟨centre (Γ.z i), Γ.z_spec i⟩ : Cpt ξ) = ⟨centre Γ.η, Γ.η_spec⟩ :=
      Subtype.ext ((Γ.generic_centre_specializes i).mem_closed hc rfl)
    rw [h]
    exact he

theorem not_hasDeg_bot (d : ℤ) : ¬ Γ.HasDeg (fun _ => ⊥) d := fun ⟨_, _, _, he, _⟩ =>
  he.1 (Submodule.span_singleton_eq_bot.1 he.2.symm)

def scale (n : ℕ) (hn : 0 < n) : FibreCurve ξ ϖ :=
  { Γ with
    C := { Γ.C with
      w := fun i => n * Γ.C.w i
      prod := fun x hx => by
        simp_rw [Nat.cast_mul, mul_assoc]
        rw [← mul_finsum, Γ.C.prod x hx, mul_zero] }
    w_pos := fun i => Nat.mul_pos hn (Γ.w_pos i) }

theorem HasDeg.scale {Γ : FibreCurve ξ ϖ} (h : Γ.HasDeg L d) (n : ℕ) (hn : 0 < n) :
    (Γ.scale n hn).HasDeg L (n * d) := by
  obtain ⟨e, f, r, he, hf, hr, hfin, hd⟩ := h
  refine ⟨e, f, r, he, hf, hr, hfin, ?_⟩
  rw [← hd, mul_finsum]
  exact finsum_congr fun i => by
    change ((n * Γ.C.w i : ℕ) : ℤ) * _ = _
    rw [Nat.cast_mul, mul_assoc]
    rfl

end FibreCurve

theorem numTrivMod_of_gen {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Lat ξ Ω} {e : Ω} (he : ∀ p, L.IsGenAt p e)
    (ϖ : Ω) : NumTrivMod L ϖ := fun Γ => Γ.hasDeg_zero_of_gen (he _) fun _ => he _

example {ξ : Spec (CommRingCat.of Ω) ⟶ X} (ϖ : Ω) :
    NumTrivMod (fun p => Submodule.span (regAt ξ p) {(1 : Ω)} : Lat ξ Ω) ϖ :=
  numTrivMod_of_gen (fun _ => ⟨one_ne_zero, rfl⟩) ϖ

end General

namespace FibLine

open ProjectiveLinePlaces Crv.Inhab

section Proj

open MvPolynomial HomogeneousLocalization ProjCoord

attribute [local instance] MvPolynomial.gradedAlgebra

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem line_deg (x : Option (Fin 1) → Ω) (hx : ∀ c, x c ≠ 0)
    (hinj : ∀ (n : ℕ) (g : MvPolynomial (Option (Fin 1)) o), g.IsHomogeneous n → aeval x g = 0 → g = 0)
    (ξ : Spec (CommRingCat.of Ω) ⟶ Proj (homogeneousSubmodule (Option (Fin 1)) o)) (hξ : IsCptGen ξ)
    (e : ∀ c, ξ = CptModel.pt (chartEval x c (hx c)) ≫ Proj.awayι _ (X c) (X_mem c) one_pos)
    (k : Type) [Field k] [Algebra o k] (ϖ : o) (hϖ : algebraMap o k ϖ = 0) :
    ∃ Γ : FibreCurve ξ (algebraMap o Ω ϖ), ∀ (d : ℕ) (L : Lat ξ Ω),
      (∀ (p : Cpt ξ) c, InChart ξ x c p → L p = Submodule.span (regAt ξ p) {x c ^ d}) →
      ∀ n : ℤ, Γ.HasDeg L n ↔ n = d := by
  classical
  letI : Algebra o (RatFunc k) := ((algebraMap k (RatFunc k)).comp (algebraMap o k)).toAlgebra
  have hi := fun c => chartEval_injective x c (hx c) hinj
  let w : Option (Fin 1) → RatFunc k := fun j => j.elim 1 fun _ => RatFunc.X
  have hw : ∀ c, w c ≠ 0 := by
    rintro (_ | c)
    · exact one_ne_zero
    · exact RatFunc.X_ne_zero
  let c : (projLine k).I → Option (Fin 1) := fun i => Option.elim i (some 0) fun _ => none
  have hX : (projLine k).v none RatFunc.X = WithZero.exp 1 := RatFunc.inftyValuation.X k
  have hc : ∀ i j, (projLine k).v i (w j / w (c i)) ≤ 1 := by
    rintro (_ | q) (_ | j)
    · change (projLine k).v none (1 / RatFunc.X) ≤ 1
      rw [map_div₀, hX, map_one, one_div, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp]
      norm_num
    · change (projLine k).v none (RatFunc.X / RatFunc.X) ≤ 1
      rw [div_self RatFunc.X_ne_zero, map_one]
    · change (projLine k).v (some q) (1 / 1) ≤ 1
      simp
    · change q.valuation (RatFunc k) (RatFunc.X / 1) ≤ 1
      rw [div_one]
      exact q.valuation_le_one Polynomial.X
  have hmem : ∀ i a, chartEval (o := o) w (c i) (hw _) a ∈ ((projLine k).v i).valuationSubring := by
    intro i a
    have h := (mem_range_chartEval (o := o) w (c i) (hw _) _).1 ⟨a, rfl⟩
    generalize chartEval (o := o) w (c i) (hw _) a = b at h
    induction h using Algebra.adjoin_induction with
    | mem y hy => obtain ⟨j, rfl⟩ := hy; exact hc i j
    | algebraMap r =>
      change (projLine k).v i (algebraMap k (RatFunc k) (algebraMap o k r)) ≤ 1
      by_cases h0 : algebraMap o k r = 0
      · simp [h0]
      · exact (projective_line_place_trivial_on_constants k i _ h0).le
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
  obtain ⟨η, eη⟩ : ∃ η : Spec (CommRingCat.of (RatFunc k)) ⟶ Proj (homogeneousSubmodule (Option (Fin 1)) o), ∀ c,
      η = CptModel.pt (chartEval w c (hw c)) ≫ Proj.awayι _ (X c) (X_mem c) one_pos :=
    ⟨CptModel.pt (chartEval w none (hw none)) ≫ Proj.awayι _ (X none) (X_mem none) one_pos, fun c =>
      pt_awayι_eq _ _ (X_mem none) (X_mem c) one_pos one_pos _ _⟩
  have vη : ∀ c a, ValAt ξ η (chartEval (o := o) x c (hx c) a) (chartEval (o := o) w c (hw c) a) := fun c a => by
    rw [eη c]
    exact valAt_chart _ (hi c) _ (e c) _ a
  let χ := fun i => (chartEval (o := o) w (c i) (hw _)).codRestrict ((projLine k).v i).valuationSubring (hmem i)
  let z : ∀ i, Spec (CommRingCat.of ((projLine k).v i).valuationSubring) ⟶
      Proj (homogeneousSubmodule (Option (Fin 1)) o) := fun i =>
    Spec.map (CommRingCat.ofHom (χ i)) ≫ Proj.awayι _ (X (c i)) (X_mem (c i)) one_pos
  have vz : ∀ i a, ValAt ξ (z i) (chartEval (o := o) x (c i) (hx _) a) (χ i a) := fun i a =>
    valAt_chart _ (hi _) _ (e _) _ a
  have h0 : ValAt ξ η (algebraMap o Ω ϖ) 0 := by
    have := vη none (cst none ϖ)
    rw [chartEval_cst, chartEval_cst] at this
    convert this
    change 0 = algebraMap k (RatFunc k) (algebraMap o k ϖ)
    rw [hϖ, map_zero]
  let Γ : FibreCurve ξ (algebraMap o Ω ϖ) :=
    { k := k, κ := RatFunc k, fg := ratFunc_fg k, trdeg := ratFunc_trdeg k, C := projLine k,
      w_pos := projective_line_place_degree_pos k, triv := projective_line_place_trivial_on_constants k, all := projective_line_places_all_valuations k, η := η, η_spec := h0.1, η_zero := h0, z := z,
      z_gen := fun i => by
        rw [eη (c i), ← Category.assoc, ← Spec.map_comp]
        rfl }
  refine ⟨Γ, fun d L hL n => ?_⟩
  have vr : ∀ c j, ValAt ξ η (x j / x c) (w j / w c) := fun c j => by
    simpa only [chartEval_ratio] using vη c (ratio c j)
  rw [Γ.hasDeg_iff_of_witness hξ (L := L) (x none ^ d) (fun i => x (c i) ^ d) (fun i => (w none / w (c i)) ^ d)
    ⟨pow_ne_zero _ (hx _), hL _ none ⟨hx _, fun j => mem_regAt_of_valAt (vr none j) _⟩⟩
    (fun i => ⟨(vz i 0).1, pow_ne_zero _ (hx _), hL _ _ ⟨hx _, fun j => by
      have := mem_regAt_of_valAt (vz i (ratio (c i) j)) (vz i 0).1
      rwa [chartEval_ratio] at this⟩⟩)
    (fun i => by rw [← div_pow]; exact valAt_pow (vr _ _) d)
    (fun i => pow_ne_zero _ (div_ne_zero (hw _) (hw _)))
    ((Set.finite_singleton none).subset fun i hi => by
      rcases i with _ | q
      · rfl
      · exact absurd (show (projLine k).v (some q) ((1 / 1) ^ d) = 1 by simp) hi)]
  rw [finsum_eq_single (α := (projLine k).I) _ none]
  · change ((1 : ℕ) : ℤ) * -WithZero.log ((projLine k).v none ((1 / RatFunc.X) ^ d)) = n ↔ _
    rw [map_pow, map_div₀, hX, map_one, one_div, ← WithZero.exp_neg, ← WithZero.exp_nsmul, WithZero.log_exp]
    simp [eq_comm]
  · rintro (_ | q) hi
    · exact absurd rfl hi
    · change _ * -WithZero.log ((projLine k).v (some q) ((1 / 1) ^ d)) = 0
      simp

end Proj

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_line_curve (o : Type) [CommRing o] [IsDomain o] (k : Type) [Field k] [Algebra o k] (ϖ : o)
    (hϖ : algebraMap o k ϖ = 0) :
    ∃ ξ : Spec (CommRingCat.of (FractionRing (MvPolynomial (Fin 1) o))) ⟶
        Proj (MvPolynomial.homogeneousSubmodule (Option (Fin 1)) o), IsCptGen ξ ∧
      ∃ Γ : FibreCurve ξ (algebraMap o _ ϖ), ∀ d : ℕ, ∃ L : Lat ξ (FractionRing (MvPolynomial (Fin 1) o)),
        L.IsVB 1 ⊤ ∧ (∀ n : ℤ, Γ.HasDeg L n ↔ n = d) ∧ (d ≠ 0 → ¬ NumTrivMod L (algebraMap o _ ϖ)) := by
  have hi := IsFractionRing.injective (MvPolynomial (Fin 1) o) (FractionRing (MvPolynomial (Fin 1) o))
  have hx : ∀ c : Option (Fin 1), algebraMap (MvPolynomial (Fin 1) o)
      (FractionRing (MvPolynomial (Fin 1) o)) (c.elim 1 MvPolynomial.X) ≠ 0 := fun c => by
    rw [map_ne_zero_iff _ hi]
    cases c with
    | none => exact one_ne_zero
    | some j => exact MvPolynomial.X_ne_zero j
  have hinj : ∀ (d : ℕ) (g : MvPolynomial (Option (Fin 1)) o), g.IsHomogeneous d →
      MvPolynomial.aeval (fun j : Option (Fin 1) => algebraMap (MvPolynomial (Fin 1) o)
        (FractionRing (MvPolynomial (Fin 1) o)) (j.elim 1 MvPolynomial.X)) g = 0 → g = 0 := fun d g hg h => by
    exact ProjCoord.eq_zero_of_dehom hg ((map_eq_zero_iff _ hi).1
      ((MvPolynomial.aeval_algebraMap_apply _ _ g).symm.trans h))
  obtain ⟨ξ, hT, e⟩ := coordTie_charts _ hx none hinj (fun a => by
    have key : ∀ p : MvPolynomial (Fin 1) o, algebraMap _ (FractionRing (MvPolynomial (Fin 1) o)) p ∈
        Algebra.adjoin o (Set.range fun j : Option (Fin 1) =>
          algebraMap (MvPolynomial (Fin 1) o) (FractionRing (MvPolynomial (Fin 1) o))
            (j.elim 1 MvPolynomial.X) /
          algebraMap (MvPolynomial (Fin 1) o) (FractionRing (MvPolynomial (Fin 1) o)) 1) := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C r =>
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact Subalgebra.algebraMap_mem _ r
      | add p q hp hq =>
        rw [map_add]
        exact add_mem hp hq
      | mul_X p i hp =>
        rw [map_mul]
        exact mul_mem hp (Algebra.subset_adjoin ⟨some i, by simp⟩)
    obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin 1) o) a
    have h0 := (map_ne_zero_iff _ hi).2 (nonZeroDivisors.ne_zero hv)
    exact ⟨_, key u, _, key v, h0, div_mul_cancel₀ _ h0⟩)
  obtain ⟨Γ, hΓ⟩ := line_deg _ hx hinj ξ hT.gen e k ϖ hϖ
  refine ⟨ξ, hT.gen, Γ, fun d => ?_⟩
  obtain ⟨L, hL⟩ := Lat.exists_line hT d
  refine ⟨L, Lat.isVB_line hT hL, hΓ d L hL, fun hd h => hd ?_⟩
  exact_mod_cast ((hΓ d L hL 0).1 (h Γ)).symm

theorem exists_line_curve_int (p : ℕ) [Fact p.Prime] :
    ∃ ξ : Spec (CommRingCat.of (FractionRing (MvPolynomial (Fin 1) ℤ))) ⟶
        Proj (MvPolynomial.homogeneousSubmodule (Option (Fin 1)) ℤ), IsCptGen ξ ∧
      ∃ Γ : FibreCurve ξ (algebraMap ℤ _ (p : ℤ)), ∀ d : ℕ, ∃ L : Lat ξ (FractionRing (MvPolynomial (Fin 1) ℤ)),
        L.IsVB 1 ⊤ ∧ (∀ n : ℤ, Γ.HasDeg L n ↔ n = d) ∧ (d ≠ 0 → ¬ NumTrivMod L (algebraMap ℤ _ (p : ℤ))) :=
  exists_line_curve ℤ (ZMod p) (p : ℤ) (by simp)

theorem exists_fibreCurve : ∃ (X : Scheme.{0}) (Ω : Type) (_ : Field Ω) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ϖ : Ω)
    (Γ : FibreCurve ξ ϖ), IsCptGen ξ ∧ ϖ ≠ 0 ∧ ¬ IsClosed ({centre Γ.η} : Set X) := by
  obtain ⟨ξ, hξ, Γ, hΓ⟩ := exists_line_curve_int 2
  refine ⟨_, _, _, ξ, _, Γ, hξ, ?_, fun hc => ?_⟩
  · haveI : CharZero (FractionRing (MvPolynomial (Fin 1) ℤ)) :=
      charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial (Fin 1) ℤ) _)
    simp
  · obtain ⟨L, -, hL, -⟩ := hΓ 1
    obtain ⟨e, -, -, he, -⟩ := (hL 1).2 rfl
    exact absurd ((hL 0).1 (Γ.hasDeg_zero_of_isClosed hc he)) (by simp)

end FibLine

end GlobalTheory.CompanionTheory.Ar.Flat
