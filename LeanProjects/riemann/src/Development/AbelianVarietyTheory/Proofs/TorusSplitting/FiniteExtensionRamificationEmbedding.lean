import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EtaVal.FiniteExt

section Val

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem alg_ne {x : V} (hx : x ≠ 0) : algebraMap V (FractionRing V) x ≠ 0 := by
  simpa using hx

theorem vV_unit {u : V} (hu : IsUnit u) : vV V (algebraMap V (FractionRing V) u) = 0 := by
  have : valV V (algebraMap V (FractionRing V) u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal u).1 h hu
  simp [vV, this]

theorem vV_irr {p : V} (hp : Irreducible p) : vV V (algebraMap V (FractionRing V) p) = 1 := by
  have : valV V (algebraMap V (FractionRing V) p) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ hp.ne_zero
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer p).1 hp)
  simp [vV, this]

theorem vV_pow {x : FractionRing V} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  induction n with
  | zero => simp [vV]
  | succ n ih => rw [pow_succ, vV_mul (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem vV_eq {p : V} (hp : Irreducible p) {u : V} (hu : IsUnit u) (n : ℕ) :
    vV V (algebraMap V (FractionRing V) (u * p ^ n)) = n := by
  rw [map_mul, map_pow, vV_mul (alg_ne hu.ne_zero) (pow_ne_zero _ (alg_ne hp.ne_zero)), vV_unit hu,
    vV_pow (alg_ne hp.ne_zero), vV_irr hp]; simp

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem vV_ext (g : O →+* V) (hg : Function.Injective g) (i : FractionRing O →+* FractionRing V)
    (hi : ∀ a, i (algebraMap O _ a) = algebraMap V _ (g a)) {p : O} (hp : Irreducible p) (x : FractionRing O) :
    vV V (i x) = vV V (algebraMap V (FractionRing V) (g p)) * vV O x := by
  have h1 : ∀ a : O, a ≠ 0 → vV V (i (algebraMap O _ a)) =
      vV V (algebraMap V (FractionRing V) (g p)) * vV O (algebraMap O (FractionRing O) a) := by
    intro a ha
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hp
    have hgp : g p ≠ 0 := fun h => hp.ne_zero (hg (h.trans (map_zero g).symm))
    rw [vV_eq hp u.isUnit, hi, map_mul, map_pow, map_mul, map_pow,
      vV_mul (alg_ne (u.isUnit.map g).ne_zero) (pow_ne_zero _ (alg_ne hgp)), vV_unit (u.isUnit.map g),
      vV_pow (alg_ne hgp)]
    ring
  by_cases hx : x = 0
  · subst hx; simp [vV]
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have e1 : algebraMap O (FractionRing O) a / algebraMap O _ s * algebraMap O _ s = algebraMap O _ a :=
    div_mul_cancel₀ _ (alg_ne hs0)
  have e2 := vV_mul (V := O) hx (alg_ne hs0)
  have e3 := vV_mul (V := V) ((map_ne_zero i).2 hx) ((map_ne_zero i).2 (alg_ne hs0))
  rw [← map_mul, e1, h1 a ha0, h1 s hs0] at e3
  rw [e1] at e2
  rw [e2] at e3
  linarith

end Val

theorem exists_extension {A B C : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    (φ : A →+* B) (hφ : Function.Injective φ) (hint : φ.IsIntegral) (e : A →+* C)
    (he : Function.Injective e) (h1 : ∀ a, ‖e a‖ ≤ 1) :
    ∃ g : B →+* C, Function.Injective g ∧ (∀ a, g (φ a) = e a) ∧ ∀ b, ‖g b‖ ≤ 1 := by
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra A C := e.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hint⟩
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hφ
  haveI : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).2 he
  let g : B →ₐ[A] C := IsAlgClosed.lift
  refine ⟨g.toRingHom, ?_, fun a => g.commutes a, fun b => ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := A) ?_
    rw [eq_bot_iff]
    intro a ha
    have : g (algebraMap A B a) = 0 := ha
    rw [g.commutes] at this
    exact he (this.trans (map_zero e).symm)
  · have hb : IsIntegral A (g b) := (Algebra.IsIntegral.isIntegral b).map g
    let v := NormedField.valuation (K := C)
    let e' : A →+* v.integer := e.codRestrict v.integer (fun a => by
      rw [Valuation.mem_integer_iff]
      exact_mod_cast h1 a)
    letI : Algebra A v.integer := e'.toAlgebra
    haveI : IsScalarTower A v.integer C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hb' : IsIntegral v.integer (g b) := hb.tower_top
    have := (Valuation.integer.integers v).isIntegral_iff_v_le_one.1 hb'
    exact_mod_cast this

end GlobalTheory.EtaVal.FiniteExt

namespace GlobalTheory.EtaVal

open FiniteExt in

theorem finite_extension_ramification_embedding :
    ∀ (T T' : CDVR) (φ : T.V →+* T'.V), Function.Injective φ → φ.Finite → ∃ (i : T.Fr →+* T'.Fr) (ρ : ℕ), 0 < ρ ∧ (∀ a, i (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (φ a)) ∧ (∀ x, vV T'.V (i x) = (ρ : ℤ) * vV T.V x) ∧ ∀ (p : ℕ) (C : SCF p) (eF : T.Fr →+* ↥C.S), (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) → (∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) → ∃ f : T'.V →+* intO ↥C.S, Function.Injective f ∧ (∀ a, ((f (φ a) : intO ↥C.S) : ↥C.S) = eF (algebraMap T.V T.Fr a)) ∧ ∀ a ∈ maximalIdeal T'.V, ‖((f a : intO ↥C.S) : ↥C.S)‖ < 1 := by
  intro T T' φ hφ hfin
  have hint : φ.IsIntegral := hfin.to_isIntegral
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
  have hφp : φ p ≠ 0 := fun h => hp.ne_zero (hφ (h.trans (map_zero φ).symm))
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hφp hq
  have hn : 0 < n := by
    haveI : IsLocalHom φ := hint.isLocalHom hφ
    rcases n with _ | n
    · exfalso
      apply hp.not_isUnit
      refine isUnit_of_map_unit φ p ?_
      rw [hu]; simp
    · omega
  have hinj : Function.Injective ((algebraMap T'.V T'.Fr).comp φ) :=
    (IsFractionRing.injective T'.V T'.Fr).comp hφ
  let i : T.Fr →+* T'.Fr := IsFractionRing.lift hinj
  have hi : ∀ a, i (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (φ a) := fun a =>
    IsFractionRing.lift_algebraMap hinj a
  refine ⟨i, n, hn, hi, fun x => ?_, fun l C eF h1 h2 => ?_⟩
  · rw [vV_ext φ hφ i hi hp x, hu, vV_eq hq u.isUnit]
  · obtain ⟨g, hg, hgφ, hg1⟩ := exists_extension φ hφ hint (eF.comp (algebraMap T.V T.Fr))
      (eF.injective.comp (IsFractionRing.injective T.V T.Fr)) h1
    refine ⟨g.codRestrict (intO ↥C.S) (fun b => hg1 b), fun a b h => hg (congrArg Subtype.val h),
      fun a => hgφ a, fun a ha => ?_⟩
    change ‖g a‖ < 1
    have hp1 : ‖g (φ p)‖ < 1 := by
      rw [hgφ]
      exact h2 p ((IsLocalRing.mem_maximalIdeal p).2 hp.not_isUnit)
    have hq1 : ‖g q‖ < 1 := by
      have e : q ^ n = (u⁻¹ : T'.Vˣ) * φ p := by rw [hu, Units.inv_mul_cancel_left]
      have : ‖g q‖ ^ n < 1 := by
        rw [← norm_pow, ← map_pow, e, map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hg1 _) (norm_nonneg _) hp1
      exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
    rw [hq.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hq1 (hg1 _)

end GlobalTheory.EtaVal
