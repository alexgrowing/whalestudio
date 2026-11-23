import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Ring

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} {δ : DividedPowers J}

theorem divPowerCompatFunctionDifferential_smul (r : R) (b : B) : kd0 R δ (r • b) = r • kd0 R δ b := by
  rw [divPowerCompatFunctionDifferential_apply, divPowerCompatFunctionDifferential_apply, Derivation.map_smul, Submodule.Quotient.mk_smul]

theorem divPowerCompatOneFormDerivative_smul (r : R) (x : K1 R δ) : kd1 R δ (r • x) = r • kd1 R δ x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormDerivative_mk, divPowerCompatOneFormDerivative_mk, map_smul, Submodule.Quotient.mk_smul]

theorem divPowerCompatTwoFormDerivative_smul (r : R) (x : K R δ 2) : kd2 R δ (r • x) = r • kd2 R δ x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatTwoFormDerivative_mk, divPowerCompatTwoFormDerivative_mk, map_smul, Submodule.Quotient.mk_smul]

variable {R' B' : Type} [CommRing R'] [CommRing B'] [Algebra R' B'] {J' : Ideal B'} {δ' : DividedPowers J'}
  {σ : R →+* R'} {α : B →+* B'} (h : SemiHom σ α) (hd : IsDPMorphism δ δ' α)

theorem divPowerCompatOneFormMap_smul (r : R) (x : K1 R δ) : km1 h hd (r • x) = σ r • km1 h hd x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, map_smulₛₗ, Submodule.Quotient.mk_smul]

theorem km_smul (j : ℕ) (r : R) (x : K R δ j) : km h hd j (r • x) = σ r • km h hd j x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, km_mk, km_mk, map_smulₛₗ, Submodule.Quotient.mk_smul]

end Ring

section Site

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}

theorem crystallineCompatibleFormsComplex_functionMap_smul {T T' : Thick κ t} (φ : T ⟶ T') (r : R) (x : (KK κ t).M0.obj T) :
    (KK κ t).M0.map φ (r • x) = r • (KK κ t).M0.map φ x := map_smul (mp (O κ t) φ) r x

theorem crystallineCompatibleFormsComplex_oneFormMap_smul {T T' : Thick κ t} (φ : T ⟶ T') (r : R) (x : (KK κ t).M1.obj T) :
    (KK κ t).M1.map φ (r • x) = r • (KK κ t).M1.map φ x := divPowerCompatOneFormMap_smul (SemiHom.of_algHom φ.φ) φ.dp r x

theorem crystallineCompatibleFormsComplex_twoFormMap_smul {T T' : Thick κ t} (φ : T ⟶ T') (r : R) (x : (KK κ t).M2.obj T) :
    (KK κ t).M2.map φ (r • x) = r • (KK κ t).M2.map φ x := km_smul (SemiHom.of_algHom φ.φ) φ.dp 2 r x

theorem crystallineCompatibleFormsComplex_functionDifferential_smul (T : Thick κ t) (r : R) (x : (KK κ t).M0.obj T) :
    (KK κ t).d0 T (r • x) = r • (KK κ t).d0 T x := divPowerCompatFunctionDifferential_smul r x

theorem crystallineCompatibleFormsComplex_oneFormDifferential_smul (T : Thick κ t) (r : R) (x : (KK κ t).M1.obj T) :
    (KK κ t).d1 T (r • x) = r • (KK κ t).d1 T x := divPowerCompatOneFormDerivative_smul r x

theorem crystallineCompatibleFormsComplex_twoFormDifferential_smul (T : Thick κ t) (r : R) (x : (KK κ t).M2.obj T) :
    (KK κ t).d2 T (r • x) = r • (KK κ t).d2 T x := divPowerCompatTwoFormDerivative_smul r x

theorem crystallineCompatibleFormsComplex_totalDifferentialOne_smul (r : R) (c : (KK κ t).T1) : (KK κ t).D1 (r • c) = r • (KK κ t).D1 c := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext T T' T'' φ ψ
    show (KK κ t).M0.map ψ (r • c.1 T T' φ) - r • c.1 T T'' (φ ≫ ψ) + r • c.1 T' T'' ψ =
      r • ((KK κ t).M0.map ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ)
    rw [crystallineCompatibleFormsComplex_functionMap_smul, smul_add, smul_sub]
  · funext T T' φ
    show r • c.2 T' - (KK κ t).M1.map φ (r • c.2 T) - (KK κ t).d0 T' (r • c.1 T T' φ) =
      r • (c.2 T' - (KK κ t).M1.map φ (c.2 T) - (KK κ t).d0 T' (c.1 T T' φ))
    rw [crystallineCompatibleFormsComplex_oneFormMap_smul, crystallineCompatibleFormsComplex_functionDifferential_smul, smul_sub, smul_sub]
  · funext T
    exact crystallineCompatibleFormsComplex_oneFormDifferential_smul T r (c.2 T)

theorem crystallineCompatibleFormsComplex_cocyclesOne_smul_mem (r : R) {c : (KK κ t).T1} (hc : c ∈ (KK κ t).Z1) : r • c ∈ (KK κ t).Z1 := by
  have h0 : (KK κ t).D1 c = 0 := hc
  show (KK κ t).D1 (r • c) = 0
  rw [crystallineCompatibleFormsComplex_totalDifferentialOne_smul, h0, smul_zero]

theorem crystallineCompatibleFormsComplex_cocyclesTwo_smul_mem (r : R) {c : (KK κ t).T2} (hc : c ∈ (KK κ t).Z2) : r • c ∈ (KK κ t).Z2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  refine ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · show (KK κ t).M0.map χ (r • c.1 T T' T'' φ ψ) + r • c.1 T T'' T''' (φ ≫ ψ) χ =
      r • c.1 T T' T''' φ (ψ ≫ χ) + r • c.1 T' T'' T''' ψ χ
    rw [crystallineCompatibleFormsComplex_functionMap_smul, ← smul_add, ← smul_add, h1]
  · show r • c.2.1 T T'' (φ ≫ ψ) = (KK κ t).M1.map ψ (r • c.2.1 T T' φ) + r • c.2.1 T' T'' ψ +
      (KK κ t).d0 T'' (r • c.1 T T' T'' φ ψ)
    rw [crystallineCompatibleFormsComplex_oneFormMap_smul, crystallineCompatibleFormsComplex_functionDifferential_smul, ← smul_add, ← smul_add, h2]
  · show r • c.2.2 T' = (KK κ t).M2.map φ (r • c.2.2 T) + (KK κ t).d1 T' (r • c.2.1 T T' φ)
    rw [crystallineCompatibleFormsComplex_twoFormMap_smul, crystallineCompatibleFormsComplex_oneFormDifferential_smul, ← smul_add, h3]
  · show (KK κ t).d2 T (r • c.2.2 T) = 0
    rw [crystallineCompatibleFormsComplex_twoFormDifferential_smul, h4, smul_zero]

end Site

theorem rel_add_smul : ∀ (D : Data) (Λ : Lift D),
    (∀ a b h h', Λ.Rel1 a h → Λ.Rel1 b h' → Λ.Rel1 (a + b) (h + h')) ∧
    (∀ (r : D.R) a h, Λ.Rel1 a h → Λ.Rel1 (r • a) (r • h)) ∧
    (∀ a b h h', Λ.Rel2 a h → Λ.Rel2 b h' → Λ.Rel2 (a + b) (h + h')) ∧
    ∀ (r : D.R) a h, Λ.Rel2 a h → Λ.Rel2 (r • a) (r • h) := by
  intro D Λ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro a b h h' ⟨k, f, w, hf, hw, hk, hr⟩ ⟨k', f', w', hf', hw', hk', hr'⟩
    refine ⟨k + k', f + f', w + w', by rw [map_add, hf, hf'], by rw [map_add, hw, hw'], ?_, ?_⟩
    · show k.1.1 + k'.1.1 = f.1 + f'.1
      rw [hk, hk']
    · refine ⟨fun U V c ↦ (congrArg₂ (· + ·) (hr.1 U V c) (hr'.1 U V c)).trans (map_add (Λ.e V) _ _).symm,
        fun U ↦ (congrArg₂ (· + ·) (hr.2 U) (hr'.2 U)).trans ?_⟩
      show _ = Submodule.Quotient.mk ((Λ.semi U).m1 (w.1.2 U + w'.1.2 U))
      rw [map_add, Submodule.Quotient.mk_add]
  · rintro r a h ⟨k, f, w, hf, hw, hk, hr⟩
    refine ⟨⟨r • k.1, crystallineCompatibleFormsComplex_cocyclesOne_smul_mem r k.2⟩, r • f, r • w, by rw [map_smul, hf], by rw [map_smul, hw], ?_, ?_⟩
    · show r • k.1.1 = r • f.1
      rw [hk]
    · refine ⟨fun U V c ↦ (congrArg (r • ·) (hr.1 U V c)).trans (map_smul (Λ.e V) r _).symm,
        fun U ↦ (congrArg (r • ·) (hr.2 U)).trans ?_⟩
      show _ = Submodule.Quotient.mk ((Λ.semi U).m1 (r • w.1.2 U))
      rw [map_smulₛₗ, RingHom.id_apply, Submodule.Quotient.mk_smul]
  · rintro a b h h' ⟨k, f, w, hf, hw, hk, hr⟩ ⟨k', f', w', hf', hw', hk', hr'⟩
    refine ⟨k + k', f + f', w + w', by rw [map_add, hf, hf'], by rw [map_add, hw, hw'], ?_, ?_⟩
    · show k.1.1 + k'.1.1 = f.1 + f'.1
      rw [hk, hk']
    · refine ⟨fun U V W c d ↦ (congrArg₂ (· + ·) (hr.1 U V W c d) (hr'.1 U V W c d)).trans (map_add (Λ.e W) _ _).symm,
        fun U V c ↦ (congrArg₂ (· + ·) (hr.2.1 U V c) (hr'.2.1 U V c)).trans ?_,
        fun U ↦ (congrArg₂ (· + ·) (hr.2.2 U) (hr'.2.2 U)).trans ?_⟩
      · show _ = Submodule.Quotient.mk ((Λ.semi V).m1 (w.1.2.1 U V c + w'.1.2.1 U V c))
        rw [map_add, Submodule.Quotient.mk_add]
      · show _ = Submodule.Quotient.mk ((Λ.semi U).mOm 2 (w.1.2.2 U + w'.1.2.2 U))
        rw [map_add, Submodule.Quotient.mk_add]
  · rintro r a h ⟨k, f, w, hf, hw, hk, hr⟩
    refine ⟨⟨r • k.1, crystallineCompatibleFormsComplex_cocyclesTwo_smul_mem r k.2⟩, r • f, r • w, by rw [map_smul, hf], by rw [map_smul, hw], ?_, ?_⟩
    · show r • k.1.1 = r • f.1
      rw [hk]
    · refine ⟨fun U V W c d ↦ (congrArg (r • ·) (hr.1 U V W c d)).trans (map_smul (Λ.e W) r _).symm,
        fun U V c ↦ (congrArg (r • ·) (hr.2.1 U V c)).trans ?_,
        fun U ↦ (congrArg (r • ·) (hr.2.2 U)).trans ?_⟩
      · show _ = Submodule.Quotient.mk ((Λ.semi V).m1 (r • w.1.2.1 U V c))
        rw [map_smulₛₗ, RingHom.id_apply, Submodule.Quotient.mk_smul]
      · show _ = Submodule.Quotient.mk ((Λ.semi U).mOm 2 (r • w.1.2.2 U))
        rw [map_smulₛₗ, RingHom.id_apply, Submodule.Quotient.mk_smul]

end GlobalTheory.PDForm
