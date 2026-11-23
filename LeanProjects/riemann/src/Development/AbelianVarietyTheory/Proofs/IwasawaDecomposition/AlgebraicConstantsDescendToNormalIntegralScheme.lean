import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstDescent

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Cartier

theorem exists_fnOf_eq_of_algebraic {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp F) (U : X.Opens) (hU : genericPoint X ∈ U)
    {a : X.functionField} (ha : ∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (Cartier.constFn p) a = 0) :
    ∃ s : Γ(X, U), fnOf U hU s = a := by
  haveI : Nonempty U := ⟨⟨_, hU⟩⟩
  letI := (algX p U).toAlgebra
  letI : Algebra F X.functionField := (Cartier.constFn p).toAlgebra
  haveI : IsScalarTower F Γ(X, U) X.functionField :=
    IsScalarTower.of_algebraMap_eq' (fnOf_comp_algX p U hU).symm
  obtain ⟨P, hP, hPa⟩ := ha
  have hint : IsIntegral F a := (show IsAlgebraic F a from
    ⟨P, hP, by rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]; exact hPa⟩).isIntegral
  obtain ⟨s, hs⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := Γ(X, U))
    (A := X.functionField)).1 hint.tower_top
  exact ⟨s, hs⟩

theorem appLE_comp_algX {F : Type} [CommRing F] {W V : Scheme.{0}} (pW : W ⟶ Sp F) (π : V ⟶ W) :
    (π.appLE ⊤ ⊤ le_top).hom.comp (algX pW ⊤) = algX (π ≫ pW) ⊤ := by
  have e := Scheme.Hom.appLE_comp_appLE π pW ⊤ ⊤ ⊤ le_top le_top
  exact congrArg (fun f => (CommRingCat.Hom.hom f).comp
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom) e

theorem descent : ∀ (F : Type) [Field F] (W V : Scheme.{0}) [IsIntegral W] [IsIntegral V]
    [GlobalTheory.IsNormalScheme W] (pW : W ⟶ Sp F) (pV : V ⟶ Sp F) (π : V ⟶ W), π ≫ pW = pV →
    (∀ b : V.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pV) b = 0) →
      b ∈ (GlobalTheory.Cartier.constFn pV).range) →
    ∀ a : W.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pW) a = 0) →
      a ∈ (GlobalTheory.Cartier.constFn pW).range := by
  intro F _ W V _ _ _ pW pV π hπ hV a ha
  subst hπ
  have hW : genericPoint W ∈ (⊤ : W.Opens) := trivial
  have hV' : genericPoint V ∈ (⊤ : V.Opens) := trivial

  let φ : Γ(W, ⊤) →+* V.functionField := (fnOf ⊤ hV').comp (π.appLE ⊤ ⊤ le_top).hom
  have hφ : φ.comp (algX pW ⊤) = Cartier.constFn (π ≫ pW) := by
    simp only [φ, RingHom.comp_assoc, appLE_comp_algX]
    rfl
  obtain ⟨s, hs⟩ := exists_fnOf_eq_of_algebraic pW ⊤ hW ha
  obtain ⟨P, hP, hPa⟩ := ha
  have h0 : P.eval₂ (algX pW ⊤) s = 0 := fnOf_injective ⊤ trivial (by
    rw [Polynomial.hom_eval₂, fnOf_comp_algX pW ⊤ hW, hs, hPa, map_zero])
  have hb : P.eval₂ (Cartier.constFn (π ≫ pW)) (φ s) = 0 := by
    rw [← hφ, ← Polynomial.hom_eval₂, h0, map_zero]
  obtain ⟨c, hc⟩ := hV _ ⟨P, hP, hb⟩
  refine ⟨c, ?_⟩
  by_contra hne
  have hne' : a - Cartier.constFn pW c ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have ht : fnOf ⊤ hW (s - algX pW ⊤ c) = a - Cartier.constFn pW c := by
    rw [map_sub, hs, ← fnOf_comp_algX pW ⊤ hW, RingHom.comp_apply]
  have hφt : φ (s - algX pW ⊤ c) = 0 := by
    rw [map_sub, ← RingHom.comp_apply φ, hφ, hc, sub_self]
  have hinv : ∃ Q : Polynomial F, Q ≠ 0 ∧ Q.eval₂ (Cartier.constFn pW) (a - Cartier.constFn pW c)⁻¹ = 0 := by
    letI : Algebra F W.functionField := (Cartier.constFn pW).toAlgebra
    have h1 : IsAlgebraic F a :=
      ⟨P, hP, by rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]; exact hPa⟩
    have h2 : IsAlgebraic F (a - Cartier.constFn pW c) :=
      h1.sub (isAlgebraic_algebraMap (A := W.functionField) c)
    obtain ⟨Q, hQ, hQx⟩ := h2.inv
    exact ⟨Q, hQ, by rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] at hQx; exact hQx⟩
  obtain ⟨u, hu⟩ := exists_fnOf_eq_of_algebraic pW ⊤ hW hinv
  have htu : (s - algX pW ⊤ c) * u = 1 := fnOf_injective ⊤ trivial (by
    rw [map_mul, ht, hu, map_one, mul_inv_cancel₀ hne'])
  have h3 := congrArg φ htu
  rw [map_mul, hφt, zero_mul, map_one] at h3
  exact zero_ne_one h3

end GlobalTheory.ConstDescent
