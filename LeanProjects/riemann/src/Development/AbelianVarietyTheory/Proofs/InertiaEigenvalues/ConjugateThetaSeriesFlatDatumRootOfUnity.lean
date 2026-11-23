import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesTwistedThetaSeriesConjugateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeChoiceFlatScalarConjTwistStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTranslatedDatumAtTranslatedClassStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

namespace GlobalTheory.ConjTwist.FlatSeries

theorem scale {X B : Type} (J : B → X → ℂ) (τ : ℂ ≃+* ℂ) (ζ η C C' : ℂ) (Φ Φ' : X → ℂ)
    (h1 : ∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), ∀ g, Φ g = ∑ k, a k * J (f k) g)
    (h2 : ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), (∀ g, Φ g = ∑ k, a k * J (f k) g) →
      ∀ g, Φ' g = ∑ k, ζ * τ (a k) * J (f k) g)
    (hC : C' = η * τ C) :
    (∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), ∀ g, C * Φ g = ∑ k, a k * J (f k) g) ∧
      ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), (∀ g, C * Φ g = ∑ k, a k * J (f k) g) →
        ∀ g, C' * Φ' g = ∑ k, ζ * η * τ (a k) * J (f k) g := by
  refine ⟨?_, ?_⟩
  · obtain ⟨n, a, f, h⟩ := h1
    refine ⟨n, fun k => C * a k, f, fun g => ?_⟩
    rw [h g, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · intro n a f ha g
    by_cases hC0 : C = 0
    · subst hC0
      obtain ⟨n₀, b, e, hb⟩ := h1
      have hC' : C' = 0 := by simp [hC]
      have hz : ∀ g, ∑ k, a k * J (f k) g = 0 := fun g => by simpa using (ha g).symm
      have hcat : ∀ g, Φ g = ∑ k, (Fin.append b a) k * J ((Fin.append e f) k) g := fun g => by
        rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right]
        rw [hz g, add_zero, hb g]
      have e1 := h2 _ _ _ hcat g
      have e2 := h2 _ _ _ hb g
      rw [Fin.sum_univ_add] at e1
      simp only [Fin.append_left, Fin.append_right] at e1
      rw [e2] at e1
      have e3 : ∑ k, ζ * τ (a k) * J (f k) g = 0 := by simpa using e1.symm
      have e4 : ∑ k, ζ * η * τ (a k) * J (f k) g = η * ∑ k, ζ * τ (a k) * J (f k) g := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e4, e3, hC']
      simp
    · have hτ : τ C ≠ 0 := fun h => hC0 ((map_eq_zero_iff τ τ.injective).1 h)
      have hexp : ∀ g, Φ g = ∑ k, (C⁻¹ * a k) * J (f k) g := fun g => by
        have : Φ g = C⁻¹ * (C * Φ g) := by field_simp
        rw [this, ha g, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [h2 _ _ _ hexp g, hC, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_inv₀]
      field_simp

end GlobalTheory.ConjTwist.FlatSeries

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem GlobalTheory.ConjTwist.FlatSeries.conjFun_scale (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) {ζ η C C' : ℂ}
    {Φ Φ' : GA D (Wc D i) → ℂ} (h : ConjFun O κ τ ζ Φ Φ') (hC : C' = η * τ C) :
    ConjFun O κ τ (ζ * η) (fun g => C * Φ g) (fun g => C' * Φ' g) := by
  have key := GlobalTheory.ConjTwist.FlatSeries.scale
    (fun (b : T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) (g : GA D (Wc D i)) =>
      ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
        O.phi (T.cE ((i : ℕ) + 1) O.s0) (b : T.toCore.R ((i : ℕ) + 1)) g))
    τ ζ η C C' Φ Φ' h.1 (fun n a f ha g => h.2 n a f ha g) hC
  exact ⟨key.1, fun n a f ha g => key.2 n a f ha g⟩
end

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.ConjTwist.FlatSeries.conj_flat_series : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * ser R i t f u h (c x) g) (fun g => ph i * ser R i t' f' u h (c x') g) := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hn hCore hT0 hFW hIo hQ i hPins hPh cc hcc u hu τ hFix
  obtain ⟨ζ0, hζ0, hser⟩ := GlobalTheory.T.conjugate_tuples_twisted_thetaSeries_conjugate hCI D G Pl0 T0 A T R F κ v₀ O ph hn hCore hT0 hFW hIo hQ i hPins hPh cc hcc u hu τ hFix
  refine ⟨ζ0, hζ0, fun t t' hConj f f' hf hf' => ?_⟩
  obtain ⟨s, hs⟩ := hser t t' hConj
  obtain ⟨z, C, C', s₂, hz, rfl, rfl, hC⟩ :=
    GlobalTheory.T.heckeChoice_flatScalar_conj_twist D G Pl0 T0 A T R F κ v₀ hCore hQ i τ t t' hPins.2.lift.std hFix hConj f f' hf hf'
  refine ⟨s * s₂, fun h hh x x' hx => ?_⟩
  have hzG : z ∈ GfC (Vc D i) := hz.2.1
  have base := hs (h * z) ((GfC (Vc D i)).mul_mem hh hzG) x x' hx
  have sc := GlobalTheory.ConjTwist.FlatSeries.conjFun_scale (O i) (κ i) τ base hC
  have e1 : (fun g => ph i * ser R i t (C • R.ωP i t (z, 1) (R.vP i t)) u h (cc x) g) =
      fun g => C * (ph i * ser R i t (R.vP i t) u (h * z) (cc x) g) := funext fun g => by
    rw [GlobalTheory.T.thetaSeries_translated_datum_at_translated_class D G Pl0 T0 A T.Q.c.F R F hCore i t z C hzG u h (cc x) g]
    ring
  have e2 : (fun g => ph i * ser R i t' (C' • R.ωP i t' (z, 1) (R.vP i t')) u h (cc x') g) =
      fun g => C' * (ph i * ser R i t' (R.vP i t') u (h * z) (cc x') g) := funext fun g => by
    rw [GlobalTheory.T.thetaSeries_translated_datum_at_translated_class D G Pl0 T0 A T.Q.c.F R F hCore i t' z C' hzG u h (cc x') g]
    ring
  rw [e1, e2]
  have e3 : ζ0 * ((R.xi t' (s * s₂) : Circle) : ℂ) = ζ0 * ((R.xi t' s : Circle) : ℂ) * ((R.xi t' s₂ : Circle) : ℂ) := by
    rw [map_mul, Circle.coe_mul, mul_assoc]
  rw [e3]
  exact sc
