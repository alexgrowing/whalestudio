import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartTransportSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Ring

variable {V K : Type} [CommRing V] [CommRing K] (f : V →+* K)

theorem jetCoef_mk (κ : Type) (m : ℕ) (p : MvPolynomial κ V) :
    jetCoef f κ m (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl

theorem psTrunc_map {σ : Type} [Fintype σ] [DecidableEq σ] (m : ℕ) (F : MvPowerSeries σ V) :
    psTrunc m (MvPowerSeries.map f F) = MvPolynomial.map f (psTrunc m F) := by
  simp only [psTrunc, map_sum, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem jetCoef_alg (κ : Type) (m : ℕ) :
    (jetCoef f κ m).comp (algebraMap V (Jet V κ m)) = (algebraMap K (Jet K κ m)).comp f := by
  refine RingHom.ext fun v => ?_
  first
  | (show jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.C v)) = Ideal.Quotient.mk _ (MvPolynomial.C (f v))
     rw [jetCoef_mk, MvPolynomial.map_C])
  | (simp only [RingHom.comp_apply]
     rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq,
       MvPolynomial.algebraMap_eq, jetCoef_mk, MvPolynomial.map_C])

theorem jetCoef_aug (κ : Type) (m : ℕ) :
    ((jetAug : Jet K κ m →ₐ[K] K) : Jet K κ m →+* K).comp (jetCoef f κ m) =
      f.comp ((jetAug : Jet V κ m →ₐ[V] V) : Jet V κ m →+* V) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_))
  · show (jetAug : Jet K κ m →ₐ[K] K) (jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.C a))) =
      f ((jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.C a)))
    rw [jetCoef_mk, MvPolynomial.map_C]
    show (MvPolynomial.aeval fun _ => (0 : K)) (MvPolynomial.C (f a)) =
      f ((MvPolynomial.aeval fun _ => (0 : V)) (MvPolynomial.C a))
    simp
  · show (jetAug : Jet K κ m →ₐ[K] K) (jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
      f ((jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)))
    rw [jetCoef_mk, MvPolynomial.map_X]
    show (MvPolynomial.aeval fun _ => (0 : K)) (MvPolynomial.X i) =
      f ((MvPolynomial.aeval fun _ => (0 : V)) (MvPolynomial.X i))
    simp

theorem jetCoef_trunc (κ : Type) (m : ℕ) :
    ((jetTrunc : Jet K κ (m + 1) →ₐ[K] Jet K κ m) : Jet K κ (m + 1) →+* Jet K κ m).comp (jetCoef f κ (m + 1)) =
      (jetCoef f κ m).comp ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p => ?_)
  first
  | rfl
  | simp [jetCoef_mk, jetTrunc]

theorem jetCoef_map {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' V) (hφ : ∀ i, φ i ∈ orig V κ')
    (hφ' : ∀ i, MvPolynomial.map f (φ i) ∈ orig K κ') :
    (jetCoef f κ' m).comp ((jetMap φ hφ : Jet V κ m →ₐ[V] Jet V κ' m) : Jet V κ m →+* Jet V κ' m) =
      ((jetMap (fun i => MvPolynomial.map f (φ i)) hφ' : Jet K κ m →ₐ[K] Jet K κ' m) : Jet K κ m →+* Jet K κ' m).comp
        (jetCoef f κ m) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_))
  · show jetCoef f κ' m (Ideal.Quotient.mk _ ((MvPolynomial.aeval φ) (MvPolynomial.C a))) =
      Ideal.Quotient.mk _ ((MvPolynomial.aeval fun i => MvPolynomial.map f (φ i))
        (MvPolynomial.map f (MvPolynomial.C a)))
    rw [jetCoef_mk]
    simp
  · show jetCoef f κ' m (Ideal.Quotient.mk _ ((MvPolynomial.aeval φ) (MvPolynomial.X i))) =
      Ideal.Quotient.mk _ ((MvPolynomial.aeval fun i => MvPolynomial.map f (φ i))
        (MvPolynomial.map f (MvPolynomial.X i)))
    rw [jetCoef_mk]
    simp

end Ring

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
