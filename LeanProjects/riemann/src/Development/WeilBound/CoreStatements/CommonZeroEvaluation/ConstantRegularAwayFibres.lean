import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk

open AlgebraicGeometry CategoryTheory
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace ModelDimension

theorem mem_regAt_of_over {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {R : Type} [CommRing R] (g : X ⟶ Spec (CommRingCat.of R)) (φ : R →+* Ω)
    (h : ξ ≫ g = Spec.map (CommRingCat.ofHom φ)) (q : Cpt ξ) (r : R) : φ r ∈ regAt ξ q := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.fromSpecStalk q.1 ≫ g)
  have h1 : Spec.map (ψ ≫ CommRingCat.ofHom (genMap ξ q)) = Spec.map (CommRingCat.ofHom φ) :=
    (Spec.map_comp _ _).trans ((congrArg (Spec.map (CommRingCat.ofHom (genMap ξ q)) ≫ ·) hψ).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) (LieCarrier.genMap_fromSpecStalk q)).trans h)))
  have h2 := Spec.map_injective h1
  exact ⟨ψ.hom r, congrArg (fun t => t.hom r) h2⟩

theorem inv_natCast_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (q : Cpt ξ) (hq : ∀ p : ℕ, p.Prime → ¬ InFibre ξ p q) (n : ℕ) : ((n : Ω))⁻¹ ∈ regAt ξ q := by
  induction n using Nat.recOnMul with
  | zero => simp
  | one => simp
  | prime p hp => exact (not_not.1 (hq p hp)).2.2
  | mul a b ha hb => rw [Nat.cast_mul, mul_inv]; exact mul_mem ha hb

theorem constant_regular_away_fibres : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (q : Cpt 𝔐.ξ), (∀ p : ℕ, p.Prime → ¬ InFibre 𝔐.ξ p q) → ∀ a : c.F, 𝔐.cst a ∈ regAt 𝔐.ξ q := by
  intro E _ _ _ H Dw l Xo c Y S Ω _ K _ J y 𝔐 q hq a
  have hfin := c.fin
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a)
  obtain ⟨n, o, hn, ho⟩ := halg.exists_nsmul_eq (𝓞 c.F)
  have h1 : 𝔐.cst (algebraMap (𝓞 c.F) c.F o) ∈ regAt 𝔐.ξ q :=
    mem_regAt_of_over (𝔐.f ≫ Y.s) (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) 𝔐.cst_over q o
  have h0 : (n : Ω) ≠ 0 := by
    rw [← map_natCast 𝔐.cst]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn)
  have h2 : 𝔐.cst a = (n : Ω)⁻¹ * 𝔐.cst (algebraMap (𝓞 c.F) c.F o) := by
    rw [← ho, nsmul_eq_mul, map_mul, map_natCast, inv_mul_cancel_left₀ h0]
  rw [h2]
  exact mul_mem (inv_natCast_mem_regAt q hq n) h1

end ModelDimension
