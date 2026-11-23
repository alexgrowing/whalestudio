import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallCompleteDvrDominating
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialDataStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Arith

theorem idlAlong_monomial : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (φ : InvFun ℤ)
    (J : Z.IdealSheafData) (d : ℕ), ValOn F i φ J d →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : ℕ) (ga δ : Fin m → LinearMap.BilinForm ℤ X)
      (M : ℕ), IsCone id φ ga → (∀ k, δ k = (M : ℤ) • ga k) → ∀ b : Fin m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ (δ k)) →
    ∀ (T : Trait F) (W : Type) [CommRing W] [IsLocalRing W] (σ : W →+* T.V) (c : Fin m → ℕ) (e' : T.D.toPre.X ≃+ X)
      (x : Sp W ⟶ Z) (s : Fin m → W), Function.Bijective σ → jK T.V ≫ spMap σ ≫ x = T.y ≫ i →
      (∀ k, Associated (σ (s k)) (T.ϖ ^ c k)) → (∀ a b, T.β a b = ∑ k, (c k : ℤ) * δ k (e' a) (e' b)) →
      idlAlong J x = Ideal.span {∏ k, s k ^ b k} := by
  intro o _ ζ g n F Z i φ J d hV X _ _ _ m ga δ M hcone hδ b hb T W _ _ σ c e' x s hσ hcomm hs hβ
  obtain ⟨a, ha, hid⟩ := hV T (spMap σ ≫ x) hcomm
  rw [GlobalTheory.TraitOrder.idlAlong_comp] at hid
  have hlin : φ.LinearOn δ := by
    have := hcone.linearOn_smul M
    rwa [show δ = fun k => (M : ℤ) • ga k from funext hδ]
  have hev : φ.evalZ T.β = ∑ k, (c k : ℝ) * φ.evalZ (δ k) := by
    refine InvFun.LinearOn.eval_eq_sum (X := X) hlin (r := e'.symm.toIntLinearEquiv.toLinearMap)
      e'.symm.surjective (fun k => Nat.cast_nonneg _) ?_
    intro u v
    simp [hβ]
  have haN : a = ∑ k, c k * b k := by
    have : (a : ℝ) = ∑ k, (c k : ℝ) * b k := by
      rw [ha, hev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb k]; ring
    exact_mod_cast this
  have hassoc : Associated (∏ k, σ (s k) ^ b k) (T.ϖ ^ a) := by
    rw [haN, ← Finset.prod_pow_eq_pow_sum]
    refine Associated.prod _ _ _ fun k _ => ?_
    rw [pow_mul]
    exact (hs k).pow_pow
  have hmap : (idlAlong J x).map σ = (Ideal.span {∏ k, s k ^ b k}).map σ := by
    rw [hid, Ideal.map_span, Set.image_singleton, map_prod]
    simp only [map_pow]
    exact (Ideal.span_singleton_eq_span_singleton.2 hassoc).symm
  rw [← Ideal.comap_map_of_bijective σ hσ (I := idlAlong J x), hmap, Ideal.comap_map_of_bijective σ hσ]

end GlobalTheory.Poinc.Arith
