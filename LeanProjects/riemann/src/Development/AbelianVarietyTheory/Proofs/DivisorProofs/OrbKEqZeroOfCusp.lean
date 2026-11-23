import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbUEqZeroOfCusp

noncomputable section

open MeasureTheory Matrix
open scoped Classical

namespace GlobalTheory.OrbDesc

theorem orbK_eq_twOrbU {G : Type} [Group G] (K0 : Subgroup G) (γ : G) (f : G → ℂ)
    (hbi : ∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) :
    GlobalTheory.LKCount.orbK (MonoidHom.id G) K0 γ f =
      GlobalTheory.LKLoc.twOrbU (MonoidHom.id G) K0 γ (GlobalTheory.BCT.twCent (MonoidHom.id G) γ ⊓ K0) f := by
  unfold GlobalTheory.LKCount.orbK GlobalTheory.LKCount.orbC GlobalTheory.LKLoc.twOrbU GlobalTheory.LKLoc.orbSum
  refine finsum_congr fun q => ?_
  have hc : (fun k : K0 => f ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k))) =
      fun _ => f ((Quotient.out q)⁻¹ * γ * Quotient.out q) := by
    funext k
    have := hbi (k : G)⁻¹ (K0.inv_mem k.2) k k.2 ((Quotient.out q)⁻¹ * γ * Quotient.out q)
    rw [← this]
    simp only [MonoidHom.id_apply, _root_.mul_inv_rev, mul_assoc]
  rw [hc, avg_const']
  simp only [MonoidHom.id_apply, GlobalTheory.LKCount.vol, GlobalTheory.LKLoc.volRat, GlobalTheory.LKLoc.locPart]
  congr 1
  push_cast
  rw [inv_div]

end GlobalTheory.OrbDesc

namespace GlobalTheory.LKCount

theorem orbK_eq_zero_of_cusp : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (f : GL ι K → ℂ), IsLocallyConstant f → HasCompactSupport f →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) →
  ∀ γ : GL ι K, (γ : Matrix ι ι K).charpoly.Separable → ¬ Irreducible (γ : Matrix ι ι K).charpoly →
  ∀ (K0 : Subgroup (GL ι K)), IsOpen (K0 : Set (GL ι K)) → IsCompact (K0 : Set (GL ι K)) →
    (∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) →
    GlobalTheory.LKCount.orbK (MonoidHom.id (GL ι K)) K0 γ f = 0 := by
  intro K _ _ _ _ _ _ ι _ _ _ f hlc hcs hyp γ hsep hirr K0 hK0o hK0c hbi
  rw [GlobalTheory.OrbDesc.orbK_eq_twOrbU K0 γ f hbi]
  exact GlobalTheory.OrbDesc.twOrbU_eq_zero_of_cusp K ι f hlc hcs hyp γ hsep hirr K0 K0 hK0o hK0c hK0o hK0c hbi

end GlobalTheory.LKCount
