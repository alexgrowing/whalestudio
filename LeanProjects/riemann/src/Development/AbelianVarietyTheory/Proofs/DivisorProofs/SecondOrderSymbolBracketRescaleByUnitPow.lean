import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem bracket_symbol_rescale_twist : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (δ₀ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Λ : Matrix (Fin n) (Fin n) (FractionRing Ω)) (q b c : FractionRing Ω) (k : ℕ), q ≠ 0 → (k : FractionRing Ω) * (q ^ k * b) * ((q ^ k * b) * δ₀ (q ^ k * c) - (q ^ k * c) * δ₀ (q ^ k * b)) - ∑ a, ∑ e, Λ a e * δL a (q ^ k * b) * ((q ^ k * b) * δL e (q ^ k * c) - (q ^ k * c) * δL e (q ^ k * b)) = q ^ (3 * k) * ((k : FractionRing Ω) * b * (b * (δ₀ c - ∑ a, ∑ e, Λ a e * δL a q / q * δL e c) - c * (δ₀ b - ∑ a, ∑ e, Λ a e * δL a q / q * δL e b)) - ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b)) := by
  intro Ω _ _ n δ₀ δL Λ q b c k hq
  have hpow : ∀ (d : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (x : FractionRing Ω),
      d (q ^ k * x) = q ^ k * (d x + (k : FractionRing Ω) * x * (d q / q)) := by
    intro d x
    rw [Derivation.leibniz, Derivation.leibniz_pow]
    cases k with
    | zero => simp
    | succ k =>
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
      field_simp
      ring
  have hbr : ∀ d : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      (q ^ k * b) * d (q ^ k * c) - (q ^ k * c) * d (q ^ k * b)
        = q ^ k * q ^ k * (b * d c - c * d b) := by
    intro d
    rw [hpow d b, hpow d c]
    ring
  have h3 : q ^ (3 * k) = q ^ k * q ^ k * q ^ k := by ring
  simp only [hbr]
  simp only [hpow _ b]
  have hs : ∑ a, ∑ e, Λ a e * (q ^ k * (δL a b + (k : FractionRing Ω) * b * (δL a q / q))) *
        (q ^ k * q ^ k * (b * δL e c - c * δL e b))
      = q ^ k * q ^ k * q ^ k * ((k : FractionRing Ω) * b *
          (b * (∑ a, ∑ e, Λ a e * δL a q / q * δL e c)
            - c * (∑ a, ∑ e, Λ a e * δL a q / q * δL e b))
          + ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [hs, h3]
  ring

end GlobalTheory.Heat
