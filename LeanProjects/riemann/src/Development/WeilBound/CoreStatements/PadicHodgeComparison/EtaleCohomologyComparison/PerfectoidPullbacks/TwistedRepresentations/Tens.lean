import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup

noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.Tw

variable {W : Type} [CommRing W]

structure LSeq (l : ℕ) (S S' : Sys.{1} W) where
  ρ : ∀ c b, S.M c →ₗ[W] S.M b
  ν : ∀ a c, S.M a →ₗ[W] S.M c
  δ : ∀ b a, S.M b →ₗ[W] S'.M a
  kill : ∀ n (x : S.M n), ((l : W) ^ n) • x = 0
  ρ_self : ∀ c x, ρ c c x = x
  ρ_succ : ∀ c b, b ≤ c → ∀ x, ρ (c + 1) b x = ρ c b (S.r c x)
  ν_ρ : ∀ a c, a ≤ c → ∀ x, ν a c (ρ c a x) = ((l : W) ^ (c - a)) • x
  ν_r : ∀ a c, a ≤ c → ∀ y, S.r c (ν (a + 1) (c + 1) y) = ν a c (S.r a y)
  ex₁ : ∀ a b c, c = a + b → ∀ x, ρ c b x = 0 → ∃ y, ν a c y = x
  δ_r : ∀ b a x, S'.r a (δ b (a + 1) x) = δ b a x
  ex₂ : ∀ a b c, c = a + b → ∀ x, δ b a x = 0 → ∃ y, ρ c b y = x

def pr (S : Sys.{1} W) (n : ℕ) : S.lim →ₗ[W] S.M n := (LinearMap.proj n).comp S.lim.subtype

def tens (A : Type) [CommRing A] [Algebra W A] (S : Sys.{1} W) : Sys.{1} A where
  M n := A ⊗[W] S.M n
  r n := (S.r n).baseChange A

end CrystallineSemistableComparison.Tw

end
