import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ClearDen

theorem exists_pow_mul_eq_val : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U : A.left.Opens), IsAffineOpen U → ∀ (r : Γ(A.left, U)) (k : (Fin g → ℂ) → ℂ), IsReg u.ex (A.left.basicOpen r) k → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ b : Γ(A.left, U), ∀ z ∈ pre u.ex (A.left.basicOpen r), val u.ex U b z = val u.ex U r z ^ N * k z := by
  intro A _ g L u U hU r k ⟨f, hf⟩
  have hloc := hU.isLocalization_basicOpen r
  obtain ⟨⟨b₀, ⟨_, n, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers r) f
  simp only at hb
  refine ⟨n, fun N hN => ⟨r ^ (N - n) * b₀, fun z hz => ?_⟩⟩
  have hzU : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U := GlobalTheory.top_le_preimage_mono _ (A.left.basicOpen_le r) hz
  have key : ∀ c : Γ(A.left, U), val u.ex (A.left.basicOpen r) (algebraMap Γ(A.left, U) Γ(A.left, A.left.basicOpen r) c) z = val u.ex U c z := by
    intro c
    exact GlobalTheory.valAt'_map _ (homOfLE (A.left.basicOpen_le r)).op c hz
  have e0 := congrArg (fun y => val u.ex (A.left.basicOpen r) y z) hb
  have e1 : val u.ex (A.left.basicOpen r) f z * val u.ex U r z ^ n = val u.ex U b₀ z := by
    rw [← key b₀, ← e0]
    unfold val
    rw [GlobalTheory.valAt'_mul]
    congr 1
    have := key (r ^ n)
    unfold val at this
    rw [this, GlobalTheory.valAt'_pow _ hzU]
  have e2 : val u.ex U (r ^ (N - n) * b₀) z = val u.ex U r z ^ (N - n) * val u.ex U b₀ z := by
    unfold val
    rw [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_pow _ hzU]
  rw [e2, ← e1, hf z hz, ← Nat.sub_add_cancel hN, pow_add, Nat.add_sub_cancel]
  ring

end GlobalTheory.ClearDen
