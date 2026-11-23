import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulEqRegularValueBasicOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularPeriodicRatioCoverFamiliesStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isReg_of_isReg_sub : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (n : ℕ) (W : Fin n → A.left.Opens) (r : ∀ k, Fin n → Γ(A.left, W k)), IsRatioCover u.ex W r → ∀ (h : Fin n → (Fin g → ℂ) → ℂ), (∀ k, DifferentiableOn ℂ (h k) (pre u.ex (W k))) → (∀ k (l : u.Λ), ∀ z ∈ pre u.ex (W k), h k (z + l) = h k z) → (∀ k j, IsReg u.ex (W k ⊓ W j) (h k - h j)) → ∀ k, IsReg u.ex (W k) (h k) := by
  intro A _ g L u hA n W r hr h hd hp hreg l
  obtain ⟨-, hdiff, -, hper, hinf, -, -, -, -, -, hbas, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have hr' := hr
  obtain ⟨haff, -, hbo, -, hco⟩ := hr'
  have h1 : ∀ k, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ b : Γ(A.left, W k), ∀ z ∈ pre u.ex (A.left.basicOpen (r k l)),
      val u.ex (W k) b z = val u.ex (W k) (r k l) z ^ N * (h k - h l) z := fun k ↦
    GlobalTheory.T.exists_pow_mul_eq_regularValue_basicOpen A g L u (W k) (haff k) (r k l) (h k - h l) (by rw [hbo]; exact hreg k l)
  choose N₀ hN₀ using h1
  set N : ℕ := Finset.univ.sup N₀ with hN
  have h2 := fun k ↦ hN₀ k N (Finset.le_sup (f := N₀) (Finset.mem_univ k))
  choose b hb using h2
  let σ : Fin n → (Fin g → ℂ) → ℂ := fun k z ↦
    val u.ex (W k) (r k l) z * (val u.ex (W k) (r k l) z ^ N * h k z - val u.ex (W k) (b k) z)
  have hin : ∀ k z, z ∈ pre u.ex (W k) → z ∈ pre u.ex (W l) → σ k z = val u.ex (W k) (r k l) z ^ (N + 1) * h l z := by
    intro k z hk hl
    have hz : z ∈ pre u.ex (A.left.basicOpen (r k l)) := by rw [hbo, hinf]; exact ⟨hk, hl⟩
    simp only [σ]
    rw [hb k z hz, Pi.sub_apply]
    ring
  have hout : ∀ k z, z ∉ pre u.ex (W l) → σ k z = 0 := by
    intro k z hl
    have hz : z ∉ pre u.ex (A.left.basicOpen (r k l)) := by rw [hbo, hinf]; exact fun hz ↦ hl hz.2
    rw [hbas, not_not] at hz
    simp only [σ]
    rw [hz, zero_mul]
  have hσ := GlobalTheory.T.isRegular_periodic_ratioCover_families A g L u hA n W r hr (N + 1) σ
    (fun k ↦ (hdiff _ (r k l)).mul ((((hdiff _ (r k l)).pow N).mul (hd k)).sub (hdiff _ (b k))))
    (fun k m z hz ↦ by simp only [σ]; rw [hper, hper, hp k m z hz])
    (fun k j z hk hj ↦ by
      by_cases hl : z ∈ pre u.ex (W l)
      · rw [hin k z hk hl, hin j z hj hl, hco k j l z hk hj]
        ring
      · rw [hout k z hl, hout j z hl, mul_zero]) l
  obtain ⟨c, hc⟩ := hσ
  refine ⟨c, fun z hz ↦ ?_⟩
  have hne : val u.ex (W l) (r l l) z ≠ 0 := by
    rw [← hbas, hbo, hinf]; exact ⟨hz, hz⟩
  have hone : val u.ex (W l) (r l l) z = 1 :=
    (mul_right_cancel₀ hne ((_root_.one_mul _).trans (hco l l l z hz hz))).symm
  rw [← hc z hz, hin l z hz hz, hone, one_pow, _root_.one_mul]

end GlobalTheory.CechPer
