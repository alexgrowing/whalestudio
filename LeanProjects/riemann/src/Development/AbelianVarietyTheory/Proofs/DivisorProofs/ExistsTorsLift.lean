import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateCondCongr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.TateTransportAlg

theorem exists_torsLift {G H : Type} [Group G] [Group H] (p : ℕ) (ρ : G →* H)
    (hi : ∀ n, 0 < n → n.Coprime p → ∀ g h : G, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h) :
    ∃ L : H → G, ∀ n, 0 < n → n.Coprime p → ∀ g : G, g ^ n = 1 → L (ρ g) = g := by
  classical
  refine ⟨fun x => if h : ∃ g : G, (∃ n, 0 < n ∧ n.Coprime p ∧ g ^ n = 1) ∧ ρ g = x then h.choose else 1, ?_⟩
  intro n hn hnp g hg
  have h : ∃ g' : G, (∃ n, 0 < n ∧ n.Coprime p ∧ g' ^ n = 1) ∧ ρ g' = ρ g := ⟨g, ⟨n, hn, hnp, hg⟩, rfl⟩
  simp only [dif_pos h]
  obtain ⟨⟨m, hm, hmp, hgm⟩, he⟩ := h.choose_spec
  exact hi (m * n) (Nat.mul_pos hm hn) (Nat.Coprime.mul hmp hnp) _ _
    (by rw [pow_mul, hgm, one_pow]) (by rw [mul_comm, pow_mul, hg, one_pow]) he

end GlobalTheory.TateTransportAlg
