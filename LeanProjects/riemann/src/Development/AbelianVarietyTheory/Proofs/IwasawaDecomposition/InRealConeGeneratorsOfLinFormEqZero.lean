import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem inRCone_of_apply_eq_zero {X : Type} [AddCommGroup X] {m p : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (e : Fin p ↪ Fin m) (β : LinearMap.BilinForm ℤ X) (hnn : ∀ i, 0 ≤ h (δ i))
    (hz : ∀ i, h (δ i) = 0 → i ∈ Set.range e) (hβ : InRCone δ β) (hβ0 : h β = 0) :
    InRCone (fun k => δ (e k)) β := by
  obtain ⟨c, hc, hsum⟩ := hβ
  have happ := apply_eq_of_toReal_eq hsum h
  rw [hβ0, Int.cast_zero] at happ
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin m)), c i * (h (δ i) : ℝ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hnn i)).1 happ.symm
  have hvan : ∀ i, i ∉ Set.range e → c i = 0 := by
    intro i hi
    rcases mul_eq_zero.1 (hterm i (Finset.mem_univ i)) with h1 | h1
    · exact h1
    · exact absurd (hz i (by exact_mod_cast h1)) hi
  refine ⟨fun k => c (e k), fun k => hc (e k), ?_⟩
  rw [hsum, ← Finset.sum_map Finset.univ e (fun i => c i • toReal (δ i))]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have : i ∉ Set.range e := by
    rintro ⟨k, rfl⟩
    exact hi (Finset.mem_map_of_mem e (Finset.mem_univ k))
  rw [hvan i this, zero_smul]

end GlobalTheory.PolFan
