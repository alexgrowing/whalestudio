import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinity

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.Corev.UnrPow

theorem exists_pow_unrAt : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L),
    ∃ N : ℕ, 0 < N ∧ ∀ v : HeightOneSpectrum (𝓞 L), (χ ^ N).UnrAt v := by
  intro L _ _ χ
  obtain ⟨hfin, hlev⟩ := GlobalTheory.Mem.UnrAe.unr_ae_and_level L χ
  have hm : ∀ v, ∃ m : ℕ, 0 < m ∧ ∀ x, IsUnitAt v x → χ.loc v x ^ m = 1 := by
    intro v
    obtain ⟨n, hn⟩ := hlev v
    obtain ⟨m, hm, hx⟩ := GlobalTheory.Mem.FinOrder.exists_pow_congr v n
    refine ⟨m, hm, fun x hu => ?_⟩
    rw [← map_pow]
    exact hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hu m) (hx x hu)
  choose m hm0 hm using hm
  refine ⟨∏ v ∈ hfin.toFinset, m v, Finset.prod_pos fun v _ => hm0 v, fun v x hx => ?_⟩
  show χ.loc v x ^ (∏ v ∈ hfin.toFinset, m v) = 1
  by_cases hv : χ.UnrAt v
  · rw [hv x hx, one_pow]
  · obtain ⟨d, hd⟩ : m v ∣ ∏ v ∈ hfin.toFinset, m v := Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 hv)
    rw [hd, pow_mul, hm v x hx, one_pow]

end GlobalTheory.Corev.UnrPow
