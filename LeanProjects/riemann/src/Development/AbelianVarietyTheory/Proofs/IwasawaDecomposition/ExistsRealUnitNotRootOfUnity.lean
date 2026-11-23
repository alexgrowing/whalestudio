import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

open NumberField.Units IsCMField in

theorem exists_real_unit_infinite_order (E : Type) [Field E] [NumberField E] [IsCMField E]
    (hE : 1 < Module.finrank ℚ E / 2) :
    ∃ u : (𝓞 E)ˣ, cc (u : E) = u ∧ ∀ n : ℕ, 0 < n → (u : E) ^ n ≠ 1 := by
  have hrank : 0 < rank E := by
    have h1 := IsTotallyComplex.finrank (K := E)
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
    have h3 := IsTotallyComplex.nrRealPlaces_eq_zero (K := E)
    unfold rank
    omega
  let i : Fin (rank E) := ⟨0, hrank⟩
  refine ⟨realFundSystem E i, ?_, ?_⟩
  · simp only [realFundSystem, cc]
    exact complexConj_apply_eq_self E _
  · intro n hn hpow
    set v := fundSystem (maximalRealSubfield E) (finCongr (units_rank_eq_units_rank E).symm i)
    have hv : v ^ n = 1 := by
      have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) E) :=
        (FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) E)
      apply Units.ext
      apply hinj
      rw [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one,
        IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (𝓞 E) E]
      exact hpow
    have htor : v ∈ torsion (maximalRealSubfield E) := (CommGroup.mem_torsion _).mpr
      ((isOfFinOrder_iff_pow_eq_one).mpr ⟨n, hn, hv⟩)
    have hmk := fundSystem_mk (maximalRealSubfield E) (finCongr (units_rank_eq_units_rank E).symm i)
    rw [(QuotientGroup.eq_one_iff _).mpr htor] at hmk
    exact (basisModTorsion (maximalRealSubfield E)).ne_zero _ hmk.symm

end GlobalTheory.UnipKill
