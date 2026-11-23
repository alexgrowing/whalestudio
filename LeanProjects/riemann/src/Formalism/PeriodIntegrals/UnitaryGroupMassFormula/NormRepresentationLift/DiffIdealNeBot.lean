import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem diffIdeal_ne_bot (D : D7) :
    Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ≠ ⊥ := by
  have h0 : differentIdeal ℤ (𝓞 D.host.F) ≠ ⊥ := by
    first
      | exact differentIdeal_ne_bot
      | exact differentIdeal_ne_bot (A := ℤ)
  first
    | exact Ideal.map_ne_bot_of_ne_bot h0
    | exact fun h => h0 ((Ideal.map_eq_bot_iff_of_injective
        (NoZeroSMulDivisors.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))).mp h)
    | exact fun h => h0 ((Ideal.map_eq_bot_iff_of_injective
        (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))).mp h)

theorem one_mem_ddS_neg (D : D7) (m : ℕ) :
    (1 : D.host.E) ∈ (ddS D ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have hpow : ddS D ^ m = ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
      (differentIdeal ℤ (𝓞 D.host.F)) ^ m : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [ddS, FractionalIdeal.coeIdeal_pow]
  have hI : ddS D ^ m ≠ 0 := by
    rw [hpow, Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact pow_ne_zero _ (diffIdeal_ne_bot D)
  have hle : ddS D ^ m ≤ 1 := by
    rw [hpow]
    exact FractionalIdeal.coeIdeal_le_one
  rw [zpow_neg, zpow_natCast, ← FractionalIdeal.one_le]
  have h1 := FractionalIdeal.inv_anti_mono hI one_ne_zero hle
  rwa [inv_one] at h1

theorem e_mem_lam (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : IsRowLat D F0 Λ) (a : Fin D.R.rS) : F0.e a ∈ Λ := by
  have hx : F0.e a ∈ XS D F0 := by
    apply Submodule.subset_span
    refine ⟨a, 1, ?_, (one_smul _ _).symm⟩
    have h1 := one_mem_ddS_neg D (D.R.rS - (a : ℕ))
    rwa [Nat.cast_sub a.isLt.le] at h1
  rw [← hΛ.2.2] at hx
  exact (Submodule.mem_inf.mp hx).1

end PI.NRL
