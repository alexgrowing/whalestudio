import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open GlobalTheory.BK PowerSeries

namespace GlobalTheory.BK

theorem PhiMod.pow_smul_phi_mem_MM (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (η : ℕ)
    (h : ∀ m ∈ P.L, E K l e ^ η • m ∈ P.M) :
    ∀ m ∈ P.MM, (l : K) ^ η • P.phi m ∈ P.MM := by
  intro m hm
  have h1 : E K l e ^ η • m ∈ P.Mext (S O K e) :=
    P.smul_mem_Mext_of_basis (fun i => h _ (P.phi_mem_L (P.bas_mem_M i))) (A_le_S l e) hm
  have h2 := P.phi_mem_ext (fun _ => frob_mem_S l) h1
  obtain ⟨c, hc, hcE⟩ := exists_mul_frob_E (O := O) (K := K) l e
  have h3 := (P.ext (S O K e)).smul_mem (⟨c ^ η, pow_mem hc η⟩ : S O K e) h2
  rw [Subalgebra.smul_def, P.phi_smul, smul_smul, map_pow, ← mul_pow, hcE] at h3
  have h4 : ((l : K⟦X⟧) ^ η) • P.phi m = (l : K) ^ η • P.phi m := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rwa [h4] at h3

end GlobalTheory.BK
