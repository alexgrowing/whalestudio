import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction

noncomputable section

open PowerSeries Matrix

namespace GlobalTheory.BK.FilAn

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι)

theorem E_pow_smul_mem_extRpi {β : ℕ} (hβ : ∀ v ∈ P.M, E K l e ^ β • v ∈ P.L) {m : Vec K a ι}
    (hm : m ∈ P.Mext (Rpi O K l e)) : E K l e ^ β • m ∈ P.ext (Rpi O K l e) :=
  P.smul_mem_ext_of_basis (fun i => hβ _ (P.bas_mem_M i)) (A_le_Rpi l e) hm

theorem mem_extInvL_of_Ezpow_smul {i : ℤ} {y : Vec K a ι} (hy : y ∈ P.ext (Rpi O K l e))
    (hg : Ezpow K l e i • y ∈ P.Mext (invL l (A O K))) : y ∈ P.ext (invL l (A O K)) := by
  refine mem_tot.2 fun τ => P.mem_extc_iff.2 fun j => ?_
  have hc : (P.mxInv τ *ᵥ y τ) j ∈ Rpi O K l e := P.mem_extc_iff.1 (mem_tot.1 hy τ) j
  have hB : invE l e (A O K) ≤ invE l e (invL l (A O K)) := away_mono (le_away _ _) rfl
  have h1 : (P.mxInv τ *ᵥ (Ezpow K l e i • y) τ) j ∈ invE l e (invL l (A O K)) := by
    simp only [Matrix.mulVec, dotProduct]
    exact Subalgebra.sum_mem _ fun k _ => mul_mem (hB (P.mxInv_mem τ j k))
      (le_away _ _ (mem_tot.1 hg τ k))
  obtain ⟨n, hn⟩ := h1
  have h2 : Ezpow K l e (n + i) * (P.mxInv τ *ᵥ y τ) j ∈ invL l (A O K) := by
    rw [Ezpow_add, Ezpow_natCast, mul_assoc]
    simpa [Matrix.mulVec_smul] using hn
  have h3 := mul_mem ((Ezpow_mem_invL_A_iff (O := O) (K := K) (l := l) (e := e)
    (i := ((-(n + i)).toNat : ℤ))).2 (by omega)) h2
  rw [← mul_assoc, ← Ezpow_add,
    show (((-(n + i)).toNat : ℕ) : ℤ) + (n + i) = ((n + i).toNat : ℕ) by omega, Ezpow_natCast] at h3
  exact mem_invL_A_of_E_pow_mul l e _ hc h3

omit [IsUltrametricDist K] [CompleteSpace K] [IsUnitBall O K] [Fintype ι] [DecidableEq ι] in
theorem Ezpow_zero' : Ezpow K l e 0 = 1 := by
  simpa using Ezpow_natCast (K := K) l e 0

omit [CompleteSpace K] in
theorem mem_extRpi_of_mem_shiftE_one {z : Vec K a ι} (hz : z ∈ shiftE l e 1 (P.ext (Rpi O K l e))) :
    z ∈ P.ext (Rpi O K l e) := by
  have h := P.smul_tot_mem_ext (f := fun _ => E K l e) (fun _ => E_mem l e _) (mem_shiftE.1 hz)
  have h1 : E K l e * Ezpow K l e (-1) = 1 := by
    simpa using E_pow_mul_Ezpow_neg (K := K) l e 1
  have h2 : ((fun _ : ZMod a => E K l e) • Ezpow K l e (-1) • z) = z := by
    ext τ j
    simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, h1, one_mul]
  rwa [h2] at h

theorem exists_mem_filL_of_mem_inf [NeZero a] (i : ℤ) {x : Vec K a ι}
    (hx : x ∈ P.ext (Rpi O K l e) ⊓ shiftE l e i (P.Mext (Rpi O K l e))) :
    ∃ y ∈ P.filL i, x - y ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
  obtain ⟨hxL, hxM⟩ := Submodule.mem_inf.1 hx
  obtain ⟨-, β, -, hβ⟩ := P.exists_exponents
  set N : ℕ := (β + 1 - i).toNat with hN
  choose g hg h hh hgh using fun τ k => exists_div_E_pow l e N (mem_tot.1 (mem_shiftE.1 hxM) τ k)
  have hgM : g ∈ P.Mext (invL l (A O K)) := mem_tot.2 fun τ k => hg τ k
  have hhM : h ∈ P.Mext (Rpi O K l e) := mem_tot.2 fun τ k => hh τ k
  have hx' : Ezpow K l e (-i) • x = g + E K l e ^ N • h := by
    funext τ k
    exact hgh τ k
  have hxe : x = Ezpow K l e i • g + Ezpow K l e i • E K l e ^ N • h := by
    rw [← smul_add, ← hx', smul_smul, ← Ezpow_add, add_neg_cancel, Ezpow_zero', one_smul]
  have hsub : x - Ezpow K l e i • g ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
    rw [mem_shiftE]
    have h1 := E_pow_smul_mem_extRpi P hβ (P.smul_tot_mem_Mext (f := fun _ => E K l e ^ (i - 1 + N - β).toNat)
      (fun _ => pow_mem (E_mem l e _) _) hhM)
    convert h1 using 1
    have hs : Ezpow K l e (-1) * (Ezpow K l e i * E K l e ^ N) =
        E K l e ^ β * E K l e ^ (i - 1 + N - β).toNat := by
      simp only [← Ezpow_natCast, ← Ezpow_add]
      congr 1
      omega
    rw [hxe, add_sub_cancel_left]
    funext τ k
    simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul]
    linear_combination (h τ k) * hs
  refine ⟨Ezpow K l e i • g, Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨?_, ?_⟩), hsub⟩
  · refine mem_extInvL_of_Ezpow_smul P (i := -i) ?_ ?_
    · have := sub_mem hxL (mem_extRpi_of_mem_shiftE_one P hsub)
      rwa [sub_sub_cancel] at this
    · rwa [smul_smul, ← Ezpow_add, neg_add_cancel, Ezpow_zero', one_smul]
  · rwa [mem_shiftE, smul_smul, ← Ezpow_add, neg_add_cancel, Ezpow_zero', one_smul]

end GlobalTheory.BK.FilAn

open GlobalTheory.BK in

theorem GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (i : ℤ) (x : Vec K a ι), x ∈ (P.ext (Rpi O K l e) ⊓ shiftE l e i (P.Mext (Rpi O K l e))) ⊔ shiftE l e 1 (P.ext (Rpi O K l e)) ↔ ∃ y ∈ P.filL i, x - y ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P i x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨y, hy, hxy⟩ := FilAn.exists_mem_filL_of_mem_inf P i hx₁
    refine ⟨y, hy, ?_⟩
    rw [add_sub_right_comm]
    exact add_mem hxy hx₂
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨hy₁L, hy₁M⟩ := Submodule.mem_inf.1 hy₁
    refine Submodule.mem_sup.2 ⟨y₁, Submodule.mem_inf.2 ⟨P.ext_mono (invL_A_le_Rpi l e) hy₁L,
      mem_shiftE.2 (P.Mext_mono (invL_A_le_Rpi l e) (mem_shiftE.1 hy₁M))⟩, y₂ + (x - (y₁ + y₂)),
      add_mem (mem_shiftE.2 (P.ext_mono (invL_A_le_Rpi l e) (mem_shiftE.1 hy₂))) hxy, by abel⟩
