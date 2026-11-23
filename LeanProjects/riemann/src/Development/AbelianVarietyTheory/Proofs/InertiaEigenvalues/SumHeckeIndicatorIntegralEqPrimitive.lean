import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumCardSubspaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardCosetsEqSubspacesKernelResidue
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardSubspacesFinrankCongr

noncomputable section

open Matrix GlobalTheory.SplitHecke GlobalTheory.ExportSeries

namespace GlobalTheory.HeckeMobius

section Pure

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K]

theorem reps_mul_central {n : ℕ} {ι : Type} {x c : GL (Fin n) K} {R : Finset ι} {ρ : ι → GL (Fin n) K}
    (hc : ∀ g : GL (Fin n) K, c * g = g * c) (h : Reps O x R ρ) :
    Reps O (x * c) R fun γ => ρ γ * c := by
  have hc' : ∀ g : GL (Fin n) K, c⁻¹ * g = g * c⁻¹ := fun g => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc g, mul_inv_cancel_right]
  refine ⟨fun γ hγ => ?_, fun k₁ k₂ h₁ h₂ => ?_⟩
  · obtain ⟨k₁, k₂, h₁, h₂, e⟩ := h.1 γ hγ
    exact ⟨k₁, k₂, h₁, h₂, by show ρ γ * c = _; rw [e]; simp only [mul_assoc, hc k₂]⟩
  · have e : ∀ γ, (ρ γ * c)⁻¹ * (k₁ * (x * c) * k₂) = (ρ γ)⁻¹ * (k₁ * x * k₂) := fun γ => by
      calc (ρ γ * c)⁻¹ * (k₁ * (x * c) * k₂) = c⁻¹ * ((ρ γ)⁻¹ * (k₁ * x * k₂)) * c := by
            rw [_root_.mul_inv_rev]; simp only [mul_assoc, hc k₂]
        _ = (ρ γ)⁻¹ * (k₁ * x * k₂) := by rw [hc', inv_mul_cancel_right]
    exact (existsUnique_congr fun γ => and_congr_right fun _ => by rw [e γ]).2 (h.2 k₁ k₂ h₁ h₂)

def scal {n : ℕ} (a : K) (ha : a ≠ 0) : GL (Fin n) K :=
  Units.map (Matrix.scalar (Fin n) : K →+* Matrix (Fin n) (Fin n) K).toMonoidHom (Units.mk0 a ha)

theorem scal_val {n : ℕ} (a : K) (ha : a ≠ 0) :
    ((scal a ha : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) a := rfl

theorem scal_comm {n : ℕ} (a : K) (ha : a ≠ 0) (g : GL (Fin n) K) : scal a ha * g = g * scal a ha :=
  Units.ext (by
    rw [Units.val_mul, Units.val_mul, scal_val]
    exact (Matrix.scalar_commute a (fun _ => Commute.all _ _) _).eq)

theorem scal_inv_comm {n : ℕ} (a : K) (ha : a ≠ 0) (g : GL (Fin n) K) : (scal a ha)⁻¹ * g = g * (scal a ha)⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, scal_comm, mul_inv_cancel_right]

theorem scal_mul_val {n : ℕ} (a : K) (ha : a ≠ 0) (g : GL (Fin n) K) : (scal a ha * g).1 = a • g.1 := by
  rw [Units.val_mul, scal_val, Matrix.scalar_apply, smul_eq_diagonal_mul]

theorem hk_compl {p : O} (hp : algebraMap O K p ≠ 0) {n j : ℕ} (hj : j ≤ n) {α : GL (Fin n) K} (h : Hk O p j α) :
    Hk O p (n - j) (scal (algebraMap O K p) hp * α⁻¹) := by
  refine ⟨by rw [scal_mul_val]; exact h.2.1, ?_, ?_⟩
  · have : algebraMap O K p • ((scal (algebraMap O K p) hp * α⁻¹)⁻¹ : GL (Fin n) K).1 = α.1 := by
      rw [← scal_mul_val _ hp, _root_.mul_inv_rev, inv_inv, ← mul_assoc, scal_comm, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact h.1
  · obtain ⟨u, hu⟩ := h.2.2
    refine ⟨u⁻¹, ?_⟩
    have h1 : (α⁻¹).1.det * α.1.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have h2 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [scal_mul_val, Matrix.det_smul, Fintype.card_fin, map_mul, map_pow]
    rw [hu, map_mul, map_pow] at h1
    have hn : algebraMap O K p ^ n = algebraMap O K p ^ (n - j) * algebraMap O K p ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    rw [hn]
    linear_combination (-(algebraMap O K p ^ (n - j) * algebraMap O K p ^ j * (α⁻¹).1.det)) * h2 +
      (algebraMap O K p ^ (n - j) * algebraMap O K ((u⁻¹ : Oˣ) : O)) * h1

theorem cond_eq {p : O} (hp : algebraMap O K p ≠ 0) {r n : ℕ} (g : GL (Fin r) K) (z : Matrix (Fin r) (Fin n) O) :
    ((algebraMap O K p)⁻¹ • zᵀ.map (algebraMap O K)) * (tr ((g * (scal (algebraMap O K p) hp)⁻¹)⁻¹)).1 =
      ((g⁻¹).1 * z.map (algebraMap O K))ᵀ := by
  have : (tr ((g * (scal (algebraMap O K p) hp)⁻¹)⁻¹)).1 = (algebraMap O K p • (g⁻¹).1)ᵀ := by
    rw [_root_.mul_inv_rev, inv_inv, ← scal_mul_val _ hp]; rfl
  rw [this, Matrix.transpose_mul, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ hp, one_smul]
  rfl

open IsLocalRing in

theorem count_eq [Finite (ResidueField O)] {p : O} (hp : Irreducible p) {r n k : ℕ} (hk : k ≤ r) {ι : Type}
    {α : GL (Fin r) K} {R : Finset ι} {ρ : ι → GL (Fin r) K} (hα : Hk O p k α) (hR : Reps O α R ρ)
    (z : Matrix (Fin r) (Fin n) O) :
    Nat.card {γ : ι // γ ∈ R ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))} =
      Nat.card {W : Submodule (ResidueField O)
        (Fin (Module.finrank (ResidueField O) (LinearMap.ker (z.map (residue O))ᵀ.mulVecLin)) → ResidueField O) //
          Module.finrank (ResidueField O) W = k} := by
  have h0 : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hp.ne_zero
  have hR' : Reps O (tr (scal (algebraMap O K p) h0 * α⁻¹)) R
      fun γ => tr ((ρ γ * (scal (algebraMap O K p) h0)⁻¹)⁻¹) := by
    apply Reps.tr
    rw [_root_.mul_inv_rev, inv_inv]
    exact reps_mul_central (scal_inv_comm _ h0) hR
  have hc := Cosets.card_cosets O K p hp n r (r - k) ι _ R _ zᵀ (Nat.sub_le r k) (hk_compl h0 hk hα).tr hR'
  calc Nat.card {γ : ι // γ ∈ R ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))}
      = Nat.card {γ : ι // γ ∈ R ∧ IntM O (((algebraMap O K p)⁻¹ • zᵀ.map (algebraMap O K)) *
          (tr ((ρ γ * (scal (algebraMap O K p) h0)⁻¹)⁻¹)).1)} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun γ => and_congr_right fun _ => by
          rw [cond_eq h0]; exact ⟨fun h => h.transpose, fun h => h.transpose⟩)
    _ = _ := hc
    _ = Nat.card {W : Submodule (ResidueField O) (Fin r → ResidueField O) //
          W ≤ LinearMap.ker (z.map (residue O))ᵀ.mulVecLin ∧ Module.finrank (ResidueField O) W = k} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun W => by
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
          · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩)
    _ = _ := GlobalTheory.card_subspaces_le_eq _ _
    _ = _ := GlobalTheory.card_subspaces_finrank_congr (LinearEquiv.ofFinrankEq _ _ (Module.finrank_fin_fun _).symm) k

theorem sum_smul_row {F : Type} [Field F] {r n : ℕ} (y : Matrix (Fin r) (Fin n) F) (g : Fin r → F) :
    yᵀ *ᵥ g = ∑ i, g i • y.row i := by
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.row, mul_comm]

end Pure

open IsLocalRing in

theorem sum_hecke_indicator_eq_prim : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Finite (IsLocalRing.ResidueField O)] (p : O), Irreducible p → ∀ (r n : ℕ) (ι : Type) (α : ℕ → GL (Fin r) K) (R : ℕ → Finset ι) (ρ : ι → GL (Fin r) K), (∀ k ∈ Finset.Icc 1 r, Hk O p k (α k) ∧ Reps O (α k) (R k) ρ) → ∀ z : Matrix (Fin r) (Fin n) O, (1 : ℂ) + ∑ k ∈ Finset.Icc 1 r, (-1 : ℂ) ^ k * (Nat.card (IsLocalRing.ResidueField O) : ℂ) ^ (k * (k - 1) / 2) * (Nat.card {γ : ι // γ ∈ R k ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))} : ℂ) = ((prim (z.map (IsLocalRing.residue O)) : ℚ) : ℂ) := by
  intro O K _ _ _ _ _ _ _ p hp r n ι α R ρ h z
  set A := (z.map (residue O))ᵀ with hA
  set c := Module.finrank (ResidueField O) (LinearMap.ker A.mulVecLin) with hc
  have hcr : c ≤ r := by
    have := Submodule.finrank_le (LinearMap.ker A.mulVecLin)
    rwa [Module.finrank_fin_fun] at this
  let N : ℕ → ℂ := fun k => (Nat.card {W : Submodule (ResidueField O) (Fin c → ResidueField O) //
    Module.finrank (ResidueField O) W = k} : ℂ)
  have hN0 : N 0 = 1 := by
    simp only [N, Submodule.finrank_eq_zero]
    rw [Nat.card_unique, Nat.cast_one]
  have hNc : ∀ k, c < k → N k = 0 := fun k hk => by
    simp only [N, Nat.cast_eq_zero]
    haveI : IsEmpty {W : Submodule (ResidueField O) (Fin c → ResidueField O) //
        Module.finrank (ResidueField O) W = k} := ⟨fun W => by
      have := Submodule.finrank_le W.1
      rw [Module.finrank_fin_fun, W.2] at this
      omega⟩
    exact Nat.card_of_isEmpty
  have e1 : (1 : ℂ) + ∑ k ∈ Finset.Icc 1 r, (-1 : ℂ) ^ k * (Nat.card (ResidueField O) : ℂ) ^ (k * (k - 1) / 2) *
      (Nat.card {γ : ι // γ ∈ R k ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))} : ℂ) =
      ∑ k ∈ Finset.range (r + 1), (-1 : ℂ) ^ k * (Nat.card (ResidueField O) : ℂ) ^ (k * (k - 1) / 2) * N k * 1 ^ k := by
    rw [Finset.sum_range_succ', pow_zero, pow_zero, one_mul, hN0, mul_one, one_mul, add_comm]
    congr 1
    have hI : Finset.Icc 1 r = Finset.Ico 1 (r + 1) := by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hI, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : 1 + k ≤ r := by rw [Finset.mem_range] at hk; omega
    have hm : 1 + k ∈ Finset.Icc 1 r := Finset.mem_Icc.2 ⟨by omega, hk'⟩
    rw [count_eq hp hk' (h _ hm).1 (h _ hm).2 z, one_pow, mul_one, add_comm 1 k]
  have hli : LinearIndependent (ResidueField O) (z.map (residue O)).row ↔ c = 0 := by
    rw [hc, Submodule.finrank_eq_zero, LinearMap.ker_eq_bot', Fintype.linearIndependent_iff]
    refine forall_congr' fun g => ?_
    rw [Matrix.mulVecLin_apply, hA, sum_smul_row]
    constructor
    · intro H h0; funext i; exact H h0 i
    · intro H h0 i; rw [H h0]; rfl
  rw [e1, ← Finset.sum_subset (Finset.range_subset_range.2 (show c + 1 ≤ r + 1 by omega)) (fun k hk hk' => ?_)]
  · refine Eq.trans (GlobalTheory.GaussSubspace.sum_card_subspaces (ResidueField O) c ℂ 1) ?_
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [prim, if_pos (hli.2 h0), h0, Finset.prod_range_zero]
      simp
    · rw [prim, if_neg (fun H => by have := hli.1 H; omega)]
      obtain ⟨m, hm⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
      rw [hm, Finset.prod_range_succ', pow_zero, one_mul, sub_self, mul_zero]
      simp
  · rw [Finset.mem_range, not_lt] at hk'
    rw [hNc k (by omega)]
    ring

end GlobalTheory.HeckeMobius
