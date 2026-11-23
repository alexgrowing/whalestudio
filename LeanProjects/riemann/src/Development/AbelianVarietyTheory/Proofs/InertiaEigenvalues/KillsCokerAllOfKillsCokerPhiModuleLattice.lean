import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationBounds

noncomputable section

namespace GlobalTheory.CokerLift

open PowerSeries GlobalTheory.BK Matrix

section Psi

variable {K : Type} [NormedField K]

def psi (l : ℕ) : K⟦X⟧ →ₗ[K] K⟦X⟧ where
  toFun f := PowerSeries.mk fun n => coeff (l * n) f
  map_add' f g := by ext n; simp
  map_smul' c f := by ext n; simp

theorem coeff_psi (l : ℕ) (f : K⟦X⟧) (n : ℕ) : coeff n (psi l f) = coeff (l * n) f := by
  simp [psi]

theorem psi_frob_mul (l : ℕ) [Fact l.Prime] (g h : K⟦X⟧) :
    psi l (frob K l g * h) = g * psi l h := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  rw [coeff_psi, coeff_mul, coeff_mul]
  have hinj : Function.Injective (fun p : ℕ × ℕ => (l * p.1, l * p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hl h.1) (Nat.eq_of_mul_eq_mul_left hl h.2)
  have h1 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff p.1 g * coeff p.2 (psi l h) =
      ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).map ⟨_, hinj⟩, coeff p.1 (frob K l g) * coeff p.2 h := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Function.Embedding.coeFn_mk, coeff_frob, coeff_psi, dvd_mul_right, if_true,
      Nat.mul_div_cancel_left _ hl]
  rw [h1]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro p hp
    rw [Finset.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq ⊢
    simp only [Function.Embedding.coeFn_mk]
    rw [← mul_add, hq]
  · intro p hp hp'
    rw [coeff_frob, if_neg, zero_mul]
    rintro ⟨c, hc⟩
    apply hp'
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [Finset.mem_map]
    refine ⟨(c, n - c), ?_, ?_⟩
    · have : l * c ≤ l * n := by omega
      have := Nat.le_of_mul_le_mul_left this hl
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      simp only; omega
    · refine Prod.ext hc.symm ?_
      simp only [Function.Embedding.coeFn_mk, Nat.mul_sub]
      omega

theorem psi_frob (l : ℕ) [Fact l.Prime] (g : K⟦X⟧) : psi l (frob K l g) = g := by
  ext n
  rw [coeff_psi, coeff_frob, if_pos (dvd_mul_right _ _),
    Nat.mul_div_cancel_left _ (Fact.out : l.Prime).pos]

theorem psi_mulVec {ι κ : Type} [Fintype ι] (l : ℕ) [Fact l.Prime] (Y : Matrix κ ι K⟦X⟧)
    (m : ι → K⟦X⟧) :
    (fun i => psi l ((Y.map (frob K l) *ᵥ m) i)) = Y *ᵥ fun j => psi l (m j) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, psi_frob_mul]

end Psi

end GlobalTheory.CokerLift

noncomputable section

namespace GlobalTheory.CokerLift

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds

section Main

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]

theorem psi_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : psi l f ∈ A O K := fun n => by
  rw [coeff_psi]
  exact hf _

theorem killsCoker_M {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q) (n : ℕ)
    (hL : KillsCoker F.app n P.L Q.L) : KillsCoker F.app n P.M Q.M := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hL (Q.phi y) (Q.phi_mem_L hy)
  have hm (τ : ZMod a) := P.mem_extc_iff.1 (mem_tot.1 hx τ)
  refine ⟨fun σ i => psi l ((P.mxInv (σ + 1) *ᵥ x (σ + 1)) i),
    mem_tot.2 fun σ i => psi_mem_A (hm (σ + 1) i), ?_⟩
  funext σ
  have key : (F.mat σ).map (frob K l) *ᵥ (P.mxInv (σ + 1) *ᵥ x (σ + 1)) = n • frobV l (y σ) := by
    have hc := F.comm (σ + 1)
    rw [add_sub_cancel_right] at hc
    have h2 : (F.mat σ).map (frob K l) = Q.mxInv (σ + 1) * (F.mat (σ + 1) * P.mx (σ + 1)) := by
      rw [hc, ← Matrix.mul_assoc, Q.mxInv_mul_mx, Matrix.one_mul]
    have h3 := congrFun hxy (σ + 1)
    rw [Hom.app_apply, Pi.smul_apply, Q.phi_apply, add_sub_cancel_right] at h3
    rw [h2, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, P.mx_mul_mxInv, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Q.mxInv_mul_mx,
      Matrix.one_mulVec]
  rw [Hom.app_apply, ← psi_mulVec, key]
  funext i
  simp only [Pi.smul_apply, frobV_apply, map_nsmul, psi_frob]

theorem killsCoker_EM [NormedAlgebra ℚ_[l] K] [NeZero e] {P : PhiMod O K l e a ι}
    {Q : PhiMod O K l e a κ} (F : Hom P Q) (n η : ℕ) (hM : KillsCoker F.app n P.M Q.M) :
    KillsCoker F.app n (P.EM η) (Q.EM η) := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hM _ hy
  refine ⟨Ezpow K l e (-(η : ℤ)) • x, ?_, ?_⟩
  · change E K l e ^ η • Ezpow K l e (-(η : ℤ)) • x ∈ P.M
    rw [smul_smul, E_pow_mul_Ezpow_neg, one_smul]
    exact hx
  · rw [map_smul, hxy, smul_comm, smul_smul, mul_comm, E_pow_mul_Ezpow_neg, one_smul]

theorem killsCoker_invOf [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
    {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {Δ₁ : Descent P} {Δ₂ : Descent Q}
    (F : Descent.Hom Δ₁ Δ₂) (n : ℕ) (W₁ : Submodule (A O K) (Vec K a ι))
    (W₂ : Submodule (A O K) (Vec K a κ)) (hW : ∀ g, ∀ v ∈ W₁, Δ₁.act g v ∈ W₁)
    (h : KillsCoker F.app n W₁ W₂) : KillsCoker F.app n (Δ₁.invOf W₁) (Δ₂.invOf W₂) := by
  intro y hy
  obtain ⟨hy1, hy2⟩ := Δ₂.mem_invOf.1 hy
  obtain ⟨x, hx, hxy⟩ := h y hy1
  refine ⟨Δ₁.avg x, Δ₁.mem_invOf.2 ⟨Δ₁.avg_mem (W₁.restrictScalars O) fun g => hW g x hx,
    fun g => Δ₁.avg_mem_inv x g⟩, ?_⟩
  have := Δ₁.map_avg (F.app.restrictScalars K) (v := x) fun g => by
    simp only [LinearMap.restrictScalars_apply]
    rw [F.app_act, hxy, map_nsmul, hy2 g]
  exact this.trans hxy

theorem killsCoker_Y' [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
    {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {Δ₁ : Descent P} {Δ₂ : Descent Q}
    (F : Descent.Hom Δ₁ Δ₂) (n η : ℕ) (hY : KillsCoker F.app n (Δ₁.Y η) (Δ₂.Y η)) :
    KillsCoker F.app n (Δ₁.Y' η) (Δ₂.Y' η) := by
  intro y hy
  obtain ⟨y₀, h₀, rfl⟩ := Δ₂.mem_Y'.1 hy
  obtain ⟨x, hx, hxy⟩ := hY y₀ h₀
  exact ⟨_, Δ₁.mem_Y'.2 ⟨x, hx, rfl⟩, by rw [map_smul, hxy, smul_comm]⟩

end Main

theorem killsAll_of_killsCoker_L (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type)
    [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H)
    (F : BKHom D₁ D₂) : ∀ r : ℕ, KillsCoker F.app (l ^ r) D₁.L D₂.L → KillsAll F (l ^ r) := by
  intro r hL
  have hM := killsCoker_M F.toHom _ hL
  have hEM := killsCoker_EM F.toHom _ η hM
  have hY := killsCoker_invOf F _ _ _ (fun g _ hv => D₁.desc.act_mem_EM g hv) hEM
  exact ⟨hL, hM, hEM, killsCoker_invOf F _ _ _ (fun g v hv => D₁.desc.act_mem_M g v hv) hM, hY,
    killsCoker_Y' F _ η hY⟩

end GlobalTheory.CokerLift
