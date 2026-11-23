import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilRingEqIntegralAddEisensteinFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemEisensteinFiltrationEqEisensteinPowMulDiscStatement

open PowerSeries GlobalTheory.BK Matrix

noncomputable section

namespace GlobalTheory.IntegralityComp

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]

theorem S_eq_A_add_Fil {j : ℕ} (hj : j < l) {f : K⟦X⟧} (hf : f ∈ S O K e) :
    ∃ g ∈ A O K, ∃ φ ∈ Fil O K l e j, f = g + (φ : K⟦X⟧) := GlobalTheory.T.breuilRing_eq_integral_add_eisensteinFiltration O K l e j hj f hf

theorem Fil_le_E_pow (j : ℕ) {φ : S O K e} (hφ : φ ∈ Fil O K l e j) :
    ∃ q ∈ Rpi O K l e, (φ : K⟦X⟧) = E K l e ^ j * q := GlobalTheory.T.mem_eisensteinFiltration_eq_eisenstein_pow_mul_disc O K l e j φ hφ

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def colVec (P : PhiMod O K l e a ι) (τ : ZMod a) (i : ι) : Vec K a ι := Pi.single τ ((P.mx τ).col i)

theorem colVec_mem_MM (P : PhiMod O K l e a ι) (τ : ZMod a) (i : ι) : colVec P τ i ∈ P.MM := by
  refine mem_tot.2 fun σ => ?_
  by_cases h : σ = τ
  · subst h
    simp only [colVec, Pi.single_eq_same]
    exact Submodule.subset_span ⟨i, rfl⟩
  · simp only [colVec, Pi.single_eq_of_ne h]
    exact zero_mem _

theorem sum_colVec (P : PhiMod O K l e a ι) (c : ZMod a → ι → K⟦X⟧) :
    (∑ τ, ∑ i, c τ i • colVec P τ i) = fun τ => P.mx τ *ᵥ c τ := by
  ext τ k
  simp only [Finset.sum_apply, Pi.smul_apply, colVec, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single τ]
  · simp [Matrix.mulVec, dotProduct, mul_comm]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem MM_eq_L_add_FilMM (P : PhiMod O K l e a ι) {j : ℕ} (hj : j < l) {m : Vec K a ι}
    (hm : m ∈ P.MM) : ∃ p ∈ P.L, ∃ f ∈ P.FilMM j, m = p + f := by
  have hs (τ : ZMod a) (i : ι) : (P.mxInv τ *ᵥ m τ) i ∈ S O K e :=
    P.mem_extc_iff.1 (mem_tot.1 hm τ) i
  choose g hg φ hφ hgφ using fun τ i => S_eq_A_add_Fil (O := O) (l := l) hj (hs τ i)
  have hm' (τ : ZMod a) : m τ = P.mx τ *ᵥ (P.mxInv τ *ᵥ m τ) := by
    rw [Matrix.mulVec_mulVec, P.mx_mul_mxInv, Matrix.one_mulVec]
  refine ⟨fun τ => P.mx τ *ᵥ g τ, mem_tot.2 fun τ => P.mem_extc.2 ⟨g τ, fun i => hg τ i, rfl⟩,
    ∑ τ, ∑ i, φ τ i • colVec P τ i, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun τ _ => Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem_smul (hφ τ i) (colVec_mem_MM P τ i)
  · have : (∑ τ, ∑ i, φ τ i • colVec P τ i) = ∑ τ, ∑ i, (φ τ i : K⟦X⟧) • colVec P τ i := rfl
    rw [this, sum_colVec]
    ext1 τ
    rw [Pi.add_apply, ← Matrix.mulVec_add, hm' τ]
    congr 1
    ext1 i
    exact hgφ τ i

section Dat

variable [TameDescentExponentData K l e a] {η H : ℕ} (D : BKDat O K l e a ι η H)

theorem Ezpow_smul_FilMM_mem (hηH : η < H) {f : Vec K a ι} (hf : f ∈ D.FilMM (10 * H)) :
    Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man := by
  refine Submodule.smul_induction_on hf (fun φ hφ m hm => ?_) (fun x y hx hy => ?_)
  · obtain ⟨q, hq, hφq⟩ := Fil_le_E_pow (O := O) (10 * H) hφ
    have hEm := D.smul_mem_Mext (A_le_S l e) hm
    have key : Ezpow K l e (-(2 * H : ℤ)) • φ • m =
        (E K l e ^ (8 * H - η) * q) • (E K l e ^ η • m) := by
      have h1 : Ezpow K l e (-(2 * H : ℤ)) * E K l e ^ (10 * H) = E K l e ^ (8 * H - η) * E K l e ^ η := by
        rw [← pow_add, show 8 * H - η + η = 8 * H by omega, ← Ezpow_natCast, ← Ezpow_natCast,
          ← Ezpow_add]
        congr 1
        push_cast
        ring
      rw [show φ • m = (φ : K⟦X⟧) • m from rfl, hφq, smul_smul, smul_smul, ← mul_assoc, h1]
      congr 1
      ring
    rw [key]
    exact D.smul_mem_Man (mul_mem (pow_mem (E_mem l e _) _) hq)
      (D.Mext_mono (S_le_R l e) hEm)
  · rw [smul_add]
    exact add_mem hx hy

theorem E_pow_smul_EN_mem (hηH : η < H) (hl : 10 * H + 2 ≤ l) {y : Vec K a ι} (hy : y ∈ D.EM η) :
    ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), E K l e ^ (2 * H) • D.EN y = p + f := by
  have hl0 : E K l e ^ (H + η) • y ∈ D.L := by
    rw [pow_add, mul_smul]
    exact D.lower _ hy
  have hMM : E K l e ^ (H + η) • y ∈ D.MM := D.ext_mono (A_le_S l e) hl0
  have hc : D.conn (E K l e ^ (H + η) • y) ∈ D.MM := D.conn_mem_MM hMM
  have hA : E K l e ^ (H - η) * E K l e ∈ S O K e := mul_mem (pow_mem (E_mem l e _) _) (E_mem l e _)
  obtain ⟨p, hp, f, hf, hpf⟩ := MM_eq_L_add_FilMM D.toPhiMod (j := 10 * H) (by omega)
    (D.MM.smul_mem ⟨_, hA⟩ hc)
  have hB : E K l e ^ (H - η) * (((H + η : ℕ) : K⟦X⟧) * N K (E K l e)) ∈ A O K :=
    mul_mem (pow_mem (E_mem l e _) _) (mul_mem (natCast_mem _ _) (by
      rw [N_E]; exact mul_mem (natCast_mem _ _) (pow_mem HasU.X_mem _)))
  refine ⟨p - (E K l e ^ (H - η) * (((H + η : ℕ) : K⟦X⟧) * N K (E K l e))) • (E K l e ^ (H + η) • y),
    sub_mem hp (D.L.smul_mem ⟨_, hB⟩ hl0), f, hf, ?_⟩
  have h1 : E K l e ^ (2 * H) • D.EN y = E K l e ^ (H - η) • (E K l e ^ (H + η) • D.EN y) := by
    rw [smul_smul, ← pow_add, show H - η + (H + η) = 2 * H by omega]
  rw [h1, PhiMod.E_pow_smul_EN, PhiMod.EN_apply, smul_sub, smul_smul, smul_smul]
  have h2 : (E K l e ^ (H - η) * E K l e) • D.conn (E K l e ^ (H + η) • y) = p + f := hpf
  rw [h2]
  abel

end Dat

end GlobalTheory.IntegralityComp

theorem GlobalTheory.IntegralityComp.integralityComputation : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), η < H → 10 * H + 2 ≤ l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.IntegralityComputation D := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hηH hl
  exact ⟨fun m hm => GlobalTheory.IntegralityComp.MM_eq_L_add_FilMM D.toPhiMod (by omega) hm,
    fun f hf => GlobalTheory.IntegralityComp.Ezpow_smul_FilMM_mem D hηH hf,
    fun y hy => GlobalTheory.IntegralityComp.E_pow_smul_EN_mem D hηH hl hy⟩
