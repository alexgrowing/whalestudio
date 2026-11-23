import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting
open Formalism.L2.SG.RealObj.InfCut

section RelGen

theorem mulVec_single_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    (M *ᵥ Pi.single j (1 : ℂ)) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem herm_smul_right' (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v w : Fin (2 * r + k + 1) → ℂ)
    (s : ℂ) : Formalism.QuantumDeterminants.herm H v (s • w) = star s * Formalism.QuantumDeterminants.herm H v w := by
  unfold Formalism.QuantumDeterminants.herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem hJ_fd_Q (hT : TrHyp F Qm Qim c) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    hJ ε (F.fd a) (Qm *ᵥ v) = c a * v (Formalism.QuantumDeterminants.eI k r a) := by
  have e1 : F.fd a = Qm *ᵥ (Qim *ᵥ F.fd a) := by rw [Matrix.mulVec_mulVec, hT.h2, Matrix.one_mulVec]
  rw [e1, ← herm_Q hT, Qi_f hT, herm_smul_right', star_star, Formalism.L2.SG.Pf.CarrierBase.herm_bvec,
    Formalism.L2.SG.Pf.CarrierBase.hpk_mulVec_esI]

theorem rootCoord_Q (hT : TrHyp F Qm Qim c) {κ : ℂ} (hc : ∀ a : Fin r, c a = κ ^ (r - a.val)) (hκ0 : κ ≠ 0)
    (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r) :
    rootCoord ε F.e F.fd F.z (Qm * ρ * Qim) a =
      κ * (if h : a.val + 1 < r then ρ (Formalism.QuantumDeterminants.eI k r a) (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩)
        else (ρ *ᵥ (Qim *ᵥ F.z)) (Formalism.QuantumDeterminants.eI k r a)) := by
  unfold rootCoord nxt
  by_cases h : a.val + 1 < r
  · rw [dif_pos h, dif_pos h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Qi_e hT, Matrix.mulVec_smul,
      Matrix.mulVec_smul, PtRepPf.hJ_smul_right, hJ_fd_Q hT, hc, hc]
    unfold Formalism.QuantumDeterminants.bvec
    rw [mulVec_single_apply]
    have he : r - a.val = (r - (a.val + 1)) + 1 := by omega
    simp only
    rw [he, pow_succ]
    field_simp
  · rw [dif_neg h, dif_neg h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hJ_fd_Q hT, hc]
    have he : r - a.val = 1 := by have := a.2; omega
    rw [he, pow_one]

theorem sum_rootCoord (hT : TrHyp F Qm Qim c) {κ : ℂ} (hc : ∀ a : Fin r, c a = κ ^ (r - a.val)) (hκ0 : κ ≠ 0)
    (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ∑ a, rootCoord ε F.e F.fd F.z (Qm * ρ * Qim) a = κ * Formalism.QuantumDeterminants.ell k r (Qim *ᵥ F.z) ρ := by
  simp only [rootCoord_Q hT hc hκ0, ← Finset.mul_sum]
  rfl

theorem psiR_Q (hT : TrHyp F Qm Qim c) (gg : ℕ) (hgg : 0 < gg) {κ : ℂ} (hc : ∀ a : Fin r, c a = κ ^ (r - a.val))
    (hκ : κ = -Complex.I * (((gg : ℝ) / (2 * Real.pi) : ℝ) : ℂ)) (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    psiR ε gg F.e F.fd F.z (Qm * ρ * Qim) = Formalism.QuantumDeterminants.psi k r (Qim *ᵥ F.z) Formalism.QuantumDeterminants.cStd ρ := by
  have hg : (0 : ℝ) < gg := by exact_mod_cast hgg
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    refine mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) ?_
    have : (0 : ℝ) < (gg : ℝ) / (2 * Real.pi) := div_pos hg (by positivity)
    exact_mod_cast this.ne'
  unfold psiR Formalism.QuantumDeterminants.psi
  congr 1
  rw [Finset.sum_add_distrib, ← star_sum, sum_rootCoord hT hc hκ0]
  set ℓ := Formalism.QuantumDeterminants.ell k r (Qim *ᵥ F.z) ρ
  rw [show star (κ * ℓ) = (starRingEnd ℂ) (κ * ℓ) from rfl, Complex.add_conj]
  rw [hκ]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Formalism.QuantumDeterminants.cStd, Complex.div_re, Complex.div_im] <;>
    field_simp <;> ring

theorem psiR_conj {H Hi g : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε)
    (hiH : Hi * H = 1) (hHe : ∀ a, H *ᵥ F.e a = F.e a) (hHf : ∀ a, H *ᵥ F.fd a = F.fd a) (hHz : H *ᵥ F.z = F.z)
    (gg : ℕ) : psiR ε gg F.e F.fd F.z (H * g * Hi) = psiR ε gg F.e F.fd F.z g := by
  have hHi : ∀ x, H *ᵥ x = x → Hi *ᵥ x = x := fun x hx => by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hiH, Matrix.one_mulVec]
  have hrc : ∀ a, rootCoord ε F.e F.fd F.z (H * g * Hi) a = rootCoord ε F.e F.fd F.z g a := by
    intro a
    unfold rootCoord
    have hn : H *ᵥ nxt F.e F.z a = nxt F.e F.z a := by
      unfold nxt; split_ifs; · exact hHe _
      · exact hHz
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hHi _ hn, fixed_left hH (hHf a)]
  unfold psiR
  simp only [hrc]

theorem spanLt_map {H : Matrix (Fin n) (Fin n) ℂ} (hHe : ∀ a, H *ᵥ F.e a = F.e a) (m : ℕ) {x : Fin n → ℂ}
    (hx : x ∈ spanLt F.e m) : H *ᵥ x ∈ spanLt F.e m := by
  have hle : spanLt F.e m ≤ (spanLt F.e m).comap (Matrix.mulVecLin H) := by
    unfold spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, hHe]
    exact Submodule.subset_span ⟨b, hb, rfl⟩
  exact hle hx

theorem span_range_le (hT : TrHyp F Qm Qim c) : Submodule.span ℂ (Set.range F.e) ≤ spanLt F.e r := by
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, a.2, rfl⟩

theorem inN_Q (hT : TrHyp F Qm Qim c) {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hρ : ρ ∈ Formalism.QuantumDeterminants.Nset k r) : InN ε F.e F.z (Qm * ρ * Qim) := by
  have hsub : ∀ x, (Qm * ρ * Qim - 1) *ᵥ x = Qm *ᵥ ((ρ - 1) *ᵥ (Qim *ᵥ x)) := fun x => by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ Qm Qim, hT.h2, Matrix.one_mulVec]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [hsub, Qi_e hT, Matrix.mulVec_smul, Matrix.mulVec_smul]
    refine Submodule.smul_mem _ _ ?_
    set v := (ρ - 1) *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) with hv
    have hva : ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → v i = 0 := by
      intro i hi
      rw [hv, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
      unfold Formalism.QuantumDeterminants.bvec
      rw [mulVec_single_apply, hρ.2.1 a i hi, sub_eq_zero]
      simp [Pi.single_apply]
    have hvX : IsXv v := fun i hi => hva i (by have := a.2; omega)
    rw [isXv_eq v hvX, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : b.val < a.val
    · rw [Matrix.mulVec_smul, hT.he, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · rw [hva _ (by simp only [Formalism.QuantumDeterminants.eI]; omega), zero_smul, Matrix.mulVec_zero]
      exact Submodule.zero_mem _
  · rw [hsub]
    exact span_range_le hT (Q_X hT _ (N_sub_X hρ _ (Qi_noXs hT F.z F.ez)))
  · rw [hsub]
    exact span_range_le hT (Q_X hT _ (N_sub_X hρ _ (Qi_noXs hT y hy)))

theorem inN_conj {H Hi g : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε)
    (hHi : H * Hi = 1) (hiH : Hi * H = 1) (hHe : ∀ a, H *ᵥ F.e a = F.e a) (hHz : H *ᵥ F.z = F.z)
    (hg : InN ε F.e F.z g) : InN ε F.e F.z (H * g * Hi) := by
  have hHi' : ∀ x, H *ᵥ x = x → Hi *ᵥ x = x := fun x hx => by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hiH, Matrix.one_mulVec]
  have hsub : ∀ x, (H * g * Hi - 1) *ᵥ x = H *ᵥ ((g - 1) *ᵥ (Hi *ᵥ x)) := fun x => by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ H Hi, hHi, Matrix.one_mulVec]
  obtain ⟨⟨h1, h2⟩, h3⟩ := hg
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [hsub, hHi' _ (hHe a)]; exact spanLt_map hHe _ (h1 a)
  · rw [hsub, hHi' _ hHz]; exact spanLt_map hHe _ h2
  · rw [hsub]
    refine spanLt_map hHe _ (h3 _ fun a => ?_)
    rw [← fixed_left hH (hHe a), Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec, hy a]

end RelGen

end Formalism.L2.SG.Pf.Bridge
