import Formalism.HermitianCurvature.HermitianCurvatureProofs.SectionEmbeddingMulVec

open Matrix Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW

noncomputable section

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P

variable {n r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nu0'_facts (Bs : B.RealPlaceData (n + 1) r Wp Wq) {ζ : ℂ}
    (hζ : Tz (n + 1) r Bs.z * Tz (n + 1) r Bs.z' < Complex.normSq ζ) {m : ℕ}
    {Fr' : Fin m → Fin (2 * r + (n + 1) + 1) → ℂ}
    (hFr' : IsFrameOf (n + 1) r [(NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z'] Fr') :
    inWb (n + 1) r (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ) ∧
      herm (Hpk (n + 1) r) (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ) Bs.z' = 0 ∧
      IsFrameOf (n + 1) r [Bs.z', SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ] Fr' := by
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  obtain ⟨-, -, hfix, -⟩ := DU.base hz hz' Bs.T_pos Bs.T'_pos Bs.sec hζ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ
  have hG := NFRadRedA.uwb_glev hm
  have hGi := FrameEntries.glev_inv hG
  have hy : inWb (n + 1) r ((NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z) := Qx8.inWb_mulVec hGi hz
  have hW : inWb (n + 1) r (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ) := by
    show inWb (n + 1) r (SSn.unitH (n + 1) r (SSn.prWv (n + 1) r Bs.z' ((NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z)))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz' hy) _
  refine ⟨hW, ?_, hFr'.1, hFr'.2.1, fun a w hw => ?_⟩
  · rw [← hfix]; exact DU.prWv_perp Bs.T'_pos hW
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hFr'.2.2 a _ (by simp)
    · show herm (Hpk (n + 1) r) (Fr' a)
        (SSn.unitH (n + 1) r (SSn.prWv (n + 1) r Bs.z' ((NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z))) = 0
      have h0 : herm (Hpk (n + 1) r) (Fr' a)
          (SSn.prWv (n + 1) r Bs.z' ((NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z)) = 0 := by
        rw [DU.prWv_of hy, DU.hadd_r, DU.hsmul_r, hFr'.2.2 a ((NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z) (by simp),
          hFr'.2.2 a Bs.z' (by simp), mul_zero, add_zero]
      unfold SSn.unitH
      rw [DU.hsmul_r, h0, mul_zero]

theorem tht_adapted (Bs : B.RealPlaceData (n + 1) r Wp Wq) {ζ : ℂ}
    (hζ : Tz (n + 1) r Bs.z * Tz (n + 1) r Bs.z' < Complex.normSq ζ)
    {Bw Bw' : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ} (hBw : IsFrameOf (n + 1) r [Bs.z] Bw)
    (hBw' : IsFrameOf (n + 1) r [Bs.z'] Bw') {Fr : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ}
    (hB₁ : IsFrameOf (n + 1) r [Bs.z]
      (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Fr (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ)))
    (hFr' : IsFrameOf (n + 1) r [(NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z']
      (fun a => (NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Fr a)) (X : Wq →L[ℂ] Wp) (v : Wq) :
    tht (n + 1) r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ)
        (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ) X v =
      ∑ c : Fin n, etaK (EB Bs.π (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Fr
          (SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ))) c
        (X (yK (EB Bs.π' (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ)
          (fun a => (NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ *ᵥ Fr a) (SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ))) c v)) := by
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hT := Bs.T_pos
  have hT' := Bs.T'_pos
  have hR : IsRepW (n + 1) r Bs.z Bs.π := ⟨Bs.π_rep, Bs.π_cont⟩
  have hR' : IsRepW (n + 1) r Bs.z' Bs.π' := ⟨Bs.π'_rep, Bs.π'_cont⟩
  obtain ⟨hνfix, hνν, hν'fix, hν'ν'⟩ := DU.base hz hz' hT hT' Bs.sec hζ
  obtain ⟨hν'W, hν'z, hFr2⟩ := nu0'_facts Bs hζ hFr'
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ
  have hG := NFRadRedA.uwb_glev hm
  have hU : NF.muZ (n + 1) r Bs.μsec ζ ∈ UH (Hpk (n + 1) r) := hG.1
  have hmm : NF.muZ (n + 1) r Bs.μsec ζ * (NF.muZ (n + 1) r Bs.μsec ζ)⁻¹ = 1 := Gauge.GC.KLAM.mul_inv_uh hU
  set μ := NF.muZ (n + 1) r Bs.μsec ζ with hμ
  set ν := SSn.nu0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ with hν
  set ν' := SSn.nu0' (n + 1) r Bs.z Bs.z' Bs.μsec ζ with hν'
  have hB₁' := FrameExtension.frame_snoc hFr2 hν'W hν'z hν'ν'
  set B₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Fr ν with hB₁def
  set B₁' : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) (fun a => μ⁻¹ *ᵥ Fr a) ν' with hB₁'def
  have hBc : ∀ c : Fin n, B₁ c.castSucc = Fr c := fun c => by rw [hB₁def, Fin.snoc_castSucc]
  have hBl : B₁ (Fin.last n) = ν := by rw [hB₁def, Fin.snoc_last]
  have hBc' : ∀ c : Fin n, B₁' c.castSucc = μ⁻¹ *ᵥ Fr c := fun c => by rw [hB₁'def, Fin.snoc_castSucc]
  have hBl' : B₁' (Fin.last n) = ν' := by rw [hB₁'def, Fin.snoc_last]
  rw [TF.tht_indep hz hT hR hz' hT' hR' hBw hB₁ hBw' hB₁' ν ν' _, TF.tht_form hz hT hR hB₁, hνfix, hν'fix]
  simp only [ContinuousLinearMap.sum_apply, TF.sandw_apply, ContinuousLinearMap.comp_apply]
  rw [Fin.sum_univ_castSucc]
  have hlast : SSn.io0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ *ᵥ B₁' (Fin.last n) = 0 := by
    rw [section_embedding_mul_vec, hBl', ← hν', hν'fix, hν'ν', one_smul, sub_self, Matrix.mulVec_zero]
  have hpr0 : SSn.prWv (n + 1) r Bs.z (0 : Fin (2 * r + (n + 1) + 1) → ℂ) = 0 := by
    have := TF.prWv_smul (k := n + 1) (r := r) Bs.z 0 0
    simpa using this
  rw [hlast, hpr0, TF.ebM_zero_left, TF.ecOp_zero, ContinuousLinearMap.zero_apply, add_zero]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc : SSn.io0 (n + 1) r Bs.z Bs.z' Bs.μsec ζ *ᵥ B₁' c.castSucc = Fr c := by
    rw [section_embedding_mul_vec, hBc', ← hν', DU.prWv_fix (hFr2.1 c) (hFr2.2.2 c Bs.z' (by simp)), hFr2.2.2 c ν' (by simp),
      zero_smul, sub_zero, Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec]
  have hFc : SSn.prWv (n + 1) r Bs.z (Fr c) = Fr c := by
    rw [← hBc c]
    exact DU.prWv_fix (hB₁.1 _) (hB₁.2.2 _ Bs.z (by simp))
  rw [hc, hFc]
  have e1 : ebM (n + 1) r (Fr c) ν = unitB (Hpk (n + 1) r) B₁ c.castSucc (Fin.last n) := by
    rw [← TF.ebM_frame, hBc, hBl]
  have e2 : ebM (n + 1) r ν' (B₁' c.castSucc) = unitB (Hpk (n + 1) r) B₁' (Fin.last n) c.castSucc := by
    rw [← TF.ebM_frame, hBl']
  rw [e1, e2]
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
