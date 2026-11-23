import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.UnitriangularInversePolynomialBound

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.PolynomialProperness

lemma one_mem_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · show (1 : B.Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  · simp
  · simp
  · simp

lemma UW_fix {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z)
    (b : Fin (r + 1)) : h *ᵥ fvec k r z b = fvec k r z b := by
  unfold fvec
  split_ifs with hb
  · exact (hh.2.1 _).1
  · exact hh.2.2

lemma unipotent_fixes_frame_vector (hU : UMapFrame) {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : StdZ k r z)
    {n0 : B.Mat k r} (hn : n0 ∈ N0set k r z) (b : Fin (r + 1)) :
    n0 *ᵥ fvec k r z b = fvec k r z b := by
  have hS : n0 ∈ Sset k r z := ⟨1, one_mem_UW k r z, n0, hn.1, (Matrix.one_mul _).symm⟩
  rw [((hU k r z hz).1 n0 hS).1 b, hn.2]
  simp [Matrix.one_apply]

lemma sg_frame (hU : UMapFrame) (hT : TauMem) (hG : GVGroup) {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} (hz : StdZ k r z) {n0 h : B.Mat k r}
    {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hn : n0 ∈ N0set k r z) (hv : v ∈ UTset (r + 1)) (hh : h ∈ UWset k r z) :
    n0 * tauM k r z v * h ∈ B.GV k r ∧
      ∀ b, (n0 * tauM k r z v * h) *ᵥ fvec k r z b = fmul k r z v b := by
  obtain ⟨hτN, hτf, -⟩ := hT k r z hz v hv
  have hmul := (hG k r).1
  refine ⟨hmul _ (hmul _ hn.1.1 _ hτN.1) _ hh.1, fun b => ?_⟩
  rw [← Matrix.mulVec_mulVec, UW_fix hh, ← Matrix.mulVec_mulVec, hτf b]
  simp only [fmul, Matrix.mulVec_sum, Matrix.mulVec_smul, unipotent_fixes_frame_vector hU hz hn]

theorem frameS_of (hU : UMapFrame) (hG : GVGroup) : FrameS := by
  intro k r z hz s hs
  have hs' := hs
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  obtain ⟨hf, hut, -⟩ := (hU k r z hz).1 _ hs'
  exact ⟨(hG k r).1 _ hh.1 _ hm.1, uMap k r z (h * m), hut, hf⟩

theorem frameSg_of (hU : UMapFrame) (hT : TauMem) (hG : GVGroup) : FrameSg := by
  intro k r z z' γ hstd σ hσ
  obtain ⟨n0, hn, v, hv, hvL, h, hh, rfl⟩ := hσ
  obtain ⟨h1, h2⟩ := sg_frame hU hT hG hstd.2.1 hn hv hh
  exact ⟨h1, v, hv, hvL, h2⟩

theorem frameSg'_of (hU : UMapFrame) (hT : TauMem) (hG : GVGroup) : FrameSg' := by
  intro k r z z' γ hstd σ hσ
  obtain ⟨n0, hn, v, hv, hPv, h, hh, rfl⟩ := hσ
  obtain ⟨h1, h2⟩ := sg_frame hU hT hG hstd.2.2 hn hv hh
  exact ⟨h1, v, hv, hPv, h2⟩

end PI.PolynomialProperness
