import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLLieGrpGeo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTKLineCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

namespace KLR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem exp_intertwine {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) (D' : Wq →L[ℂ] Wq)
    (D : Wp →L[ℂ] Wp) (h : A.comp D' = D.comp A) :
    A.comp (NormedSpace.exp D') = (NormedSpace.exp D).comp A := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : CompleteSpace Wq := FiniteDimensional.complete ℂ Wq
  have hp : ∀ n : ℕ, A.comp (D' ^ n) = (D ^ n).comp A := by
    intro n
    induction n with
    | zero => ext v; simp
    | succ n ih =>
      ext v
      have e1 := congrArg (fun T : Wq →L[ℂ] Wp => T (D' v)) ih
      have e2 := congrArg (fun T : Wq →L[ℂ] Wp => T v) h
      simp only [ContinuousLinearMap.comp_apply] at e1 e2 ⊢
      rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, e1, e2]
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) D'
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) D
  have g1 := h1.map (ContinuousLinearMap.compL ℂ Wq Wq Wp A) (ContinuousLinearMap.continuous _)
  have g2 := h2.map ((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip A) (ContinuousLinearMap.continuous _)
  have e : ((ContinuousLinearMap.compL ℂ Wq Wq Wp A) ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • D' ^ n) =
      (((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip A) ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • D ^ n) := by
    funext n
    simp only [Function.comp_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, hp]
  rw [e] at g1
  exact g1.unique g2

theorem exp_conj {g : Mx k r} (hg : IsUnit g.det) (X : Mx k r) :
    NormedSpace.exp (g * X * g⁻¹) = g * NormedSpace.exp X * g⁻¹ := by
  have h := HermitianFormRankFour.exp_semiconj (g * X * g⁻¹) X g (by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg, Matrix.mul_one])
  calc NormedSpace.exp (g * X * g⁻¹) = NormedSpace.exp (g * X * g⁻¹) * g * g⁻¹ := by
        rw [Matrix.mul_assoc (NormedSpace.exp (g * X * g⁻¹)) g g⁻¹, Matrix.mul_nonsing_inv _ hg, Matrix.mul_one]
    _ = g * NormedSpace.exp X * g⁻¹ := by rw [h]

theorem pi_exp_frame {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} (hπ : Qr.IsRepW k r z π) {m : ℕ}
    {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r [z] Bs) (B : Matrix (Fin m) (Fin m) ℂ)
    (hBs : Bᴴ = -B) :
    InLieW k r z (∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2) ∧
    π (NormedSpace.exp (∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2)) =
      NormedSpace.exp (∑ p : Fin m × Fin m, B p.1 p.2 • ecOp π (unitB (Hpk k r) Bs p.1 p.2)) := by
  obtain ⟨X, hX⟩ : ∃ X, X = ∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2 := ⟨_, rfl⟩
  rw [← hX]
  have hsk : Xᴴ * Hpk k r + Hpk k r * X = 0 := by
    rw [hX, ← KLG.sum_unitB]
    exact HermitianFormRankFour.skew_of Qx8.hpk_herm hBs
  have hs := HermitianFormSums.ec_sum elementary_lie_elements hπ Finset.univ (fun p : Fin m × Fin m => B p.1 p.2)
    (fun p => unitB (Hpk k r) Bs p.1 p.2) (fun p => frame_lie hB p.1 p.2) 0 (SkewHermitianParts.inGl_zero z)
  beta_reduce at hs
  rw [← hX] at hs
  have hL : InLieW k r z X := by
    have := hs.1.1
    rwa [SkewHermitianParts.hpart1_skew hsk] at this
  have he : ecOp π X = dOp π X := by
    unfold ecOp
    rw [SkewHermitianParts.hpart1_skew hsk, SkewHermitianParts.hpart2_skew hsk, SkewHermitianParts.dOp_zero, smul_zero, add_zero]
  refine ⟨hL, ?_⟩
  have h2 := representation_exp W k r z π hπ X hL 1
  simp only [Complex.ofReal_one, one_smul] at h2
  rw [h2, ← he, hs.2]

end KLR

open KLR in
theorem lie_group_realization : KLLieGrp := by
  intro Wp Wq _ _ _ _ _ _ k r z z' π π' hz hz' hT hT' hπ hπ' g hg hGG Fr hFr A hA h hh h' hh' hgh
  have hgu := hg.1
  have hgU : IsUnit g.det := WeylGroupFacts.isUnit_of_uh hgu
  have hhU : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hh.1
  have cancel : ∀ M : Mx k r, IsUnit M.det → ∀ v, M⁻¹ *ᵥ (M *ᵥ v) = v := fun M hM v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]
  obtain ⟨y, hy⟩ : ∃ y, y = g⁻¹ *ᵥ z := ⟨_, rfl⟩
  rw [← hy] at hFr
  have hgy : g *ᵥ y = z := by rw [hy]; exact Qx8.inv_mulVec_uh hgu z
  have hginv : g⁻¹ ∈ Glev k r (Fin.last r) := FrameEntries.glev_inv hg
  have hyW : inWb k r y := by rw [hy]; exact Qx8.inWb_mulVec hginv hz
  have hyy : herm (Hpk k r) y y = -((Tz k r z : ℝ) : ℂ) := by
    rw [← Qx8.herm_self', ← hgy, Qx8.herm_UH hgu]
  have hζ : herm (Hpk k r) z' y = zetaL k r z z' (Fin.last r) g := by
    unfold zetaL
    rw [Qx8.fvec_last, Qx8.fvec_last, ← hgy, Qx8.herm_UH hgu]
  have hpos := Qx8.GGl_pos hz hz' hT hT' hg hGG
  have hG2 : 0 < Complex.normSq (herm (Hpk k r) y z') - Tz k r z * Tz k r z' := by
    rw [← Qx8.herm_conj, hζ]
    have hc : Complex.normSq (star (zetaL k r z z' (Fin.last r) g)) = Complex.normSq (zetaL k r z z' (Fin.last r) g) :=
      Complex.normSq_conj _
    rw [hc]
    exact hpos
  obtain ⟨e', s, c, hs, he', he'W, he'z, he'e⟩ := Qx8.orth_unit hyW hz' hT' hyy (Qx8.herm_self' z') hG2
  have hFz' : ∀ a, herm (Hpk k r) (Fr a) z' = 0 := fun a => hFr.2.2 a z' (by simp)
  have hFy : ∀ a, herm (Hpk k r) (Fr a) y = 0 := fun a => hFr.2.2 a y (by simp)
  have hFe : ∀ a, herm (Hpk k r) (Fr a) e' = 0 := by
    intro a
    rw [he', Qx8.herm_smul_right', Qx8.herm_add_right', Qx8.herm_smul_right', hFy, hFz']
    simp
  have hFr2 : IsFrameOf k r [z', e'] Fr := ⟨hFr.1, hFr.2.1, fun a v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hFz' a
    · exact hFe a⟩
  have hFz'1 : IsFrameOf k r [z'] Fr := ⟨hFr.1, hFr.2.1, fun a v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv
    exact hFz' a⟩

  have e1 : h *ᵥ (g *ᵥ (h' *ᵥ y)) = h *ᵥ z := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgh, hgy, hh.2.2]
  have e2 : g *ᵥ (h' *ᵥ y) = z := by
    rw [← cancel h hhU (g *ᵥ (h' *ᵥ y)), e1, cancel h hhU z]
  have hh'y : h' *ᵥ y = y := by
    calc h' *ᵥ y = g⁻¹ *ᵥ (g *ᵥ (h' *ᵥ y)) := (cancel g hgU _).symm
      _ = y := by rw [e2, hy]
  have hh'e : h' *ᵥ e' = e' := by
    rw [he', Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hh'y, hh'.2.2]

  obtain ⟨B, hBs, hBe⟩ := KLG.stab_exp hz' hT' he'W he'z he'e hFr2 hh' hh'e
  rw [KLG.sum_unitB] at hBe
  obtain ⟨-, hE'⟩ := pi_exp_frame hπ' hFz'1 B hBs
  have hgF : IsFrameOf k r [z] (fun a => g *ᵥ Fr a) := ⟨fun a => Qx8.inWb_mulVec hg (hFr.1 a), fun a b => by
    rw [Qx8.herm_UH hgu]; exact hFr.2.1 a b, fun a v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv
    rw [← hgy, Qx8.herm_UH hgu]
    exact hFy a⟩
  obtain ⟨hL, hE⟩ := pi_exp_frame hπ hgF B hBs
  have hconj : g * h' * g⁻¹ = NormedSpace.exp
      (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • unitB (Hpk k r) (fun a => g *ᵥ Fr a) p.1 p.2) := by
    have hsum : (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • unitB (Hpk k r) (fun a => g *ᵥ Fr a) p.1 p.2) =
        g * (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • unitB (Hpk k r) Fr p.1 p.2) * g⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, Qx8.unitB_conj Fr p.1 p.2 hgu]
    rw [hsum, ← hBe]
    exact (exp_conj hgU _).symm
  have hD : A.comp (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • ecOp π' (unitB (Hpk k r) Fr p.1 p.2)) =
      (∑ p : Fin (k - 1) × Fin (k - 1), B p.1 p.2 • ecOp π (unitB (Hpk k r) (fun a => g *ᵥ Fr a) p.1 p.2)).comp A := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      map_sum, map_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    exact hA p.1 p.2 v
  have hX := exp_intertwine A _ _ hD
  rw [← hE', ← hE, hBe, ← hconj] at hX
  have hmem : g * h' * g⁻¹ ∈ UWset k r z := by
    rw [hconj]
    have := exp_uw hL 1
    simpa using this
  have hone : h * (g * h' * g⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgh, Matrix.mul_nonsing_inv _ hgU]
  rw [hX, ← ContinuousLinearMap.comp_assoc, ← hπ.1.2 h hh _ hmem, hone, hπ.1.1]
  ext v
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
