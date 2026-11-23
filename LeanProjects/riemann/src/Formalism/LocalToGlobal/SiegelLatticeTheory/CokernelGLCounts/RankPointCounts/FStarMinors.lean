import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarFrame

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem lm_one {N l : ℕ} (hl : l ≤ N) : leadMinorE (1 : Matrix (Fin N) (Fin N) E) l = 1 := by
  unfold leadMinorE
  rw [dif_pos hl, Matrix.submatrix_one _ (Fin.castLE_injective hl), Matrix.det_one]

theorem lm_diag_right {N : ℕ} (X Dg : Matrix (Fin N) (Fin N) E) (hD : ∀ c b, c ≠ b → Dg c b = 0) (l : ℕ) :
    leadMinorE (X * Dg) l = leadMinorE X l * leadMinorE Dg l := by
  unfold leadMinorE
  split_ifs with h
  · have hsub : (X * Dg).submatrix (Fin.castLE h) (Fin.castLE h) =
        X.submatrix (Fin.castLE h) (Fin.castLE h) * Dg.submatrix (Fin.castLE h) (Fin.castLE h) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [Formalism.L2.SG.Pf.sum_castLE_td h]
      intro d hd
      have hj := j.isLt
      rw [hD d _ (fun e => by have h1 := congrArg Fin.val e; simp at h1; omega), mul_zero]
    rw [hsub, Matrix.det_mul]
  · simp

theorem zhatOM_one_eq {r : ℕ} :
    ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) = Matrix.diagonal fun b => (-1 : E) ^ (r - b.val) := by
  ext a b
  simp only [ZhatOM, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h; rw [mul_one]
  · rw [mul_zero]

theorem zhatOM_eq_mul {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ZhatOM X = X * ZhatOM 1 := by
  rw [zhatOM_one_eq]
  ext a b
  rw [Matrix.mul_diagonal]
  simp only [ZhatOM]
  rw [mul_comm]

theorem zhatOM_zhatOM {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ZhatOM (ZhatOM X) = X := by
  ext a b
  simp only [ZhatOM]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

theorem lm_zhatOM {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (l : ℕ) :
    leadMinorE (ZhatOM X) l = leadMinorE X l * leadMinorE (ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) l := by
  rw [zhatOM_eq_mul X]
  refine lm_diag_right X _ (fun c b hcb => ?_) l
  rw [zhatOM_one_eq, Matrix.diagonal_apply_ne _ hcb]

theorem lm_sign_ne {r l : ℕ} (hl : l ≤ r + 1) :
    leadMinorE (ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) l ≠ 0 := by
  intro h0
  have := lm_zhatOM (ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) l
  rw [zhatOM_zhatOM, lm_one hl, h0, mul_zero] at this
  exact one_ne_zero this

theorem lm_cell {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (w : Point E (r + 1))
    (h : IsInCell (ZhatOM X) w) (l : ℕ) :
    leadMinorE X l * leadMinorE (ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) l = leadMinorE (ptMat w) l := by
  obtain ⟨L, U, hL, hU, hX⟩ := h
  rw [← lm_zhatOM, hX]
  exact Formalism.L2.SG.Pf.leadMinor_uni L (ptMat w) U (fun a c h => (hL a c).1 h) (fun a => (hL a a).2 rfl)
    (fun d b h => (hU d b).1 h) (fun b => (hU b b).2 rfl) l

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem starDmin_eq (w : Point D.host.E (D.R.rS + 1)) (l : ℕ) : Dmin w l = leadMinorE (ptMat w) l := by
  unfold Dmin leadMinorE
  split_ifs <;> rfl

theorem starRepF_rep (γ : TermDef.Term D u u' F0 what₂) :
    Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls (repF γ) := by
  unfold repF
  rcases hn : nrep γ with _ | x
  · exact ⟨(Quot.out γ.cls).2, Quot.out_eq _⟩
  · unfold nrep at hn
    split_ifs at hn with h
    cases hn
    exact h.choose_spec.1

theorem star_frame_cell_minor (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (hγ : EligAt γ w)
    (l : ℕ) : leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) l *
      leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l = leadMinorE (ptMat w) l := by
  obtain ⟨F', ⟨h1, h1e⟩, -, hcell⟩ := hγ.2
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hrel := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F', h1⟩ ⟨repF γ, h2⟩).1
    (h1e.trans h2e.symm)
  have hc := Formalism.L2.SG.Pf.cell_rel (lf D F0) hrel w hcell
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  have hZ : starZh (frame (lf D F0)) (starFrame γ) =
      1 * ZhatL (lf D F0) (repF γ) * (Matrix.of fun a b => (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a b : 𝓞 D.host.E) : D.host.E)) := by
    rw [Matrix.one_mul]
    exact FsLA.gram_comb_left (S := VS D) (frame (repF γ)) _ (frame (lf D F0))
  rw [hZ, Formalism.L2.SG.Pf.leadMinor_uni 1 _ _ (fun a c h => Matrix.one_apply_ne (ne_of_lt h)) (fun a => Matrix.one_apply_eq a)
    (fun d b h => by simp [Matrix.of_apply, hξ1 d b h]) (fun b => by simp [Matrix.of_apply, hξ2 b]) l]
  exact FsLA.lm_cell _ w hc l

variable (u u' F0 what₂)

theorem starMinors_holds : StarMinors u u' F0 what₂ := by
  intro γ Z hC
  obtain ⟨w, hγ, w', -, hk, hZ⟩ := hC
  have hs : ∀ l, l ≤ D.R.rS + 1 →
      leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l ≠ 0 :=
    fun l hl => FsLA.lm_sign_ne hl
  have c1 := star_frame_cell_minor γ w hγ
  have c2 := FsLA.lm_cell Z w' hZ
  have hdet : ∀ v : Point D.host.E (D.R.rS + 1), leadMinorE (ptMat v) (D.R.rS + 1) ≠ 0 := fun v => by
    rw [FsLA.leadMinorE_full]; exact Formalism.L2.SG.Pf.det_ptMat_ne v
  have hcross : Dmin w D.R.rS * Dmin w' (D.R.rS + 1) = Dmin w' D.R.rS * Dmin w (D.R.rS + 1) := by
    unfold kind at hk
    by_cases h0 : Dmin w D.R.rS = 0
    · rw [if_pos h0] at hk
      have h0' : Dmin w' D.R.rS = 0 := by
        by_contra h; rw [if_neg h] at hk; cases hk
      rw [h0, h0', zero_mul, zero_mul]
    · rw [if_neg h0] at hk
      have h0' : Dmin w' D.R.rS ≠ 0 := by
        intro h; rw [if_pos h] at hk; cases hk
      rw [if_neg h0'] at hk
      have hz := Option.some.inj hk
      unfold zetaOf at hz
      field_simp at hz
      linear_combination hz
  rw [starDmin_eq, starDmin_eq, starDmin_eq, starDmin_eq, ← c1, ← c1, ← c2, ← c2] at hcross
  refine ⟨?_, ?_, ?_⟩
  · rw [← FsLA.leadMinorE_full]
    intro h; apply hdet w'; rw [← c2, h, zero_mul]
  · rw [← FsLA.leadMinorE_full]
    intro h; apply hdet w; rw [← c1, h, zero_mul]
  · rw [← FsLA.leadMinorE_full, ← FsLA.leadMinorE_full]
    have hr := hs D.R.rS (Nat.le_succ _)
    have hr1 := hs (D.R.rS + 1) le_rfl
    apply mul_right_cancel₀ (mul_ne_zero hr hr1)
    linear_combination hcross

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
