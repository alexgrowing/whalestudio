import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs

set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact

section Alg

variable {R : Type} [CommRing R] {s : R →+* R} {n r : ℕ} {Jm : Matrix (Fin n) (Fin n) R}
  {Xm Ym : Matrix (Fin n) (Fin r) R} {M N : Matrix (Fin n) (Fin n) R}

theorem hform_eq_dot (s : R →+* R) (H : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) :
    Formalism.UG.hform s H x y = (fun i => s (x i)) ⬝ᵥ (H *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem comp_mulVec (s : R →+* R) (P : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    (fun i => s ((P *ᵥ x) i)) = (fun i => s (x i)) ᵥ* cT s P := by
  funext i
  simp only [mulVec, vecMul, dotProduct, map_sum, map_mul, cT, Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem hform_mulVec (s : R →+* R) (P H : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    Formalism.UG.hform s H (P *ᵥ x) (P *ᵥ x) = Formalism.UG.hform s (cT s P * H * P) x x := by
  rw [hform_eq_dot, hform_eq_dot, comp_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mul_assoc,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem hform_smul (s : R →+* R) (c : R) (H : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) :
    Formalism.UG.hform s (c • H) x y = c * Formalism.UG.hform s H x y := by
  simp only [Formalism.UG.hform, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem cT_diagonal (s : R →+* R) (d : Fin r → R) : cT s (diagonal d) = diagonal fun i => s (d i) := by
  ext i j
  by_cases e : i = j
  · subst e; simp [cT]
  · simp [cT, Matrix.diagonal_apply, e, Ne.symm e]

theorem coef_row (hU : cT s M * Jm * M = Jm) (hMN : M * N = 1) {P : Matrix (Fin n) (Fin r) R} {d : Fin r → R}
    (hP : M * P = P * diagonal d) : cT s P * Jm * N = cT s (diagonal d) * (cT s P * Jm) := by
  have e := pgram_unitary hU P N
  rw [hMN, Matrix.mul_one, hP, Formalism.UG.cT_mul] at e
  rw [← e, Matrix.mul_assoc]

theorem col_inv (hNM : N * M = 1) {P : Matrix (Fin n) (Fin r) R} {D A : Matrix (Fin r) (Fin r) R}
    (hP : M * P = P * D) (hDA : D * A = 1) : N * P = P * A := by
  calc N * P = N * (P * (D * A)) := by rw [hDA, Matrix.mul_one]
    _ = N * (M * P) * A := by rw [hP]; simp only [Matrix.mul_assoc]
    _ = P * A := by rw [← Matrix.mul_assoc, hNM, Matrix.one_mul]

theorem diag_rel (hF : PFr s Jm Xm Ym) (hU : cT s M * Jm * M = Jm) {d d' : Fin r → R}
    (hX : M * Xm = Xm * diagonal d) (hY : M * Ym = Ym * diagonal d') (i : Fin r) : s (d i) * d' i = 1 := by
  have e := pgram_unitary hU Xm Ym
  rw [hX, hY, hF.xy, Formalism.UG.cT_mul] at e
  have e2 : cT s (diagonal d) * diagonal d' = 1 := by
    rw [← e]
    have : cT s (diagonal d) * cT s Xm * Jm * (Ym * diagonal d') =
        cT s (diagonal d) * (cT s Xm * Jm * Ym) * diagonal d' := by simp only [Matrix.mul_assoc]
    rw [this, hF.xy, Matrix.mul_one]
  have := congrFun (congrFun e2 i) i
  rwa [cT_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this

theorem line_conj (hss : ∀ x, s (s x) = x) (hU : cT s M * Jm * M = Jm) (hMN : M * N = 1)
    {P : Matrix (Fin n) (Fin r) R} {d : Fin r → R} (hP : M * P = P * diagonal d) (i : Fin r) :
    cT s N * vecMulVec (fun k => s ((cT s P * Jm) i k)) ((cT s P * Jm) i) * N =
      (d i * s (d i)) • vecMulVec (fun k => s ((cT s P * Jm) i k)) ((cT s P * Jm) i) := by
  have hrow : (cT s P * Jm) i ᵥ* N = s (d i) • (cT s P * Jm) i := by
    rw [← Matrix.mul_apply_eq_vecMul, coef_row hU hMN hP, cT_diagonal]
    funext k
    simp [Matrix.diagonal_mul]
  have hcol : cT s N *ᵥ (fun k => s ((cT s P * Jm) i k)) = fun k => s (((cT s P * Jm) i ᵥ* N) k) := by
    funext k
    simp only [mulVec, vecMul, dotProduct, map_sum, map_mul, cT, Matrix.transpose_apply, Matrix.map_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hcol, hrow]
  ext a b
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, map_mul, hss]
  ring

theorem aniso_conj (hF : PFr s Jm Xm Ym) (hU : cT s M * Jm * M = Jm) (hUN : cT s N * Jm * N = Jm) (hMN : M * N = 1)
    (hNM : N * M = 1) {d d' : Fin r → R} (hX : M * Xm = Xm * diagonal d) (hY : M * Ym = Ym * diagonal d')
    (P : Matrix (Fin n) (Fin n) R) (hPe : P = 1 - Xm * (cT s Ym * Jm) - Ym * (cT s Xm * Jm)) :
    cT s N * (cT s P * Jm * P) * N = cT s P * Jm * P := by
  have hrel := diag_rel hF hU hX hY
  have h1 : diagonal d * cT s (diagonal d') = 1 := by
    rw [cT_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have := congrArg s (hrel i)
    rwa [map_mul, hF.ss, map_one] at this
  have h2 : diagonal d' * cT s (diagonal d) = 1 := by
    rw [cT_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hrel i
  have hc : N * P = P * N := by
    rw [hPe, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      ← Matrix.mul_assoc N Xm, ← Matrix.mul_assoc N Ym, col_inv hNM hX h1, col_inv hNM hY h2,
      Matrix.mul_assoc Xm, Matrix.mul_assoc Ym, Matrix.mul_assoc Xm, Matrix.mul_assoc Ym,
      coef_row hU hMN hX, coef_row hU hMN hY]
  have e := pgram_unitary hUN P P
  rw [hc] at e
  have e2 : cT s N * (cT s P * Jm * P) * N = cT s (P * N) * Jm * (P * N) := by
    rw [Formalism.UG.cT_mul]
    simp only [Matrix.mul_assoc]
  rw [e2, e]

end Alg

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n r : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

theorem hform_ratV (H : Matrix (Fin n) (Fin n) E) (ξ : Fin n → E) :
    Formalism.UG.hform (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (JR (F := F) (AF F) H) (ratV F ξ) (ratV F ξ) =
      inclR (F := F) (AF F) (hE σ H ξ ξ) := by
  simp only [Formalism.UG.hform, hE, ratV, JR, Matrix.map_apply, sigRA_inclR, map_sum, map_mul]
  rfl

theorem hR_of_conj (hH : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (c : AF F ⊗[F] E)
    (h : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) P * JR (F := F) (AF F) hH * P = c • JR (F := F) (AF F) hH) (ξ : Fin n → E) :
    hR (AF F) σ hH (P *ᵥ ratV F ξ) (P *ᵥ ratV F ξ) = c * inclR (F := F) (AF F) (hE σ hH ξ ξ) := by
  change Formalism.UG.hform _ _ _ _ = _
  rw [hform_mulVec, h, hform_smul, hform_ratV]

theorem rows_map (J : Matrix (Fin n) (Fin n) E) (C : Matrix (Fin n) (Fin r) E) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F C) * JR (F := F) (AF F) J =
      (cT (σ : E →+* E) C * J).map (inclR (F := F) (AF F)) := by
  unfold JR
  rw [← cT_map_inclR, ← Matrix.map_mul]

theorem JR_normMat (C : Matrix (Fin n) (Fin r) E) (i : Fin r) :
    JR (F := F) (AF F) (normMat σ (rowOf σ J C i)) =
      vecMulVec (fun k => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ
          ((cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F C) * JR (F := F) (AF F) J) i k))
        ((cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F C) * JR (F := F) (AF F) J) i) := by
  rw [rows_map]
  ext a b
  simp [JR, normMat, rowOf, vecMulVec_apply, sigRA_inclR, -Matrix.map_mul]

theorem sum_lineProj (C D : Matrix (Fin n) (Fin r) E) :
    ∑ i, lineProj σ J C D i = C * (cT (σ : E →+* E) D * J) := by
  ext a b
  rw [Matrix.sum_apply, Matrix.mul_apply]
  rfl

theorem anisoProj_eq : anisoProj σ J X Y = 1 - X * (cT (σ : E →+* E) Y * J) - Y * (cT (σ : E →+* E) X * J) := by
  rw [anisoProj, Fintype.sum_sum_type]
  simp only [projFam, Sum.elim_inl, Sum.elim_inr]
  rw [sum_lineProj, sum_lineProj, sub_add_eq_sub_sub]

theorem adMat_anisoProj : adMat F (anisoProj σ J X Y) =
    1 - adMat F X * (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F Y) * JR (F := F) (AF F) J) -
      adMat F Y * (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F X) * JR (F := F) (AF F) J) := by
  rw [rows_map, rows_map, anisoProj_eq, ← Matrix.map_mul, ← Matrix.map_mul]
  ext a b
  simp [Matrix.one_apply, apply_ite (inclR (F := F) (AF F)), -Matrix.map_mul]

theorem JR_aniso : JR (F := F) (AF F) (hermFam σ J X Y none) =
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F (anisoProj σ J X Y)) * JR (F := F) (AF F) J * adMat F (anisoProj σ J X Y) := by
  change JR (F := F) (AF F) (cT (σ : E →+* E) (anisoProj σ J X Y) * J * anisoProj σ J X Y) = _
  unfold JR
  rw [Matrix.map_mul, Matrix.map_mul, cT_map_inclR]

theorem idele_norm (h : IsCMExt F E σ) (u : (AF F ⊗[F] E)ˣ) (hu : GlobalTheory.Doubling.absE F E u = 1) :
    ∃ t : GroundTheory.Global.IdeleGroup F, (GroundTheory.Global.IdeleGroup.ideleModule F t : ℝ) = 1 ∧
      algebraMap (AF F) (AF F ⊗[F] E) (t : AF F) = u.1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ u.1 := by
  refine ⟨Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) u, ?_, GlobalTheory.Doubling.algebraMap_norm_eq h _⟩
  have h2 : ∀ v : (AF F)ˣ, (((GlobalTheory.WeilM.adeleClass F).modu v : ℝ≥0) : ℝ) =
      (GroundTheory.Global.IdeleGroup.ideleModule F v : ℝ) := fun v => by
    change (distribHaarChar (AdeleRing (𝓞 F) F) v : ℝ) = _
    exact GlobalTheory.ModuAdele.distribHaarChar_adeleRing F v
  rw [← h2, GlobalTheory.ModuAdele.modu_norm_eq_absE, hu]
  simp

theorem idele_norm_inv (h : IsCMExt F E σ) (u : (AF F ⊗[F] E)ˣ) (hu : GlobalTheory.Doubling.absE F E u = 1)
    (e : AF F ⊗[F] E) (he : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ u.1 * e = 1) :
    ∃ t : GroundTheory.Global.IdeleGroup F, (GroundTheory.Global.IdeleGroup.ideleModule F t : ℝ) = 1 ∧
      algebraMap (AF F) (AF F ⊗[F] E) (t : AF F) = e * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ e := by
  obtain ⟨t, ht, e1⟩ := idele_norm h u hu
  refine ⟨t⁻¹, ?_, ?_⟩
  · have e0 : GroundTheory.Global.IdeleGroup.ideleModule F t = 1 := Subtype.ext ht
    rw [map_inv, e0, inv_one]
    rfl
  · have h1 : algebraMap (AF F) (AF F ⊗[F] E) ((t⁻¹ : GroundTheory.Global.IdeleGroup F) : AF F) *
        algebraMap (AF F) (AF F ⊗[F] E) (t : AF F) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h3 := congrArg (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) he
    rw [map_mul, sigRA_sigRA σ h, map_one] at h3
    have h2 : algebraMap (AF F) (AF F ⊗[F] E) (t : AF F) * (e * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ e) = 1 := by
      rw [e1]
      calc _ = (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ u.1 * e) * (u.1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ e) := by ring
        _ = 1 := by rw [he, h3, one_mul]
    exact left_inv_eq_right_inv h1 h2

end Adelic

theorem hermFam_levi_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ m ∈ leviMin σ J X Y, m ∈ minParOne σ J X → ∀ j, ∃ s : GroundTheory.Global.IdeleGroup F, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ) ∧ ∀ ξ : Fin n → E, hR (AF F) σ (hermFam σ J X Y j) ((matHom _ σ J m⁻¹).1 *ᵥ ratV F ξ) ((matHom _ σ J m⁻¹).1 *ᵥ ratV F ξ) = algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) (hE σ (hermFam σ J X Y j) ξ ξ) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW m hm hm1 j
  obtain ⟨d, d', hX, hY⟩ := hm
  obtain ⟨B, hB, hXB, hu⟩ := hm1
  have hF := pfrA h hJ hW
  have hBd : diagonal d = B := (Bm_eq hF hX).symm.trans (Bm_eq hF hXB)
  have hU := unitaryA_matHom m
  have hUN := unitaryA_matHom m⁻¹
  have hMN : (matHom _ σ J m).1 * (matHom _ σ J m⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hNM : (matHom _ σ J m⁻¹).1 * (matHom _ σ J m).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hunit : ∀ i, ∃ u : (AF F ⊗[F] E)ˣ, d i = u ∧ GlobalTheory.Doubling.absE F E u = 1 := fun i => by
    obtain ⟨u, e, e'⟩ := hu i
    exact ⟨u, by rw [← e, ← hBd, Matrix.diagonal_apply_eq], e'⟩
  rcases j with _ | i | i
  · refine ⟨1, ?_, fun ξ => ?_⟩
    · rw [map_one]
      exact le_refl _
    · rw [Units.val_one, map_one]
      refine hR_of_conj _ _ 1 ?_ ξ
      rw [one_smul, JR_aniso]
      exact aniso_conj hF hU hUN hMN hNM hX hY _ adMat_anisoProj
  · obtain ⟨u, e, hu1⟩ := hunit i
    obtain ⟨t, ht, et⟩ := idele_norm_inv h u hu1 (d' i) (by rw [← e]; exact diag_rel hF hU hX hY i)
    refine ⟨t, ht.ge, fun ξ => ?_⟩
    refine hR_of_conj _ _ _ ?_ ξ
    rw [et]
    change cT _ _ * JR (F := F) (AF F) (normMat σ (rowOf σ J Y i)) * _ = _ • JR (F := F) (AF F) (normMat σ (rowOf σ J Y i))
    rw [JR_normMat]
    exact line_conj hF.ss hU hMN hY i
  · obtain ⟨u, e, hu1⟩ := hunit i
    obtain ⟨t, ht, et⟩ := idele_norm h u hu1
    refine ⟨t, ht.ge, fun ξ => ?_⟩
    refine hR_of_conj _ _ _ ?_ ξ
    rw [et, ← e]
    change cT _ _ * JR (F := F) (AF F) (normMat σ (rowOf σ J X i)) * _ = _ • JR (F := F) (AF F) (normMat σ (rowOf σ J X i))
    rw [JR_normMat]
    exact line_conj hF.ss hU hMN hX i

end GlobalTheory.CompanionTheory.ParCocompact

end
