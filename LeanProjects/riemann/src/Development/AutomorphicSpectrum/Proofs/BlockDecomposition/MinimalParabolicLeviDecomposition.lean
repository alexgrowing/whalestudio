import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.LeviDecomp

section Block

variable {n r : ℕ} {R : Type} [CommRing R]

def piM (X Y : Matrix (Fin n) (Fin r) R) (Xs Ys : Matrix (Fin r) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  1 - X * Ys - Y * Xs

def leviM (X Y : Matrix (Fin n) (Fin r) R) (Xs Ys : Matrix (Fin r) (Fin n) R) (D D' : Matrix (Fin r) (Fin r) R)
    (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  X * (D * Ys) + Y * (D' * Xs) + piM X Y Xs Ys * (g * piM X Y Xs Ys)

variable {X Y : Matrix (Fin n) (Fin r) R} {Xs Ys : Matrix (Fin r) (Fin n) R}

theorem piM_mul_X (hxx : Xs * X = 0) (hyx : Ys * X = 1) : piM X Y Xs Ys * X = 0 := by
  simp only [piM, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hxx, hyx, Matrix.mul_one, Matrix.mul_zero, sub_self,
    sub_zero]

theorem piM_mul_Y (hxy : Xs * Y = 1) (hyy : Ys * Y = 0) : piM X Y Xs Ys * Y = 0 := by
  simp only [piM, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hxy, hyy, Matrix.mul_one, Matrix.mul_zero, sub_self,
    sub_zero]

theorem Xs_mul_piM (hxx : Xs * X = 0) (hxy : Xs * Y = 1) : Xs * piM X Y Xs Ys = 0 := by
  simp only [piM, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hxx, hxy, Matrix.zero_mul, Matrix.one_mul, sub_self,
    sub_zero]

theorem Ys_mul_piM (hyx : Ys * X = 1) (hyy : Ys * Y = 0) : Ys * piM X Y Xs Ys = 0 := by
  simp only [piM, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hyx, hyy, Matrix.zero_mul, Matrix.one_mul, sub_self,
    sub_zero]

theorem piM_mul (W : Matrix (Fin n) (Fin n) R) : piM X Y Xs Ys * W = W - X * (Ys * W) - Y * (Xs * W) := by
  simp only [piM, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]

theorem piM_idem (hxx : Xs * X = 0) (hxy : Xs * Y = 1) (hyx : Ys * X = 1) (hyy : Ys * Y = 0) :
    piM X Y Xs Ys * piM X Y Xs Ys = piM X Y Xs Ys := by
  rw [piM_mul, Xs_mul_piM hxx hxy, Ys_mul_piM hyx hyy, Matrix.mul_zero, Matrix.mul_zero, sub_zero, sub_zero]

theorem mul_piM_mul {g h : Matrix (Fin n) (Fin n) R} {B C : Matrix (Fin r) (Fin r) R} (hxx : Xs * X = 0)
    (hxy : Xs * Y = 1) (hgh : g * h = 1) (hgX : g * X = X * B) (hC : Xs * h = C * Xs) :
    g * (piM X Y Xs Ys * (h * piM X Y Xs Ys)) =
      piM X Y Xs Ys - X * (B * (Ys * (h * piM X Y Xs Ys))) := by
  have e2 : Xs * (h * piM X Y Xs Ys) = 0 := by
    rw [← Matrix.mul_assoc, hC, Matrix.mul_assoc, Xs_mul_piM hxx hxy, Matrix.mul_zero]
  rw [piM_mul (h * piM X Y Xs Ys), e2, Matrix.mul_zero, sub_zero, Matrix.mul_sub, ← Matrix.mul_assoc g h, hgh,
    Matrix.one_mul, ← Matrix.mul_assoc g X, hgX, Matrix.mul_assoc]

theorem piM_sandwich {g h : Matrix (Fin n) (Fin n) R} {B C : Matrix (Fin r) (Fin r) R} (hxx : Xs * X = 0)
    (hxy : Xs * Y = 1) (hyx : Ys * X = 1) (hyy : Ys * Y = 0) (hgh : g * h = 1) (hgX : g * X = X * B)
    (hC : Xs * h = C * Xs) :
    piM X Y Xs Ys * (g * (piM X Y Xs Ys * (h * piM X Y Xs Ys))) = piM X Y Xs Ys := by
  rw [mul_piM_mul hxx hxy hgh hgX hC, Matrix.mul_sub, piM_idem hxx hxy hyx hyy, ← Matrix.mul_assoc (piM X Y Xs Ys) X,
    piM_mul_X hxx hyx, Matrix.zero_mul, sub_zero]

theorem leviM_mul {g h : Matrix (Fin n) (Fin n) R} {D Di D' Di' : Matrix (Fin r) (Fin r) R} (hxx : Xs * X = 0)
    (hxy : Xs * Y = 1) (hyx : Ys * X = 1) (hyy : Ys * Y = 0) (h1 : D * Di = 1) (h2 : D' * Di' = 1)
    (hs : piM X Y Xs Ys * (g * (piM X Y Xs Ys * (h * piM X Y Xs Ys))) = piM X Y Xs Ys) :
    leviM X Y Xs Ys D D' g * leviM X Y Xs Ys Di Di' h = 1 := by
  have a1 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), Ys * (X * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hyx, Matrix.one_mul]
  have a2 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), Xs * (Y * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hxy, Matrix.one_mul]
  have a3 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), Xs * (X * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, hxx, Matrix.zero_mul]
  have a4 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), Ys * (Y * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, hyy, Matrix.zero_mul]
  have a5 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin n) k R), Xs * (piM X Y Xs Ys * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, Xs_mul_piM hxx hxy, Matrix.zero_mul]
  have a6 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin n) k R), Ys * (piM X Y Xs Ys * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, Ys_mul_piM hyx hyy, Matrix.zero_mul]
  have a7 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), piM X Y Xs Ys * (X * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, piM_mul_X hxx hyx, Matrix.zero_mul]
  have a8 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), piM X Y Xs Ys * (Y * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, piM_mul_Y hxy hyy, Matrix.zero_mul]
  have a9 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin n) k R),
      piM X Y Xs Ys * (piM X Y Xs Ys * M) = piM X Y Xs Ys * M := fun M => by
    rw [← Matrix.mul_assoc, piM_idem hxx hxy hyx hyy]
  have b1 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), D * (Di * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have b2 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), D' * (Di' * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  simp only [leviM, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2,
    Matrix.mul_zero, add_zero, zero_add, hs]
  unfold piM
  abel

theorem leviM_mul_X {g : Matrix (Fin n) (Fin n) R} (D D' : Matrix (Fin r) (Fin r) R) (hxx : Xs * X = 0)
    (hyx : Ys * X = 1) : leviM X Y Xs Ys D D' g * X = X * D := by
  simp only [leviM, Matrix.add_mul, Matrix.mul_assoc, hxx, hyx, piM_mul_X hxx hyx, Matrix.mul_one, Matrix.mul_zero,
    add_zero]

theorem leviM_mul_Y {g : Matrix (Fin n) (Fin n) R} (D D' : Matrix (Fin r) (Fin r) R) (hxy : Xs * Y = 1)
    (hyy : Ys * Y = 0) : leviM X Y Xs Ys D D' g * Y = Y * D' := by
  simp only [leviM, Matrix.add_mul, Matrix.mul_assoc, hxy, hyy, piM_mul_Y hxy hyy, Matrix.mul_one, Matrix.mul_zero,
    add_zero, zero_add]

theorem mul_leviM_sub_one {g h : Matrix (Fin n) (Fin n) R} {B C : Matrix (Fin r) (Fin r) R}
    (Di Di' : Matrix (Fin r) (Fin r) R) (hxx : Xs * X = 0) (hxy : Xs * Y = 1) (hgh : g * h = 1)
    (hgX : g * X = X * B) (hC : Xs * h = C * Xs) :
    g * leviM X Y Xs Ys Di Di' h - 1 =
      X * (B * (Di * Ys) - B * (Ys * (h * piM X Y Xs Ys)) - Ys) + (g * (Y * Di') - Y) * Xs := by
  have e1 : (1 : Matrix (Fin n) (Fin n) R) = X * Ys + Y * Xs + piM X Y Xs Ys := by
    unfold piM
    abel
  have e2 : g * (X * (Di * Ys)) = X * (B * (Di * Ys)) := by
    rw [← Matrix.mul_assoc, hgX, Matrix.mul_assoc]
  rw [leviM, Matrix.mul_add, Matrix.mul_add, mul_piM_mul hxx hxy hgh hgX hC, e2]
  generalize Ys * (h * piM X Y Xs Ys) = Q
  rw [e1]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

theorem exists_mulVec_eq {A : Matrix (Fin n) (Fin n) R} {T : Matrix (Fin r) (Fin n) R} {V : Matrix (Fin n) (Fin r) R}
    (hA : A = X * T + V * Xs) {w : Fin n → R} (hw : Xs *ᵥ w = 0) : ∃ a, A *ᵥ w = X *ᵥ a :=
  ⟨T *ᵥ w, by
    rw [hA, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero, add_zero]⟩

end Block

section Frame

variable {n r : ℕ} {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R}
  {X Y : Matrix (Fin n) (Fin r) R}

theorem cT_sub' {a b : Type} (P Q : Matrix a b R) : cT s (P - Q) = cT s P - cT s Q :=
  Matrix.ext fun _ _ => by simp [cT]

theorem cT_add' {a b : Type} (P Q : Matrix a b R) : cT s (P + Q) = cT s P + cT s Q :=
  Matrix.ext fun _ _ => by simp [cT]

theorem cT_diagonal' (d : Fin r → R) : cT s (diagonal d) = diagonal (fun i => s (d i)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [cT]
  · simp [cT, Matrix.diagonal_apply, hij, Ne.symm hij]

theorem cT_piM_mul (hF : PFr s Jm X Y) :
    cT s (piM X Y (cT s X * Jm) (cT s Y * Jm)) * Jm = Jm * piM X Y (cT s X * Jm) (cT s Y * Jm) := by
  simp only [piM, cT_sub', Formalism.UG.cT_one, Formalism.UG.cT_mul, hF.cc, hF.herm, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_assoc]
  abel

theorem cT_leviM_mul (hF : PFr s Jm X Y) {g h : Matrix (Fin n) (Fin n) R} (D D' : Matrix (Fin r) (Fin r) R)
    (hgJ : cT s g * Jm = Jm * h) :
    cT s (leviM X Y (cT s X * Jm) (cT s Y * Jm) D D' g) * Jm =
      Jm * leviM X Y (cT s X * Jm) (cT s Y * Jm) (cT s D') (cT s D) h := by
  have hp := cT_piM_mul hF
  have e3 : cT s (piM X Y (cT s X * Jm) (cT s Y * Jm) * (g * piM X Y (cT s X * Jm) (cT s Y * Jm))) * Jm =
      Jm * (piM X Y (cT s X * Jm) (cT s Y * Jm) * (h * piM X Y (cT s X * Jm) (cT s Y * Jm))) := by
    generalize piM X Y (cT s X * Jm) (cT s Y * Jm) = P at hp
    calc cT s (P * (g * P)) * Jm = cT s P * (cT s g * (cT s P * Jm)) := by
          rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]
          simp only [Matrix.mul_assoc]
      _ = cT s P * ((cT s g * Jm) * P) := by rw [hp, Matrix.mul_assoc]
      _ = (cT s P * Jm) * (h * P) := by rw [hgJ]; simp only [Matrix.mul_assoc]
      _ = Jm * (P * (h * P)) := by rw [hp, Matrix.mul_assoc]
  rw [leviM, leviM, cT_add', cT_add', Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e3]
  congr 1
  simp only [Formalism.UG.cT_mul, hF.cc, hF.herm, Matrix.mul_assoc]
  rw [add_comm]

theorem frame_levi (hF : PFr s Jm X Y) {g h : Matrix (Fin n) (Fin n) R} {B Q D Di : Matrix (Fin r) (Fin r) R}
    (hgh : g * h = 1) (hhg : h * g = 1) (hg : cT s g * Jm * g = Jm) (hh : cT s h * Jm * h = Jm)
    (hgX : g * X = X * B) (hhX : h * X = X * Q) (hD : D * Di = 1) (hDi : Di * D = 1) :
    leviM X Y (cT s X * Jm) (cT s Y * Jm) D (cT s Di) g * leviM X Y (cT s X * Jm) (cT s Y * Jm) Di (cT s D) h = 1 ∧
    leviM X Y (cT s X * Jm) (cT s Y * Jm) Di (cT s D) h * leviM X Y (cT s X * Jm) (cT s Y * Jm) D (cT s Di) g = 1 ∧
    cT s (leviM X Y (cT s X * Jm) (cT s Y * Jm) D (cT s Di) g) * Jm *
      leviM X Y (cT s X * Jm) (cT s Y * Jm) D (cT s Di) g = Jm ∧
    cT s X * Jm * h = cT s B * (cT s X * Jm) := by
  have hgJ : cT s g * Jm = Jm * h := by
    conv_rhs => rw [← hg]
    rw [Matrix.mul_assoc _ g h, hgh, Matrix.mul_one]
  have hhJ : cT s h * Jm = Jm * g := by
    conv_rhs => rw [← hh]
    rw [Matrix.mul_assoc _ h g, hhg, Matrix.mul_one]
  have hC : cT s X * Jm * h = cT s B * (cT s X * Jm) := by
    rw [Matrix.mul_assoc, ← hgJ, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hgX, Formalism.UG.cT_mul, Matrix.mul_assoc]
  have hC' : cT s X * Jm * g = cT s Q * (cT s X * Jm) := by
    rw [Matrix.mul_assoc, ← hhJ, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hhX, Formalism.UG.cT_mul, Matrix.mul_assoc]
  have hxx : cT s X * Jm * X = 0 := hF.xx
  have hxy : cT s X * Jm * Y = 1 := hF.xy
  have hyx : cT s Y * Jm * X = 1 := hF.yx
  have hyy : cT s Y * Jm * Y = 0 := hF.yy
  have c1 : cT s Di * cT s D = 1 := by rw [← Formalism.UG.cT_mul, hD, Formalism.UG.cT_one]
  have c2 : cT s D * cT s Di = 1 := by rw [← Formalism.UG.cT_mul, hDi, Formalism.UG.cT_one]
  have m1 := leviM_mul hxx hxy hyx hyy hD c1 (piM_sandwich hxx hxy hyx hyy hgh hgX hC)
  have m2 := leviM_mul hxx hxy hyx hyy hDi c2 (piM_sandwich hxx hxy hyx hyy hhg hhX hC')
  refine ⟨m1, m2, ?_, hC⟩
  rw [cT_leviM_mul hF D (cT s Di) hgJ, hF.cc, Matrix.mul_assoc, m2, Matrix.mul_one]

end Frame

theorem levi_decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E),
    IsWittFrame σ J X Y → ∀ p ∈ minParOne σ J X, ∃ u ∈ unipMin σ J X, ∃ m ∈ leviMin σ J X Y,
      m ∈ minParOne σ J X ∧ p = u * m := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW p hp
  have hF := pfrA hcm hJ hW
  obtain ⟨B, hB, e, hu⟩ := id hp
  choose v hv1 hv2 using hu
  obtain ⟨Q, -, eQ⟩ := inv_mem_minPar hcm hJ hW (minParOne_sub hp)
  have hgh : (matHom _ σ J p).1 * (matHom _ σ J p⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hhg : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hD : diagonal (fun i => (v i : AF F ⊗[F] E)) * diagonal (fun i => ((v i)⁻¹ : (AF F ⊗[F] E)ˣ).1) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  have hDi : diagonal (fun i => ((v i)⁻¹ : (AF F ⊗[F] E)ˣ).1) * diagonal (fun i => (v i : AF F ⊗[F] E)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  obtain ⟨m1, m2, m3, hC⟩ := frame_levi hF hgh hhg (unitaryA_matHom p) (unitaryA_matHom p⁻¹) e eQ hD hDi
  let m : GAd σ J := ⟨⟨_, _, m1, m2⟩, m3⟩
  have hm : (matHom _ σ J m).1 = leviM (adMat F X) (adMat F Y) (cT (sigR (AF F) σ) (adMat F X) * JR (AF F) J)
      (cT (sigR (AF F) σ) (adMat F Y) * JR (AF F) J) (diagonal (fun i => (v i : AF F ⊗[F] E)))
      (cT (sigR (AF F) σ) (diagonal (fun i => ((v i)⁻¹ : (AF F ⊗[F] E)ˣ).1))) (matHom _ σ J p).1 := rfl
  have hmi : (matHom _ σ J m⁻¹).1 = leviM (adMat F X) (adMat F Y) (cT (sigR (AF F) σ) (adMat F X) * JR (AF F) J)
      (cT (sigR (AF F) σ) (adMat F Y) * JR (AF F) J) (diagonal (fun i => ((v i)⁻¹ : (AF F ⊗[F] E)ˣ).1))
      (cT (sigR (AF F) σ) (diagonal (fun i => (v i : AF F ⊗[F] E)))) (matHom _ σ J p⁻¹).1 := rfl
  have hmX : (matHom _ σ J m).1 * adMat F X = adMat F X * diagonal (fun i => (v i : AF F ⊗[F] E)) := by
    rw [hm]
    exact leviM_mul_X _ _ hF.xx hF.yx
  have hmY : (matHom _ σ J m).1 * adMat F Y = adMat F Y * diagonal (fun i => sigR (AF F) σ (((v i)⁻¹ : (AF F ⊗[F] E)ˣ).1)) := by
    rw [hm]
    exact (leviM_mul_Y (X := adMat F X) _ _ hF.xy hF.yy).trans (congrArg (adMat F Y * ·) (cT_diagonal' _))
  have hmiX : (matHom _ σ J m⁻¹).1 * adMat F X = adMat F X * diagonal (fun i => ((v i)⁻¹ : (AF F ⊗[F] E)ˣ).1) := by
    rw [hmi]
    exact leviM_mul_X _ _ hF.xx hF.yx
  refine ⟨p * m⁻¹, ?_, m, ⟨_, _, hmX, hmY⟩, ⟨_, Matrix.blockTriangular_diagonal _, hmX, fun i =>
    ⟨v i, Matrix.diagonal_apply_eq _ _, hv2 i⟩⟩, (inv_mul_cancel_right p m).symm⟩
  have hval : (matHom _ σ J (p * m⁻¹)).1 = (matHom _ σ J p).1 * (matHom _ σ J m⁻¹).1 := by
    rw [map_mul, Units.val_mul]
  refine ⟨B * diagonal (fun i => ((v i)⁻¹ : (AF F ⊗[F] E)ˣ).1), hB.mul (Matrix.blockTriangular_diagonal _), fun i => ?_, ?_,
    fun z hz => ?_⟩
  · rw [Matrix.mul_diagonal, hv1]
    simp
  · rw [hval, Matrix.mul_assoc, hmiX, ← Matrix.mul_assoc, e, Matrix.mul_assoc]
  · have hs : (cT (sigR (AF F) σ) (adMat F X) * JR (AF F) J) *ᵥ (fun i => inclR (F := F) (AF F) (z i)) = 0 := by
      have e1 : cT (sigR (AF F) σ) (adMat F X) * JR (AF F) J = (cT (σ : E →+* E) X * J).map (inclR (F := F) (AF F)) := by
        unfold JR
        rw [← cT_map_inclR]
        exact (Matrix.map_mul (L := cT (σ : E →+* E) X) (M := J) (f := inclR (F := F) (AF F))).symm
      rw [e1]
      funext i
      have := RingHom.map_mulVec (inclR (F := F) (AF F)) (cT (σ : E →+* E) X * J) z i
      rw [hz, Pi.zero_apply, map_zero] at this
      exact this.symm
    rw [hval, hmi]
    exact exists_mulVec_eq (mul_leviM_sub_one (Ys := cT (sigR (AF F) σ) (adMat F Y) * JR (AF F) J) _ _ hF.xx hF.xy hgh e hC) hs

end GlobalTheory.CompanionTheory.LeviDecomp

end
