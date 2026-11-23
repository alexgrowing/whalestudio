import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LeviScale

section Alg

variable {E : Type} [Field E] [CharZero E] (σ : E →+* E)

theorem cT_fromCols {ι α β : Type} (X : Matrix ι α E) (Y : Matrix ι β E) :
    Formalism.UG.cT σ (fromCols X Y) = fromRows (Formalism.UG.cT σ X) (Formalism.UG.cT σ Y) := by
  ext (i | i) j <;> rfl

theorem cT_diagonal {ι : Type} [DecidableEq ι] (d : ι → E) (hd : ∀ i, σ (d i) = d i) :
    Formalism.UG.cT σ (diagonal d) = diagonal d := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Formalism.UG.cT, hd]
  · simp [Formalism.UG.cT, diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]

theorem levi_alg (hσ : ∀ x, σ (σ x) = x) {n m r : ℕ} (hn : n = m + 2 * r)
    (G : Matrix (Fin n) (Fin n) E) (G' Gi : Matrix (Fin m) (Fin m) E) (hGi : Gi * G' = 1)
    (hG : Formalism.UG.cT σ G = G)
    (C C' : Matrix (Fin n) (Fin r) E) (B : Matrix (Fin n) (Fin m) E)
    (h11 : Formalism.UG.cT σ C * G * C = 0) (h12 : Formalism.UG.cT σ C * G * B = 0)
    (h22 : Formalism.UG.cT σ B * G * B = G')
    (h13 : Formalism.UG.cT σ C * G * C' = 1) (h33 : Formalism.UG.cT σ C' * G * C' = 0)
    (h32 : Formalism.UG.cT σ C' * G * B = 0) :
    ∃ A A' : Matrix (Fin n) (Fin n) E, A * A' = 1 ∧ A' * A = 1 ∧ Formalism.UG.cT σ A * G * A = G ∧
      A * C = (2 : E) • C ∧ A * B = B ∧ (2 : E) • (A * C') = C' := by
  have hcc : ∀ {a : ℕ} (X : Matrix (Fin n) (Fin a) E), Formalism.UG.cT σ (Formalism.UG.cT σ X) = X := by
    intro a X; ext i j; simp [Formalism.UG.cT, hσ]
  have swap : ∀ {a b : ℕ} (X : Matrix (Fin n) (Fin a) E) (Y : Matrix (Fin n) (Fin b) E),
      Formalism.UG.cT σ (Formalism.UG.cT σ X * G * Y) = Formalism.UG.cT σ Y * G * X := by
    intro a b X Y
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hG, hcc, Matrix.mul_assoc]
  have cT0 : ∀ {a b : ℕ}, Formalism.UG.cT σ (0 : Matrix (Fin a) (Fin b) E) = 0 := by
    intro a b; ext i j; simp [Formalism.UG.cT]
  have h21 : Formalism.UG.cT σ B * G * C = 0 := by rw [← swap C B, h12, cT0]
  have h23 : Formalism.UG.cT σ B * G * C' = 0 := by rw [← swap C' B, h32, cT0]
  have h31 : Formalism.UG.cT σ C' * G * C = 1 := by rw [← swap C C', h13, Formalism.UG.cT_one]
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin r ⊕ (Fin m ⊕ Fin r)) E, P = fromCols C (fromCols B C') := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin r ⊕ (Fin m ⊕ Fin r)) (Fin n) E,
      Q = fromRows (Formalism.UG.cT σ C' * G) (fromRows (Gi * Formalism.UG.cT σ B * G) (Formalism.UG.cT σ C * G)) := ⟨_, rfl⟩
  have as3 : ∀ {a : ℕ} (X : Matrix (Fin n) (Fin a) E), Gi * Formalism.UG.cT σ B * G * X = Gi * (Formalism.UG.cT σ B * G * X) := by
    intro a X; simp only [Matrix.mul_assoc]
  have hQC : Q * C = fromRows 1 (fromRows 0 0) := by
    rw [hQ, fromRows_mul, fromRows_mul, h31, h11, as3, h21, Matrix.mul_zero]
  have hQB : Q * B = fromRows 0 (fromRows 1 0) := by
    rw [hQ, fromRows_mul, fromRows_mul, h32, h12, as3, h22, hGi]
  have hQC' : Q * C' = fromRows 0 (fromRows 0 1) := by
    rw [hQ, fromRows_mul, fromRows_mul, h33, h13, as3, h23, Matrix.mul_zero]
  have hQP : Q * P = 1 := by
    rw [hP, mul_fromCols, mul_fromCols, hQC, hQB, hQC']
    ext (i | i | i) (j | j | j) <;> simp [one_apply]
  have hPQ : P * Q = 1 := by
    have e : (Fin r ⊕ (Fin m ⊕ Fin r)) ≃ Fin n := Fintype.equivOfCardEq (by simp; omega)
    exact (Matrix.mul_eq_one_comm_of_equiv e).1 hQP
  obtain ⟨d, hd⟩ : ∃ d : Fin r ⊕ (Fin m ⊕ Fin r) → E,
      d = Sum.elim (fun _ => 2) (Sum.elim (fun _ => 1) (fun _ => 2⁻¹)) := ⟨_, rfl⟩
  obtain ⟨d', hd'⟩ : ∃ d' : Fin r ⊕ (Fin m ⊕ Fin r) → E,
      d' = Sum.elim (fun _ => 2⁻¹) (Sum.elim (fun _ => 1) (fun _ => 2)) := ⟨_, rfl⟩
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have hdd : (fun i => d i * d' i) = fun _ => 1 := by
    funext i; rcases i with i | i | i <;> simp [hd, hd', h2]
  have hdd' : (fun i => d' i * d i) = fun _ => 1 := by
    funext i; rcases i with i | i | i <;> simp [hd, hd', h2]
  have hσd : ∀ i, σ (d i) = d i := by
    intro i; rcases i with i | i | i <;> simp [hd, map_inv₀, map_ofNat]
  have hK : Formalism.UG.cT σ P * G * P = fromCols (fromRows 0 (fromRows 0 1))
      (fromCols (fromRows 0 (fromRows G' 0)) (fromRows 1 (fromRows 0 0))) := by
    rw [hP, cT_fromCols, cT_fromCols]
    simp only [fromRows_mul, mul_fromCols]
    rw [h11, h12, h13, h21, h22, h23, h31, h32, h33]
  have hDKD : diagonal d * (Formalism.UG.cT σ P * G * P) * diagonal d = Formalism.UG.cT σ P * G * P := by
    rw [hK]
    ext (i | i | i) (j | j | j) <;> simp [diagonal_mul, mul_diagonal, hd] <;> ring
  refine ⟨P * diagonal d * Q, P * diagonal d' * Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc P * diagonal d * Q * (P * diagonal d' * Q) = P * (diagonal d * (Q * P) * diagonal d') * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, diagonal_mul_diagonal, hdd, diagonal_one, Matrix.mul_one, hPQ]
  · calc P * diagonal d' * Q * (P * diagonal d * Q) = P * (diagonal d' * (Q * P) * diagonal d) * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, diagonal_mul_diagonal, hdd', diagonal_one, Matrix.mul_one, hPQ]
  · have hA : Formalism.UG.cT σ (P * diagonal d * Q) = Formalism.UG.cT σ Q * diagonal d * Formalism.UG.cT σ P := by
      rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_diagonal σ d hσd, Matrix.mul_assoc]
    calc Formalism.UG.cT σ (P * diagonal d * Q) * G * (P * diagonal d * Q)
        = Formalism.UG.cT σ Q * (diagonal d * (Formalism.UG.cT σ P * G * P) * diagonal d) * Q := by
          rw [hA]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σ (P * Q) * G * (P * Q) := by
          rw [hDKD, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  · have h : diagonal d * (Q * C) = (2 : E) • (Q * C) := by
      rw [hQC]; ext (i | i | i) j <;> simp [diagonal_mul, hd]
    calc P * diagonal d * Q * C = P * (diagonal d * (Q * C)) := by simp only [Matrix.mul_assoc]
      _ = (2 : E) • (P * Q * C) := by rw [h, Matrix.mul_smul, Matrix.mul_assoc]
      _ = (2 : E) • C := by rw [hPQ, Matrix.one_mul]
  · have h : diagonal d * (Q * B) = Q * B := by
      rw [hQB]; ext (i | i | i) j <;> simp [diagonal_mul, hd]
    calc P * diagonal d * Q * B = P * (diagonal d * (Q * B)) := by simp only [Matrix.mul_assoc]
      _ = P * Q * B := by rw [h, Matrix.mul_assoc]
      _ = B := by rw [hPQ, Matrix.one_mul]
  · have h : diagonal d * (Q * C') = (2 : E)⁻¹ • (Q * C') := by
      rw [hQC']; ext (i | i | i) j <;> simp [diagonal_mul, hd]
    calc (2 : E) • (P * diagonal d * Q * C') = (2 : E) • (P * (diagonal d * (Q * C'))) := by
          simp only [Matrix.mul_assoc]
      _ = ((2 : E) * (2 : E)⁻¹) • (P * Q * C') := by rw [h, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = C' := by rw [hPQ, Matrix.one_mul, mul_inv_cancel₀ h2, one_smul]

end Alg

theorem exists_levi_scale : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∃ a : GA D V, a ∈ GQ V ∧ HMul.hMul (matHom V a).1 (C.map (incA D)) = (2 : AE D) • C.map (incA D) ∧ HMul.hMul (matHom V a).1 (B.map (incA D)) = B.map (incA D) ∧ (2 : AE D) • HMul.hMul (matHom V a).1 (C'.map (incA D)) = C'.map (incA D) := by
  intro D V V' r C C' B hs h1 h2 h3
  obtain ⟨A, A', hAA', hA'A, hU, hC, hB, hC'⟩ :=
    levi_alg (D.sp.cm.sig : D.host.E →+* D.host.E) (fun x => star_star x) hs.rank V.gram V'.gram V'.gram⁻¹
      (Matrix.nonsing_inv_mul _ (GlobalTheory.AutFunCounterexample.gram_det_ne V').isUnit) (GlobalTheory.AutFunCounterexample.gram_herm V)
      C C' B hs.frame.2.2 hs.orth hs.isom h1 h2 h3
  let g : GL (Fin V.rank) D.host.E := ⟨A, A', hAA', hA'A⟩
  have hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := hU
  have hmem : Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (A.map (incA D)) * V.gram.map (incA D) * A.map (incA D) =
      V.gram.map (incA D)
    rw [GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul, hU]
  have hsm : ∀ {k : ℕ} (X : Matrix (Fin V.rank) (Fin k) D.host.E),
      ((2 : D.host.E) • X).map (incA D) = (2 : AE D) • X.map (incA D) := by
    intro k X; ext i j; simp [Matrix.map_apply, Matrix.smul_apply, map_ofNat]
  refine ⟨⟨Formalism.UG.bc (incA D) g, hmem⟩, ?_, ?_, ?_, ?_⟩
  · show (⟨Formalism.UG.bc (incA D) g, hmem⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram) ∈
      (HFin (AF D.host.F) D.sp.cm.sig V.gram).subgroupOf (HR (AF D.host.F) D.sp.cm.sig V.gram)
    rw [Subgroup.mem_subgroupOf]
    exact ⟨g, hg, rfl⟩
  · change HMul.hMul (A.map (incA D)) (C.map (incA D)) = _
    rw [← Matrix.map_mul, hC, hsm]
  · change HMul.hMul (A.map (incA D)) (B.map (incA D)) = _
    rw [← Matrix.map_mul, hB]
  · change (2 : AE D) • HMul.hMul (A.map (incA D)) (C'.map (incA D)) = _
    rw [← Matrix.map_mul, ← hsm, hC']

end GlobalTheory.LeviScale
