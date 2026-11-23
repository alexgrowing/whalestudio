import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CTFrameMatMulGram
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.LeviU

open Formalism.UG (cT)

section Abstract

variable {R : Type} [CommRing R] {a b : ℕ}

theorem eq_zero_of_mem_span_cols {L : Matrix (Fin b) (Fin a) R} {C : Matrix (Fin a) (Fin b) R} (hLC : L * C = 1)
    {I : Set (Fin b)} {w : Fin a → R} (hw : w ∈ Submodule.span R ((fun i => Cᵀ i) '' I))
    (h0 : ∀ i ∈ I, (L *ᵥ w) i = 0) : w = 0 := by
  classical
  have key : ∀ v ∈ Submodule.span R ((fun i => Cᵀ i) '' I), ∃ c : Fin b → R, (∀ i, i ∉ I → c i = 0) ∧ v = C *ᵥ c := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v h =>
      obtain ⟨i, hi, rfl⟩ := h
      refine ⟨Pi.single i 1, fun i' hi' => Pi.single_eq_of_ne (by rintro rfl; exact hi' hi) _, ?_⟩
      rw [mulVec_single_one]
      rfl
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨d, hd, rfl⟩ := hy
      exact ⟨c + d, fun i hi => by simp [hc i hi, hd i hi], by rw [mulVec_add]⟩
    | smul t x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨t • c, fun i hi => by simp [hc i hi], by rw [mulVec_smul]⟩
  obtain ⟨c, hc, rfl⟩ := key w hw
  have e : L *ᵥ (C *ᵥ c) = c := by rw [mulVec_mulVec, hLC, one_mulVec]
  rw [e] at h0
  have : c = 0 := funext fun i => by
    by_cases hi : i ∈ I
    · exact h0 i hi
    · exact hc i hi
  rw [this, mulVec_zero]

theorem mul_eq_of_conj (s : R →+* R) {G H A : Matrix (Fin a) (Fin a) R} {C : Matrix (Fin a) (Fin b) R}
    {B : Matrix (Fin b) (Fin b) R} (hHG : H * G = 1) (hU : cT s H * A * H = A) (hHC : H * C = C * B) :
    cT s C * A * G = cT s B * (cT s C * A) := by
  calc cT s C * A * G = cT s C * (cT s H * A * H) * G := by rw [hU]
    _ = cT s (H * C) * A * (H * G) := by rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT s B * (cT s C * A) := by
      rw [hHC, hHG, Formalism.UG.cT_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem mul_eq_self_of_pair (s : R →+* R) {G A : Matrix (Fin a) (Fin a) R} {C D : Matrix (Fin a) (Fin b) R}
    {B : Matrix (Fin b) (Fin b) R} (hU : cT s G * A * G = A) (hCD : cT s C * A * D = 1) (hGC : G * C = C)
    (hGD : G * D = D * B) : G * D = D := by
  have hB : B = 1 := by
    calc B = cT s C * A * D * B := by rw [hCD, Matrix.one_mul]
      _ = cT s (G * C) * A * (G * D) := by rw [hGC, hGD]; simp only [Matrix.mul_assoc]
      _ = cT s C * (cT s G * A * G) * D := by rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, hCD]
  rw [hGD, hB, Matrix.mul_one]

end Abstract

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem mat_inv_mul (g : GAd σ J) : (matHom _ σ J g⁻¹).1 * (matHom _ σ J g).1 = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem adMat_mul_eq_one {a b : ℕ} {L : Matrix (Fin a) (Fin b) E} {C : Matrix (Fin b) (Fin a) E} (h : L * C = 1) :
    adMat F L * adMat F C = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem cT_initCols_mul (C : Matrix (Fin n) (Fin r) E) (k : Fin r) :
    cT (sigR (AF F) σ) (adMat F (initCols C k)) * adMat F J =
      (adMat F (cT (σ : E →+* E) C * J)).submatrix (Fin.castLE k.2) id := by
  have c1 : cT (sigR (AF F) σ) (adMat F (initCols C k)) = adMat F (cT (σ : E →+* E) (initCols C k)) := rfl
  rw [c1, ← Matrix.map_mul]
  rfl

theorem exists_height_lower_bound (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {T : Finset (Fin r)} {κ : Fin r}
    (hκ : κ ∉ upTo T) {g : GAd σ J} (hl : g ∈ levi σ J X Y T) (hu : g ∈ unip σ J X (insert κ T)) {j : Fin r}
    (hj : j ∈ upTo T) : (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ j = (adMat F X)ᵀ j := by
  have hκj : j < κ := by
    obtain ⟨k, hk, hjk⟩ := hj
    by_contra hc
    exact hκ ⟨k, hk, (not_lt.1 hc).trans hjk⟩
  have h1 := (Subgroup.mem_iInf.1 hu.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
  have hLC : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := adMat_mul_eq_one (yx h hJ hW)
  refine sub_eq_zero.1 (eq_zero_of_mem_span_cols hLC h1 ?_)
  rintro i ⟨k, hk, hik, hkj⟩
  have hkT : k ∈ T := by
    rcases Finset.mem_insert.1 hk with rfl | hk'
    · exact absurd (hkj.trans hκj) (lt_irrefl _)
    · exact hk'
  have hl' := inv_mem hl
  simp only [levi, Subgroup.mem_iInf] at hl'
  obtain ⟨B, -, e⟩ := (Subgroup.mem_inf.1 (hl' k hkT)).2
  have h2 := mul_eq_of_conj (A := adMat F J) (sigR (AF F) σ) (mat_inv_mul g) (g⁻¹).2 e
  rw [cT_initCols_mul] at h2
  set L := (adMat F (cT (σ : E →+* E) Y * J)).submatrix (Fin.castLE k.2) id with hL
  have h3 : L *ᵥ (adMat F X)ᵀ j = 0 := by
    funext p
    have hp : Fin.castLE k.2 p ≠ j := fun hc => by
      have h4 : (Fin.castLE k.2 p).val ≤ k.val := Nat.le_of_lt_succ p.2
      have h5 : k.val < j.val := hkj
      rw [hc] at h4
      omega
    exact (congrFun (congrFun hLC (Fin.castLE k.2 p)) j).trans (Matrix.one_apply_ne hp)
  have h4 : L *ᵥ ((matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ j - (adMat F X)ᵀ j) = 0 := by
    rw [mulVec_sub, mulVec_mulVec, h2, ← mulVec_mulVec, h3, mulVec_zero, sub_zero]
  exact congrFun h4 ⟨i.val, Nat.lt_succ_of_le hik⟩

theorem fix_y (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {T : Finset (Fin r)} {κ : Fin r}
    (hκ : κ ∉ upTo T) {g : GAd σ J} (hl : g ∈ levi σ J X Y T) (hu : g ∈ unip σ J X (insert κ T)) {i : Fin r}
    (hi : i ∈ upTo T) : (matHom _ σ J g).1 *ᵥ (adMat F Y)ᵀ i = (adMat F Y)ᵀ i := by
  obtain ⟨k, hkT, hik⟩ := hi
  simp only [levi, Subgroup.mem_iInf] at hl
  obtain ⟨B, -, e⟩ := (Subgroup.mem_inf.1 (hl k hkT)).2
  have hGC : (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) :=
    Matrix.ext_col fun p => exists_height_lower_bound h hJ hW hκ (by simpa only [levi, Subgroup.mem_iInf] using hl) hu
      ⟨k, hkT, Nat.le_of_lt_succ p.2⟩
  have hCD : cT (sigR (AF F) σ) (adMat F (initCols X k)) * adMat F J * adMat F (initCols Y k) = 1 := by
    rw [cT_initCols_mul]
    have h1 : adMat F (cT (σ : E →+* E) X * J) * adMat F Y = 1 := adMat_mul_eq_one hW.xy
    exact Matrix.ext fun p q => (congrFun (congrFun h1 (Fin.castLE k.2 p)) (Fin.castLE k.2 q)).trans (by simp [Matrix.one_apply])
  have h2 := mul_eq_self_of_pair (A := adMat F J) (sigR (AF F) σ) g.2 hCD hGC e
  exact congrArg (fun M => Mᵀ ⟨i.val, Nat.lt_succ_of_le hik⟩) h2

theorem levi_inf_unip_le_uPart_general (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    (T : Finset (Fin r)) {κ : Fin r} (hκ : κ ∉ upTo T) :
    levi σ J X Y T ⊓ unip σ J X (insert κ T) ≤ uPart σ J X Y T := by
  rintro g ⟨hl, hu⟩
  have key : colSpan F X (upTo T) ⊔ colSpan F Y (upTo T) ≤ LinearMap.eqLocus (matHom _ σ J g).1.mulVecLin LinearMap.id := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨j, hj, rfl⟩
      exact exists_height_lower_bound h hJ hW hκ hl hu hj
    · rintro _ ⟨j, hj, rfl⟩
      exact fix_y h hJ hW hκ hl hu hj
  exact fun y hy => key hy

end Frame

theorem levi_inf_unip_le_uPart : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (κ : Fin m), κ ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → levi D.sp.cm.sig V.gram X Y T ⊓ unip D.sp.cm.sig V.gram X (insert κ T) ≤ uPart D.sp.cm.sig V.gram X Y T := by
  intro D V m X Y hW T κ hκ
  obtain ⟨h, hJ'⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  exact levi_inf_unip_le_uPart_general h (hJ' V) hW T hκ

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.LeviU
end
