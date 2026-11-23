import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianPartLeLevi
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb

open Formalism.L2.Fam.ThC (colM colM_vec frameMat_eq frame_rel perp_rel prM coM embU)
open GlobalTheory.CompanionTheory.LeviGen (prj prX prY ind)
open Formalism.UG (cT)

section Abstract

variable {R : Type} [CommRing R] {a b : ℕ}

theorem lift_of_fix (s : R →+* R) {M : Matrix (Fin a) (Fin b) R} {P : Matrix (Fin b) (Fin a) R}
    {Q G H J : Matrix (Fin a) (Fin a) R} {K : Matrix (Fin b) (Fin b) R}
    (hMP : M * P + Q = 1) (hPM : P * M = 1) (hGQ : G * Q = Q) (hQG : Q * G = Q) (hGH : G * H = 1) (hHG : H * G = 1)
    (hU : cT s G * J * G = J) (hK : cT s M * J * M = K) :
    (P * G * M) * (P * H * M) = 1 ∧ (P * H * M) * (P * G * M) = 1 ∧ M * (P * G * M) = G * M ∧
      cT s (P * G * M) * K * (P * G * M) = K := by
  have eMP : M * P = 1 - Q := eq_sub_of_add_eq hMP
  have hQM : Q * M = 0 := by
    have : (M * P + Q) * M = M := by rw [hMP, Matrix.one_mul]
    rw [Matrix.add_mul, Matrix.mul_assoc, hPM, Matrix.mul_one] at this
    exact left_eq_add.1 this.symm
  have hQH : Q * H = Q := by rw [← hQG, Matrix.mul_assoc, hGH, Matrix.mul_one, hQG]
  have hHQ : H * Q = Q := by rw [← hGQ, ← Matrix.mul_assoc, hHG, Matrix.one_mul, hGQ]
  have hmid : ∀ {A B : Matrix (Fin a) (Fin a) R}, A * B = 1 → Q * B = Q → A * Q = Q →
      (P * A * M) * (P * B * M) = 1 := by
    intro A B hAB hQB hAQ
    calc (P * A * M) * (P * B * M) = P * A * (M * P) * B * M := by simp only [Matrix.mul_assoc]
      _ = P * (A * B) * M - P * (A * Q) * B * M := by
        rw [eMP]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by
        rw [hAB, hAQ, Matrix.mul_one, hPM, Matrix.mul_assoc P Q B, hQB, Matrix.mul_assoc P Q M, hQM, Matrix.mul_zero,
          sub_zero]
  have hMG : M * (P * G * M) = G * M := by
    calc M * (P * G * M) = (M * P) * G * M := by simp only [Matrix.mul_assoc]
      _ = G * M := by
        rw [eMP, Matrix.sub_mul, Matrix.sub_mul, hQG, hQM, Matrix.one_mul, sub_zero]
  refine ⟨hmid hGH hQH hGQ, hmid hHG hQG hHQ, hMG, ?_⟩
  calc cT s (P * G * M) * K * (P * G * M)
      = cT s (M * (P * G * M)) * J * (M * (P * G * M)) := by
        rw [show cT s (M * (P * G * M)) = cT s (P * G * M) * cT s M by rw [Formalism.UG.cT_mul], ← hK]
        simp only [Matrix.mul_assoc]
    _ = cT s M * (cT s G * J * G) * M := by
        rw [hMG, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = K := by rw [hU, hK]

end Abstract

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem mul_P {b : Type} [Fintype b] (N : Matrix b (Fin n) E) (I : Set (Fin r)) :
    N * USplit.P σ J X Y I = (N * X * diagonal (ind I : Fin r → E)) * cT (σ : E →+* E) Y * J +
      (N * Y * diagonal (ind I : Fin r → E)) * cT (σ : E →+* E) X * J := by
  simp only [USplit.P, prj, prX, prY, Matrix.mul_add, Matrix.mul_assoc]

theorem cTX_mul_P (hW : IsWittFrame σ J X Y) (I : Set (Fin r)) :
    cT (σ : E →+* E) X * J * USplit.P σ J X Y I = diagonal (ind I : Fin r → E) * (cT (σ : E →+* E) X * J) := by
  rw [mul_P, hW.xx, hW.xy]
  simp [Matrix.mul_assoc]

theorem cTY_mul_P (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (I : Set (Fin r)) :
    cT (σ : E →+* E) Y * J * USplit.P σ J X Y I = diagonal (ind I : Fin r → E) * (cT (σ : E →+* E) Y * J) := by
  rw [mul_P, hW.yy, Comm.yJx hCM hJ hW]
  simp [Matrix.mul_assoc]

end Frame

section Space

variable {D : D7}

theorem repr_symm (V : HSp D) (c : Fin V.rank → D.host.E) : ⇑(V.frame.repr (V.frame.equivFun.symm c)) = c :=
  funext fun a => congrFun (V.frame.equivFun.apply_symm_apply c) a

theorem hT_col (V : HSp D) {m : ℕ} (C : Matrix (Fin V.rank) (Fin m) D.host.E) (c : Fin V.rank → D.host.E) (i : Fin m) :
    V.hT (V.frame.equivFun.symm fun j => C j i) (V.frame.equivFun.symm c) =
      ((cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram) *ᵥ c) i := by
  have h := colM_vec V (fun i => V.frame.equivFun.symm fun j => C j i) (V.frame.equivFun.symm c) i
  have e : colM V (fun i => V.frame.equivFun.symm fun j => C j i) = C :=
    Matrix.ext fun a b => congrFun (repr_symm V fun j => C j b) a
  rw [e, repr_symm] at h
  exact h.symm

theorem mulVec_perp {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V} {c : Fin V.rank → D.host.E}
    (h : ∀ v ∈ LinearMap.range ι, V.hT (V.frame.equivFun.symm c) v = 0) :
    (cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram) *ᵥ c = 0 := by
  funext a
  have e := colM_vec V (fun k => ι (V'.frame k)) (V.frame.equivFun.symm c) a
  rw [repr_symm] at e
  rw [frameMat_eq, e, ← V.herm.eq, h _ ⟨_, rfl⟩]
  simp

end Space

section Main

variable {D : D7} {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V} {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E}
  {T : Finset (Fin m)}

theorem mul_diag_zero {b : Type} [Fintype b] {N : Matrix b (Fin m) D.host.E} {I : Set (Fin m)}
    (h : ∀ a, ∀ i ∈ I, N a i = 0) : N * diagonal (ind I : Fin m → D.host.E) = 0 := by
  classical
  refine Matrix.ext fun a i => ?_
  rw [Matrix.mul_diagonal, GlobalTheory.CompanionTheory.LeviGen.ind_apply]
  by_cases hi : i ∈ I
  · rw [h a i hi, zero_mul]; rfl
  · rw [if_neg hi, mul_zero]; rfl

theorem frame_proj (hCM : IsCMExt D.host.F D.host.E D.sp.cm.sig) (hJ : IsHermND D.sp.cm.sig V.gram)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (hι : HSpace.IsIsomEmb V' V ι)
    (hr : ∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧
      V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) :
    frameMat V V' ι * prM V V' ι = 1 - USplit.P D.sp.cm.sig V.gram X Y (upTo T) := by
  classical
  set M := frameMat V V' ι with hM
  set Pr := prM V V' ι with hPr
  set Q := USplit.P D.sp.cm.sig V.gram X Y (upTo T) with hQ
  have hPM : Pr * M = 1 := by
    rw [hPr, prM, Matrix.mul_assoc, frame_rel hι, Matrix.nonsing_inv_mul _ (gram_det_ne V').isUnit]
  have hX : ∀ a, ∀ i ∈ upTo T, (cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * X) a i = 0 := fun a i hi =>
    congrFun (mulVec_perp (ι := ι) (c := fun j => X j i) fun v hv => ((hr v).1 hv i hi).1) a
  have hY : ∀ a, ∀ i ∈ upTo T, (cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * Y) a i = 0 := fun a i hi =>
    congrFun (mulVec_perp (ι := ι) (c := fun j => Y j i) fun v hv => ((hr v).1 hv i hi).2) a
  have hMQ : cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * Q = 0 := by
    rw [hQ, mul_P, mul_diag_zero hX, mul_diag_zero hY]
    simp
  have hcol : ∀ j, ∃ u, ι u = V.frame.equivFun.symm fun a => (1 - Q) a j := fun j => by
    refine (hr _).2 fun i hi => ?_
    rw [hT_col, hT_col]
    have hi' : (ind (upTo T) : Fin m → D.host.E) i = 1 := by rw [GlobalTheory.CompanionTheory.LeviGen.ind_apply, if_pos hi]
    constructor
    · have e : cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram * (1 - Q) =
          (1 - diagonal (ind (upTo T) : Fin m → D.host.E)) * (cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) := by
        rw [Matrix.mul_sub, Matrix.mul_one, hQ, cTX_mul_P hW, Matrix.sub_mul, Matrix.one_mul]
      have e' := congrFun (congrFun e i) j
      refine e'.trans ?_
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.diagonal_mul, hi', one_mul, sub_self]
    · have e : cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram * (1 - Q) =
          (1 - diagonal (ind (upTo T) : Fin m → D.host.E)) * (cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) := by
        rw [Matrix.mul_sub, Matrix.mul_one, hQ, cTY_mul_P hCM hJ hW, Matrix.sub_mul, Matrix.one_mul]
      have e' := congrFun (congrFun e i) j
      refine e'.trans ?_
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.diagonal_mul, hi', one_mul, sub_self]
  choose u hu using hcol
  have hA : M * Matrix.of (fun b j => V'.frame.repr (u j) b) = 1 - Q := by
    refine Matrix.ext fun a j => ?_
    have e := congrFun (LinearMap.toMatrix_mulVec_repr V'.frame V.frame ι (u j)) a
    rw [hu j, repr_symm] at e
    exact e
  have e1 : M * Pr * (1 - Q) = 1 - Q := by
    rw [← hA, Matrix.mul_assoc M Pr, ← Matrix.mul_assoc Pr, hPM, Matrix.one_mul]
  have e2 : M * Pr * Q = 0 := by
    rw [hPr, prM, Matrix.mul_assoc, Matrix.mul_assoc, hMQ]
    simp
  calc M * Pr = M * Pr * (1 - Q) + M * Pr * Q := by rw [← Matrix.mul_add, sub_add_cancel, Matrix.mul_one]
    _ = 1 - Q := by rw [e1, e2, add_zero]

end Main

section Final

theorem range_embHom : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D)
    (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι →
    (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T,
      V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) →
    ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) →
    (∀ h, s h ∈ uPart D.sp.cm.sig V.gram X Y T) ∧ (∀ g ∈ uPart D.sp.cm.sig V.gram X Y T, ∃ h, s h = g) ∧
      ∀ h ∈ GfC V', s h ∈ GfC V := by
  intro D V m X Y hW T V' ι hι hr s hs
  obtain ⟨hCM, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  refine ⟨fun h => ?_, fun g hg => ?_, fun h hh => Formalism.L2.Fam.ThC.emb_fin hι hs hh⟩
  · intro y hy
    let S : Submodule (AF D.host.F ⊗[D.host.F] D.host.E) (Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E) :=
      LinearMap.eqLocus (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram (s h)).1.mulVecLin LinearMap.id
    have hle : colSpan D.host.F X (upTo T) ⊔ colSpan D.host.F Y (upTo T) ≤ S := by
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨i, hi, rfl⟩
        exact (hs h).2 (fun j => X j i) (mulVec_perp fun v hv => ((hr v).1 hv i hi).1)
      · rintro _ ⟨i, hi, rfl⟩
        exact (hs h).2 (fun j => Y j i) (mulVec_perp fun v hv => ((hr v).1 hv i hi).2)
    exact hle hy
  · have hF := frame_proj hCM (hJ V) hW hι hr
    set Q := USplit.P D.sp.cm.sig V.gram X Y (upTo T) with hQ
    have hF' : frameMat V V' ι * prM V V' ι + Q = 1 := by rw [hF, sub_add_cancel]
    have hPM' : prM V V' ι * frameMat V V' ι = 1 := by
      rw [prM, Matrix.mul_assoc, frame_rel hι, Matrix.nonsing_inv_mul _ (gram_det_ne V').isUnit]
    have hMP : (frameMat V V' ι).map (incA D) * (prM V V' ι).map (incA D) + adMat D.host.F Q = 1 := by
      rw [← Matrix.map_mul]
      show (frameMat V V' ι * prM V V' ι).map (incA D) + Q.map (incA D) = 1
      rw [← Matrix.map_add _ (map_add (incA D)), hF', Matrix.map_one _ (map_zero _) (map_one _)]
    have hPM : (prM V V' ι).map (incA D) * (frameMat V V' ι).map (incA D) = 1 := by
      rw [← Matrix.map_mul, hPM', Matrix.map_one _ (map_zero _) (map_one _)]
    have hGQ := USplit.Q_fix_of_uPart hCM (hJ V) hW hg
    have hJu : IsUnit (JR (F := D.host.F) (AF D.host.F) V.gram).det := by
      rw [show JR (F := D.host.F) (AF D.host.F) V.gram = V.gram.map (incA D) from rfl,
        show (V.gram.map (incA D)).det = incA D V.gram.det from (RingHom.map_det (incA D) V.gram).symm]
      exact (isUnit_iff_ne_zero.2 (hJ V).2).map (incA D)
    have hQG := Comm.mul_eq_of_unitary hJu (USplit.matHom_unitary g) (USplit.adMat_P_selfAdjoint hCM (hJ V) _) hGQ
    have hK : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((frameMat V V' ι).map (incA D)) *
        JR (F := D.host.F) (AF D.host.F) V.gram * (frameMat V V' ι).map (incA D) =
        JR (F := D.host.F) (AF D.host.F) V'.gram := by
      rw [Comm.cT_map]
      have e := congrArg (fun A => Matrix.map A (incA D)) (frame_rel hι)
      simp only [Matrix.map_mul] at e
      exact e
    obtain ⟨h1, h2, h3, h4⟩ := lift_of_fix (sigR (AF D.host.F) D.sp.cm.sig) hMP hPM hGQ hQG
      (USplit.matHom_mul_inv g) (USplit.matHom_inv_mul g) (USplit.matHom_unitary g) hK
    let h : GA D V' := show HR (AF D.host.F) D.sp.cm.sig V'.gram from ⟨⟨_, _, h1, h2⟩, h4⟩
    refine ⟨h, embU D V V' ι hι _ _ h (hs h) ⟨h3.symm, fun x hx => ?_⟩⟩
    have hPx : prM V V' ι *ᵥ x = 0 := by rw [prM, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    have hQx : Q *ᵥ x = x := by
      have e : (frameMat V V' ι * prM V V' ι + Q) *ᵥ x = x := by rw [hF', Matrix.one_mulVec]
      rwa [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hPx, Matrix.mulVec_zero, zero_add] at e
    have hb : adMat D.host.F Q *ᵥ (fun i => incA D (x i)) = fun i => incA D (x i) := by
      funext i
      exact ((incA D).map_mulVec Q x i).symm.trans (congrArg _ (congrFun hQx i))
    show (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram g).1 *ᵥ (fun i => incA D (x i)) = _
    rw [← hb, Matrix.mulVec_mulVec, hGQ]

end Final

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb
end
