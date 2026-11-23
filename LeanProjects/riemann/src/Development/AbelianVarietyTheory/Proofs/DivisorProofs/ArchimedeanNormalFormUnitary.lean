import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.ThKUTrUnit

open Matrix

theorem conj_frame_unitary {n : ℕ} (A Jd X Q Qi : Matrix (Fin n) (Fin n) ℂ) (hQ : Q * Qi = 1)
    (h : Qᴴ * A * Q = Jd) (hX : Xᴴ * Jd * X = Jd) :
    (Q * X * Qi)ᴴ * A * (Q * X * Qi) = A := by
  have e1 : (Q * X * Qi)ᴴ * A * (Q * X * Qi) = Qiᴴ * (Xᴴ * (Qᴴ * A * Q) * X) * Qi := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e1, h, hX, ← h]
  have e2 : Qiᴴ * (Qᴴ * A * Q) * Qi = (Q * Qi)ᴴ * A * (Q * Qi) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e2, hQ]
  simp

theorem transpose_form_of_conj {n : ℕ} (K g : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0)
    (h : gᴴ * (c • K.map star) * g = c • K.map star) :
    gᵀ * K * g.map star = K := by
  rw [Matrix.mul_smul, Matrix.smul_mul] at h
  have h' : gᴴ * K.map star * g = K.map star := smul_right_injective _ hc h
  have h2 := congrArg (fun M => M.map (starRingEnd ℂ)) h'
  simp only [Matrix.map_mul] at h2
  have e1 : (gᴴ).map (starRingEnd ℂ) = gᵀ := by ext i j; simp
  have e2 : (K.map star).map (starRingEnd ℂ) = K := by ext i j; simp
  have e3 : g.map (starRingEnd ℂ) = g.map star := by ext i j; simp
  rw [e1, e2, e3] at h2
  exact h2

theorem mat_ext_of_coord {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {R : Type} [CommRing R]
    (Φ : AE F E ≃+* (InfinitePlace F → ℂ) × R) {n : ℕ} (M N : Matrix (Fin n) (Fin n) (AE F E))
    (hre : ∀ w, M.map (fun z => (Φ z).1 w) = N.map (fun z => (Φ z).1 w))
    (hfi : M.map (fun z => (Φ z).2) = N.map (fun z => (Φ z).2)) : M = N := by
  ext i j
  apply Φ.injective
  refine Prod.ext ?_ ?_
  · funext w
    exact congrFun (congrFun (hre w) i) j
  · exact congrFun (congrFun hfi i) j

theorem sigR_invol {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (R : Type) [CommRing R] [Algebra F R] (z : E ⊗[F] R) : Formalism.UG.sigR σ R (Formalism.UG.sigR σ R z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Formalism.UG.sigR, hσ]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem sigR_inclE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Formalism.UG.sigR σ R (Formalism.UG.inclE (F := F) R e) = Formalism.UG.inclE (F := F) R (σ e) := by
  simp [Formalism.UG.sigR, Formalism.UG.inclE]

theorem rawT_mem_UG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (δ : E) (Φ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E ≃+* (InfinitePlace F → ℂ) × (E ⊗[F] Formalism.MainNotions.S.Af F)) (ε : InfinitePlace F → Fin n → Bool) (P : InfinitePlace F → (Matrix (Fin n) (Fin n) ℂ)ˣ), IsCMExt F E σ → σ δ = -δ → δ ≠ 0 → (∀ i j, σ (J j i) = -J i j) → (∀ x : E, Φ (inclR (F := F) (AF F) x) = (fun w => (B.emb w).1 x, Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) x)) → (∀ z, Φ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = (fun w => star ((Φ z).1 w), Formalism.UG.sigR σ (Formalism.MainNotions.S.Af F) (Φ z).2)) → (∀ w, ((P w : Matrix (Fin n) (Fin n) ℂ))ᴴ * (δ • J.map σ).map (B.emb w).1 * (P w : Matrix (Fin n) (Fin n) ℂ) = Formalism.REAL.Jm (ε w)) → ∀ x, GlobalTheory.ThKUTr.rawT Φ ε P (Formalism.UG.UPts σ (δ • J.map σ) (Formalism.MainNotions.S.Af F)) x ∈ UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) := by
  intro F E _ _ _ _ _ σ B n J δ Φ ε P hcm hδ hδ0 _ hinc hcA hP x
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  set g : Matrix (Fin n) (Fin n) (AE F E) :=
    ((GlobalTheory.ThKUTr.rawT Φ ε P (Formalism.UG.UPts σ (δ • J.map σ) (Formalism.MainNotions.S.Af F)) x : GL (Fin n) (AE F E)) :
      Matrix (Fin n) (Fin n) (AE F E)) with hg
  show gᵀ * incM F J * g.map (cA σ) = incM F J
  apply mat_ext_of_coord Φ
  · intro w
    let fw : AE F E →+* ℂ := (Pi.evalRingHom (fun _ : InfinitePlace F => ℂ) w).comp ((RingHom.fst _ _).comp Φ.toRingHom)
    change (gᵀ * incM F J * g.map (cA σ)).map fw = (incM F J).map fw
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    have gw : g.map fw = (P w : Matrix (Fin n) (Fin n) ℂ) * Formalism.MainNotions.S.uMat (x.1 w) *
        ((P w)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
      ext i j
      simp [fw, hg, GlobalTheory.ThKUTr.rawT_val, GlobalTheory.ThKUTr.glueM_apply]
    have Jw : (incM F J).map fw = J.map (B.emb w).1 := by
      ext i j
      simp [fw, incM, hinc]
    have cw : (g.map (cA σ)).map fw = (g.map fw).map star := by
      ext i j
      simp [fw, hcA]
    rw [cw, gw, Jw]
    have hA : (δ • J.map σ).map (B.emb w).1 = ((B.emb w).1 δ) • (J.map (B.emb w).1).map star := by
      ext i j
      simp [hcm.2.2.2]
    have hc : (B.emb w).1 δ ≠ 0 := by
      intro h0
      exact hδ0 ((B.emb w).1.injective (by rw [h0, map_zero]))
    apply transpose_form_of_conj _ _ _ hc
    rw [← hA]
    exact conj_frame_unitary _ _ _ _ _ (P w).mul_inv (hP w) (x.1 w).2
  · let ff : AE F E →+* E ⊗[F] Formalism.MainNotions.S.Af F := (RingHom.snd _ _).comp Φ.toRingHom
    change (gᵀ * incM F J * g.map (cA σ)).map ff = (incM F J).map ff
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    set s := Formalism.UG.sigR σ (Formalism.MainNotions.S.Af F) with hs
    set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F) :=
      ((x.2 : GL (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) with hY
    have gf : g.map ff = Y := by
      ext i j
      simp [ff, hg, hY, GlobalTheory.ThKUTr.rawT_val, GlobalTheory.ThKUTr.glueM_apply]
    have Jf : (incM F J).map ff = J.map (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F)) := by
      ext i j
      simp [ff, incM, hinc]
    have cf : (g.map (cA σ)).map ff = (g.map ff).map s := by
      ext i j
      simp [ff, hcA, hs]
    rw [cf, gf, Jf]
    set D := (δ • J.map σ).map (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F)) with hD
    have hy : Formalism.UG.cT s Y * D * Y = D := x.2.2
    have hy2 := congrArg (fun M => M.map s) hy
    simp only [Matrix.map_mul] at hy2
    have e1 : (Formalism.UG.cT s Y).map s = Yᵀ := by
      ext i j
      simp [Formalism.UG.cT, hs, sigR_invol σ hσ]
    set d := Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) δ with hd
    have e2 : D.map s = (-d) • J.map (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F)) := by
      ext i j
      simp only [hD, hd, hs, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, sigR_inclE, map_mul, hδ, hσ, map_neg,
        neg_mul]
    rw [e1, e2, Matrix.mul_smul, Matrix.smul_mul] at hy2
    have hu : Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (-δ)⁻¹ * (-d) = 1 := by
      rw [hd, ← map_neg, ← map_mul, inv_mul_cancel₀ (neg_ne_zero.mpr hδ0), map_one]
    have hy3 := congrArg (fun M => Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (-δ)⁻¹ • M) hy2
    simp only [smul_smul, hu, one_smul] at hy3
    exact hy3

end GlobalTheory.ThKUTrUnit
