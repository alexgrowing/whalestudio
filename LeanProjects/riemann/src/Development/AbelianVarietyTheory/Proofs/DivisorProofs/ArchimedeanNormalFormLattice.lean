import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct

namespace GlobalTheory.ThKUTr

theorem trHom_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (δ : E) (Φ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E ≃+* (InfinitePlace F → ℂ) × (E ⊗[F] Formalism.MainNotions.S.Af F)) (ε : InfinitePlace F → Fin n → Bool) (P : InfinitePlace F → (Matrix (Fin n) (Fin n) ℂ)ˣ), IsCMExt F E σ → σ δ = -δ → δ ≠ 0 → (∀ i j, σ (J j i) = -J i j) → (∀ x : E, Φ (inclR (F := F) (AF F) x) = (fun w => (B.emb w).1 x, Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) x)) → (∀ z, Φ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = (fun w => star ((Φ z).1 w), Formalism.UG.sigR σ (Formalism.MainNotions.S.Af F) (Φ z).2)) → (∀ w, ((P w : Matrix (Fin n) (Fin n) ℂ))ᴴ * (δ • J.map σ).map (B.emb w).1 * (P w : Matrix (Fin n) (Fin n) ℂ) = Formalism.REAL.Jm (ε w)) → ∀ (hU : ∀ x, GlobalTheory.ThKUTr.rawT Φ ε P (Formalism.UG.UPts σ (δ • J.map σ) (Formalism.MainNotions.S.Af F)) x ∈ UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J)), Function.Surjective (GlobalTheory.ThKUTr.trHom σ J Φ ε P (Formalism.UG.UPts σ (δ • J.map σ) (Formalism.MainNotions.S.Af F)) hU) := by
  intro F E _ _ _ _ _ σ B n J δ Φ ε P hCM hδ hδ0 hJ hΦ hΦc hP hU g

  have hσσ : ∀ x : E, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]
  let G : GL (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) := g.1
  have hg : (G : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J *
      (G : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J := g.2
  let φw : InfinitePlace F → (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E →+* ℂ) := fun w =>
    (Pi.evalRingHom (fun _ : InfinitePlace F => ℂ) w).comp ((RingHom.fst _ _).comp Φ.toRingHom)
  let φf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E →+* E ⊗[F] Formalism.MainNotions.S.Af F := (RingHom.snd _ _).comp Φ.toRingHom
  let gw : InfinitePlace F → (Matrix (Fin n) (Fin n) ℂ)ˣ := fun w => Units.map (φw w).mapMatrix.toMonoidHom G
  let y : GL (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F) := Units.map φf.mapMatrix.toMonoidHom G
  have hgw : ∀ w, ((gw w : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      (G : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)).map (φw w) := fun w => rfl
  have hy : ((y : GL (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) =
      (G : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)).map φf := rfl

  have hreal : ∀ w, ((gw w : Matrix (Fin n) (Fin n) ℂ))ᴴ * (δ • J.map σ).map (B.emb w).1 * (gw w : Matrix (Fin n) (Fin n) ℂ) =
      (δ • J.map σ).map (B.emb w).1 := by
    intro w
    have h1 := congrArg (fun M => M.map (φw w)) hg
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h1
    have hinc : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J).map (φw w) = J.map (B.emb w).1 := by
      ext i j
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply]
      show (Φ (inclR (F := F) (AF F) (J i j))).1 w = _
      rw [hΦ]
    have hc : (φw w) ∘ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = star ∘ (φw w) := by
      funext z
      show (Φ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z)).1 w = star ((Φ z).1 w)
      rw [hΦc]

    simp only [hinc, hc] at h1
    rw [show (G : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)).map (star ∘ φw w) =
      ((gw w : Matrix (Fin n) (Fin n) ℂ)).map (starRingEnd ℂ) from by ext i j; rfl, ← hgw w] at h1
    have hA : (δ • J.map σ).map (B.emb w).1 = ((B.emb w).1 δ) • (J.map (B.emb w).1).map (starRingEnd ℂ) := by
      ext i j
      simp [Matrix.smul_apply, hCM.2.2.2]
    have h2 := congrArg (fun M => M.map (starRingEnd ℂ)) h1
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h2
    have hss : (starRingEnd ℂ) ∘ (starRingEnd ℂ) = id := by funext z; simp
    rw [hss, Matrix.map_id] at h2
    rw [hA, Matrix.mul_smul, Matrix.smul_mul]
    congr 1

  have hsig2 : ∀ z : E ⊗[F] Formalism.MainNotions.S.Af F, Formalism.UG.sigR σ (Formalism.MainNotions.S.Af F) (Formalism.UG.sigR σ (Formalism.MainNotions.S.Af F) z) = z := by
    have hid : (σ.comp σ) = AlgHom.id F E := AlgHom.ext hσσ
    intro z
    show (Algebra.TensorProduct.map σ (AlgHom.id F (Formalism.MainNotions.S.Af F))) ((Algebra.TensorProduct.map σ (AlgHom.id F (Formalism.MainNotions.S.Af F))) z) = z
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, hid, AlgHom.comp_id, Algebra.TensorProduct.map_id]
    rfl
  have hfin : y ∈ Formalism.UG.UPts σ (δ • J.map σ) (Formalism.MainNotions.S.Af F) := by
    have h1 := congrArg (fun M => M.map φf) hg
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h1
    have hinc : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J).map φf = J.map (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F)) := by
      ext i j
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply]
      show (Φ (inclR (F := F) (AF F) (J i j))).2 = _
      rw [hΦ]
    have hc : φf ∘ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = (Formalism.UG.sigR σ (Formalism.MainNotions.S.Af F)) ∘ φf := by
      funext z
      show (Φ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z)).2 = Formalism.UG.sigR σ (Formalism.MainNotions.S.Af F) (Φ z).2
      rw [hΦc]
    simp only [hinc, hc] at h1
    rw [← Matrix.map_map, ← hy] at h1
    have h2 := congrArg (fun M => M.map (Formalism.UG.sigR σ (Formalism.MainNotions.S.Af F))) h1
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h2
    have hss : (Formalism.UG.sigR σ (Formalism.MainNotions.S.Af F)) ∘ (Formalism.UG.sigR σ (Formalism.MainNotions.S.Af F)) = id := funext hsig2
    rw [hss, Matrix.map_id] at h2
    have hJs : J.map ((Formalism.UG.sigR σ (Formalism.MainNotions.S.Af F)) ∘ (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F))) =
        (J.map σ).map (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F)) := by
      ext i j
      simp only [Matrix.map_apply]
      show (Algebra.TensorProduct.map σ (AlgHom.id F (Formalism.MainNotions.S.Af F))) (J i j ⊗ₜ 1) = σ (J i j) ⊗ₜ 1
      rw [Algebra.TensorProduct.map_tmul]
      rfl
    have hA : (δ • J.map σ).map (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F)) =
        (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) δ) • (J.map σ).map (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F)) := by
      ext i j
      simp [Matrix.smul_apply]
    rw [hJs] at h2
    show Formalism.UG.cT (Formalism.UG.sigR σ (Formalism.MainNotions.S.Af F)) (y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) *
      (δ • J.map σ).map (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F)) * (y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) =
      (δ • J.map σ).map (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F))
    rw [hA, Matrix.mul_smul, Matrix.smul_mul, Formalism.UG.cT]
    congr 1
  refine ⟨(fun w => ⟨(P w)⁻¹ * gw w * P w, ?_⟩, ⟨y, hfin⟩), ?_⟩
  · show (((P w)⁻¹ * gw w * P w : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm (ε w) *
      (((P w)⁻¹ * gw w * P w : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = Formalism.REAL.Jm (ε w)
    rw [← hP w]
    simp only [Units.val_mul, Matrix.conjTranspose_mul]
    have hPP : (((P w)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * ((P w : Matrix (Fin n) (Fin n) ℂ))ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    have hPP' : (P w : Matrix (Fin n) (Fin n) ℂ) * (((P w)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
      Units.mul_inv _
    calc _ = ((P w : Matrix (Fin n) (Fin n) ℂ))ᴴ * (((gw w : Matrix (Fin n) (Fin n) ℂ))ᴴ *
          (((((P w)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * ((P w : Matrix (Fin n) (Fin n) ℂ))ᴴ) *
            (δ • J.map σ).map (B.emb w).1 *
            ((P w : Matrix (Fin n) (Fin n) ℂ) * (((P w)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))) *
          (gw w : Matrix (Fin n) (Fin n) ℂ)) * (P w : Matrix (Fin n) (Fin n) ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPP, hPP', Matrix.one_mul, Matrix.mul_one, hreal w]
  · apply Subtype.ext
    apply Units.ext
    refine (GlobalTheory.ThKUTr.rawT_val Φ ε P _ _).trans ?_
    ext i j
    rw [GlobalTheory.ThKUTr.glueM_apply]
    rw [← Φ.symm_apply_apply ((G : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) i j)]
    congr 1
    refine Prod.ext ?_ rfl
    funext w
    show ((P w : Matrix (Fin n) (Fin n) ℂ) * (((P w)⁻¹ * gw w * P w : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
        (((P w)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) i j = (φw w) ((G : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) i j)
    rw [Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul,
      Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, hgw w]
    rfl

end GlobalTheory.ThKUTr
