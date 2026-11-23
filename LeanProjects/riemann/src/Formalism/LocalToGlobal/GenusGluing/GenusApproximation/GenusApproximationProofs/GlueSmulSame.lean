import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GlueExists

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

section Alg

variable {A : Type} [CommRing A] {m : Type} [Fintype m] [DecidableEq m]

def glueM (e : A) (M : Matrix m m A) : Matrix m m A := e • M + (1 - e) • (1 : Matrix m m A)

theorem glueM_mul {e : A} (he : e * e = e) (X Y : Matrix m m A) :
    glueM e X * glueM e Y = glueM e (X * Y) := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [glueM, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one,
    Matrix.one_mul, h1, h2, h3, he, zero_smul, add_zero, zero_add]

theorem glueM_one (e : A) : glueM e (1 : Matrix m m A) = 1 := by
  rw [glueM, ← add_smul, add_sub_cancel, one_smul]

def glueU {e : A} (he : e * e = e) (g : GL m A) : GL m A where
  val := glueM e (g : Matrix m m A)
  inv := glueM e ((g⁻¹ : GL m A) : Matrix m m A)
  val_inv := by rw [glueM_mul he, Units.mul_inv, glueM_one]
  inv_val := by rw [glueM_mul he, Units.inv_mul, glueM_one]

theorem glueU_val {e : A} (he : e * e = e) (g : GL m A) :
    ((glueU he g : GL m A) : Matrix m m A) = glueM e (g : Matrix m m A) := rfl

theorem cT_glueM (σ : A →+* A) {e : A} (hσ : σ e = e) (M : Matrix m m A) :
    Formalism.UG.cT σ (glueM e M) = glueM e (Formalism.UG.cT σ M) := by
  ext a b
  simp only [Formalism.UG.cT, glueM, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hσ]
  rw [Matrix.one_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

theorem glueU_mem (σ : A →+* A) {e : A} (he : e * e = e) (hσ : σ e = e) {g : GL m A}
    (hg : g ∈ Formalism.UG.UJ σ (1 : Matrix m m A)) : glueU he g ∈ Formalism.UG.UJ σ (1 : Matrix m m A) := by
  have hg' : Formalism.UG.cT σ (g : Matrix m m A) * 1 * (g : Matrix m m A) = 1 := hg
  show Formalism.UG.cT σ ((glueU he g : GL m A) : Matrix m m A) * 1 * ((glueU he g : GL m A) : Matrix m m A) = 1
  rw [glueU_val, cT_glueM σ hσ, Matrix.mul_one, glueM_mul he]
  rw [Matrix.mul_one] at hg'
  rw [hg', glueM_one]

theorem glue_smul_zero {f e : A} (hfe : f * e = 0) (M Y : Matrix m m A) :
    f • (glueM e M * Y) = f • Y := by
  rw [glueM, add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul, smul_smul,
    hfe, zero_smul, zero_add, mul_sub, mul_one, hfe, sub_zero]

theorem glue_smul_same {f e : A} (hfe : f * e = f) (M Y : Matrix m m A) :
    f • (glueM e M * Y) = f • (M * Y) := by
  rw [glueM, add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul, smul_smul,
    hfe, mul_sub, mul_one, hfe, sub_self, zero_smul, add_zero]

end Alg

section Idem

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem eP_congr {P Q : HeightOneSpectrum (𝓞 F) → Prop} (h : ∀ v, P v ↔ Q v) : eP E P = eP E Q := by
  have hPQ : P = Q := funext fun v => propext (h v)
  subst hPQ
  rfl

theorem eP_false : eP E (fun _ : HeightOneSpectrum (𝓞 F) => False) = 0 := by
  have h0 : ((Formalism.L2.DIV.idemAd (fun _ : HeightOneSpectrum (𝓞 F) => False) : Formalism.UG.intAd F)
      : Formalism.L2.Herm.Af F) = 0 := by
    ext v
    rw [Formalism.L2.DIV.idemAd_neg (P := fun _ : HeightOneSpectrum (𝓞 F) => False) (v := v) (fun h => h)]
    rfl
  rw [eP, h0, TensorProduct.tmul_zero]

theorem sigR_eP [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (P : HeightOneSpectrum (𝓞 F) → Prop) :
    Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) (eP E P) = eP E P := by
  rw [Formalism.UG.sigR, eP]
  simp

end Idem

theorem glueExists_of : IdemCalc → GlueExists := by
  intro hI F E _ _ _ _ _ _ hc n T γ
  classical
  have hmul : ∀ P Q : HeightOneSpectrum (𝓞 F) → Prop, eP E P * eP E Q = eP E (fun v => P v ∧ Q v) :=
    (hI F E).2.1
  have hAt : ∀ v : HeightOneSpectrum (𝓞 F), eAt E v = eP E (fun w => w = v) := fun v => rfl
  suffices key : ∃ y ∈ UAd hc n,
      (∀ v ∈ T, eAt E v • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        eAt E v • ((Formalism.UG.bc (iA F E) ((γ v : GL (Fin n) E)⁻¹) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
          Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) ∧
      eP E (fun v => v ∉ T) • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        eP E (fun v => v ∉ T) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) by
    obtain ⟨y, hy, h1, h2⟩ := key
    refine ⟨y⁻¹, inv_mem hy, ?_, ?_⟩
    · intro v hv; rw [inv_inv]; exact h1 v hv
    · rw [inv_inv]; exact h2
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, fun v hv => absurd hv (Finset.notMem_empty v), rfl⟩
  | insert v T hv ih =>
    obtain ⟨y, hy, h1, h2⟩ := ih
    have hgU : Formalism.UG.bc (iA F E) ((γ v : GL (Fin n) E)⁻¹) ∈ UAd hc n := (ratIn hc n (γ v)⁻¹).2
    have hev : eAt E v * eAt E v = eAt E v := by
      rw [hAt, hmul]; exact eP_congr (fun u => and_self_iff)
    have hσ : Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) (eAt E v) = eAt E v := sigR_eP hc _
    have hJ : (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    have hgU' : Formalism.UG.bc (iA F E) ((γ v : GL (Fin n) E)⁻¹) ∈
        Formalism.UG.UJ (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F)) (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      have h := hgU
      change _ ∈ Formalism.UG.UJ (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
        ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) at h
      rwa [hJ] at h
    have hzU : glueU hev (Formalism.UG.bc (iA F E) ((γ v : GL (Fin n) E)⁻¹)) ∈ UAd hc n := by
      change _ ∈ Formalism.UG.UJ (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
        ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)))
      rw [hJ]
      exact glueU_mem _ hev hσ hgU'
    refine ⟨glueU hev (Formalism.UG.bc (iA F E) ((γ v : GL (Fin n) E)⁻¹)) * y, mul_mem hzU hy, ?_, ?_⟩
    · intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with hwv | hw
      · rw [hwv, Units.val_mul, glueU_val, glue_smul_same hev]
        have hvT : eAt E v * eP E (fun u => u ∉ T) = eAt E v := by
          rw [hAt, hmul]
          exact eP_congr (fun u => ⟨fun h => h.1, fun h => ⟨h, by rw [h]; exact hv⟩⟩)
        have hy1 : eAt E v • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
            eAt E v • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
          calc eAt E v • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
              = (eAt E v * eP E (fun u => u ∉ T)) • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
                  Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by rw [hvT]
            _ = eAt E v • (eP E (fun u => u ∉ T) • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
                  Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by rw [smul_smul]
            _ = eAt E v • (eP E (fun u => u ∉ T) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by rw [h2]
            _ = eAt E v • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by rw [smul_smul, hvT]
        rw [← Matrix.mul_smul, hy1, Matrix.mul_smul, Matrix.mul_one]
      · have hwv : w ≠ v := fun h => hv (h ▸ hw)
        have h0 : eAt E w * eAt E v = 0 := by
          rw [hAt w, hAt v, hmul, ← eP_false]
          exact eP_congr (fun u => ⟨fun h => hwv (h.1.symm.trans h.2), False.elim⟩)
        rw [Units.val_mul, glueU_val, glue_smul_zero h0]
        exact h1 w hw
    · have hf0 : eP E (fun u => u ∉ insert v T) * eAt E v = 0 := by
        rw [hAt v, hmul, ← eP_false]
        exact eP_congr (fun u => ⟨fun h => h.1 (by rw [h.2]; exact Finset.mem_insert_self v T), False.elim⟩)
      have hff : eP E (fun u => u ∉ insert v T) * eP E (fun u => u ∉ T) = eP E (fun u => u ∉ insert v T) := by
        rw [hmul]
        exact eP_congr (fun u => ⟨fun h => h.1, fun h => ⟨h, fun hu => h (Finset.mem_insert_of_mem hu)⟩⟩)
      rw [Units.val_mul, glueU_val, glue_smul_zero hf0]
      calc eP E (fun u => u ∉ insert v T) • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
            Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
          = (eP E (fun u => u ∉ insert v T) * eP E (fun u => u ∉ T)) • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
              Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by rw [hff]
        _ = eP E (fun u => u ∉ insert v T) • (eP E (fun u => u ∉ T) • ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
              Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by rw [smul_smul]
        _ = eP E (fun u => u ∉ insert v T) • (eP E (fun u => u ∉ T) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by
              rw [h2]
        _ = eP E (fun u => u ∉ insert v T) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
              rw [smul_smul, hff]

end Formalism.L2.GenusGluing.Gen
