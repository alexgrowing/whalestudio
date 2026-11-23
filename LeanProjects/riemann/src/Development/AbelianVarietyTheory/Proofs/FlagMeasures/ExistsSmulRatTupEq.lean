import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuadBaseChangeIsFieldOrSplit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.LocalWittND

theorem exists_gl {K S : Type} [Field K] [CommRing S] (s : S →+* S) (hs : ∀ x, s (s x) = x)
    (h2 : (2 : S) ≠ 0) (hS : IsField S ∨ ∃ φ : S ≃+* K × K, ∀ x, φ (s x) = (φ x).swap)
    {n a : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, s (J j i) = J i j) (hd : IsUnit J.det)
    (X Y : Matrix (Fin n) (Fin a) S) (hX : IsUnit (Formalism.UG.cT s X * J * X).det)
    (hXY : Formalism.UG.cT s Y * J * Y = Formalism.UG.cT s X * J * X) :
    ∃ γ : GL (Fin n) S, Formalism.UG.cT s γ.1 * J * γ.1 = J ∧ γ.1 * X = Y := by
  have key : ∀ {m : ℕ} (Z : Matrix (Fin n) (Fin m) S),
      Zᵀ * Jᵀ * Z.map s = (Formalism.UG.cT s Z * J * Z)ᵀ := by
    intro m Z
    simp only [Formalism.UG.cT, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hX' : IsUnit (Xᵀ * Jᵀ * X.map s).det := by rw [key, Matrix.det_transpose]; exact hX
  have hXY' : Yᵀ * Jᵀ * Y.map s = Xᵀ * Jᵀ * X.map s := by rw [key, key, hXY]
  have : ∃ γ : Matrix (Fin n) (Fin n) S, γᵀ * Jᵀ * γ.map s = Jᵀ ∧ γ * X = Y := by
    rcases hS with hF | ⟨φ, hφ⟩
    · letI := hF.toField
      obtain ⟨γ, h1, h3⟩ := GlobalTheory.HermWitt.exists_gl_isometry_mul_eq_of_det_ne_zero (c := s)
        h2 hs (G := Jᵀ) (fun i j => hJ i j) (X := X) (Y := Y) hX'.ne_zero hXY'
      exact ⟨γ, h1, h3⟩
    · exact GlobalTheory.HermTuple.exists_matrix_split s φ hφ Jᵀ (fun i j => hJ i j)
        (by rwa [Matrix.det_transpose]) X Y hX' hXY'
  obtain ⟨γ, h1, h3⟩ := this
  rw [key] at h1
  have h4 := Matrix.transpose_injective h1
  have hγ : IsUnit γ.det := by
    rw [← h4, Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  obtain ⟨G, hG⟩ := (Matrix.isUnit_iff_isUnit_det γ).2 hγ
  exact ⟨G, by rw [hG]; exact h4, by rw [hG]; exact h3⟩

theorem gram_eq {S : Type} [CommRing S] (s : S →+* S) {n a : ℕ} (J : Matrix (Fin n) (Fin n) S)
    (Z : Fin a → Fin n → S) :
    (Matrix.of fun k l => Formalism.UG.hform s J (Z k) (Z l)) =
      Formalism.UG.cT s (Matrix.of Z)ᵀ * J * (Matrix.of Z)ᵀ := by
  ext k l
  simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem gramR_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (X : Fin a → Fin n → E) :
    gramR R σ J (ratTup (F := F) R X) = (gramE σ J X).map (inclR (F := F) R) := by
  ext k l
  simp only [gramR, gramE, hR, hE, Formalism.UG.hform, map_sum, map_mul, ratTup, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2

theorem invol_of_isCMExt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : (∀ a, σ (σ a) = a) ∧ ∃ a, σ a ≠ a := by
  obtain ⟨-, hE, -, hσ⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine ⟨fun a => τ.injective (by rw [hσ, hσ, star_star]), ?_⟩
  by_contra hc
  push Not at hc
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hσ τ x
  rw [hc] at this
  exact this.symm

theorem exists_smul_eq_field {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (K : Type) [Field K] [Algebra F K]
    {n a : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    (X Y : Fin a → Fin n → K ⊗[F] E) (hX : IsUnit (gramR K σ J X).det)
    (hXY : gramR K σ J Y = gramR K σ J X) : ∃ g : HA K σ J, g • X = Y := by
  obtain ⟨hi, hne⟩ := invol_of_isCMExt hcm
  have hS := (GlobalTheory.quadBaseChange_isField_or_split F E K σ hcm.2.2.1 hi hne).1
  have hg : ∀ Z : Fin a → Fin n → K ⊗[F] E, gramR K σ J Z = _ :=
    fun Z => gram_eq (sigR K σ) (JR K J) Z
  have h2 : (2 : K ⊗[F] E) ≠ 0 := by
    have : inclR (F := F) K (2 : E) ≠ 0 := by
      rw [map_ne_zero]; exact two_ne_zero
    rwa [map_ofNat] at this
  obtain ⟨γ, h1, h3⟩ := exists_gl (sigR K σ)
    (fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul k e => exact congrArg (k ⊗ₜ[F] ·) (hi e)
      | add x y hx hy => simp only [map_add, hx, hy])
    h2 hS (JR K J)
    (fun i j => by
      show (1 : K) ⊗ₜ[F] σ (J j i) = (1 : K) ⊗ₜ[F] J i j
      rw [hJ.1])
    (by
      have := (hJ.2.isUnit).map (inclR (F := F) K)
      rwa [RingHom.map_det] at this)
    (Matrix.of X)ᵀ (Matrix.of Y)ᵀ (by rw [← hg]; exact hX) (by rw [← hg, ← hg]; exact hXY)
  refine ⟨(⟨γ, h1⟩ : HR K σ J), ?_⟩
  funext k i
  exact congrFun (congrFun h3 i) k

theorem exists_smul_ratTup_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (X0 : Fin a → Fin n → E), (gramE σ J X0).det ≠ 0 → ∀ y : Fin a → Fin n → Fv F v ⊗[F] E, gramR (Fv F v) σ J y = (gramE σ J X0).map (inclR (Fv F v)) → ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) X0 = y := by
  intro F E _ _ _ _ _ σ hcm n J hJ v a X0 hX y hy
  refine exists_smul_eq_field hcm (Fv F v) hJ _ _ ?_ (by rw [hy, gramR_ratTup])
  have := hX.isUnit.map (inclR (F := F) (Fv F v))
  rw [gramR_ratTup]
  rwa [RingHom.map_det] at this

end GlobalTheory.LocalWittND
