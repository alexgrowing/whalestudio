import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.WField

noncomputable section

namespace PI.LocMassTypW.WGramP

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix
open scoped TensorProduct

theorem hform_sum_left {A : Type} [CommRing A] {n m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin n) (Fin n) A) (α : Fin m → A) (Y : Fin m → Fin n → A) (y : Fin n → A) :
    Formalism.UG.hform σ J (∑ c, α c • Y c) y = ∑ c, σ (α c) * Formalism.UG.hform σ J (Y c) y := by
  unfold Formalism.UG.hform
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  calc _ = ∑ i, ∑ c, ∑ j, σ (α c) * (σ (Y c i) * J i j * y j) :=
        Finset.sum_congr rfl fun i _ => by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring
    _ = _ := Finset.sum_comm

theorem hform_sum_right {A : Type} [CommRing A] {n m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin n) (Fin n) A) (x : Fin n → A) (β : Fin m → A) (Y : Fin m → Fin n → A) :
    Formalism.UG.hform σ J x (∑ d, β d • Y d) = ∑ d, β d * Formalism.UG.hform σ J x (Y d) := by
  unfold Formalism.UG.hform
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  calc _ = ∑ i, ∑ d, ∑ j, β d * (σ (x i) * J i j * Y d j) :=
        Finset.sum_congr rfl fun i _ => by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun j _ => by ring
    _ = _ := Finset.sum_comm

section Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem sigma_invol (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]

theorem hE_symm (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (x y : Fin n → E) :
    hE σ J x y = σ (hE σ J y x) := by
  unfold hE Formalism.UG.hform
  simp only [map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show σ (x j) * J j i * y i = σ (σ (y i)) * σ (J i j) * σ (x j)
  rw [sigma_invol σ hCM, hJ.1 j i]
  ring

theorem hermitian_form_standard_frame_vanishes (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) {r : ℕ} (P : Frame E n r) (T : F)
    (hP : P.IsStd σ J T) (c d : Fin (r + 1)) (hcd : ¬ (c = Fin.last r ∧ d = Fin.last r)) :
    hE σ J (F0 P c) (F0 P d) = 0 := by
  induction c using Fin.lastCases with
  | last =>
    induction d using Fin.lastCases with
    | last => exact absurd ⟨rfl, rfl⟩ hcd
    | cast j =>
      simp only [F0, Fin.snoc_last, Fin.snoc_castSucc]
      rw [hE_symm σ J hCM hJ, hP.2.2.2.1 j, map_zero]
  | cast i =>
    induction d using Fin.lastCases with
    | last =>
      simp only [F0, Fin.snoc_last, Fin.snoc_castSucc]
      exact hP.2.2.2.1 i
    | cast j =>
      simp only [F0, Fin.snoc_castSucc]
      exact hP.1 i j

theorem sigR_inclR (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := by
  simp [sigR, inclR, Algebra.TensorProduct.map_tmul]

theorem hR_ratV (v : HeightOneSpectrum (𝓞 F)) (a b : Fin n → E) :
    hR (Fv F v) σ J (ratV (F := F) (Fv F v) a) (ratV (F := F) (Fv F v) b) =
      inclR (Fv F v) (hE σ J a b) := by
  unfold hR hE Formalism.UG.hform
  simp only [map_sum, map_mul, ratV, JR, Matrix.map_apply, sigR_inclR]
  rfl

end Herm

end PI.LocMassTypW.WGramP

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix WGramP
open scoped TensorProduct

theorem gram_matrix_unitary_invariance : GramU := by
  classical
  intro F E _ _ _ _ _ σ n J ψ v r P T hStd hP x a b
  have hCM := hStd.1
  have hJ := hStd.2.1
  set Y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun c => ratV (F := F) (Fv F v) (F0 P c) with hY
  have hG0 : ∀ c d, ¬ (c = Fin.last r ∧ d = Fin.last r) → hR (Fv F v) σ J (Y c) (Y d) = 0 := by
    intro c d hcd
    rw [hY]
    simp only
    rw [hR_ratV, hermitian_form_standard_frame_vanishes σ J hCM hJ P T hP c d hcd, map_zero]
  have hlast : ∀ c, uMat v x (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
    intro c
    by_cases hc : c = Fin.last r
    · subst hc; simp [uMat]
    · have hlt : c < Fin.last r := lt_of_le_of_ne (Fin.le_last c) hc
      simp only [uMat, if_neg hc, if_neg (Ne.symm hc), dif_neg (not_lt_of_gt hlt)]
  show Formalism.UG.hform _ _ (∑ c, uMat v x c a • Y c) (∑ c, uMat v x c b • Y c) =
    Formalism.UG.hform _ _ (Y a) (Y b)
  rw [hform_sum_left]
  simp only [hform_sum_right]
  have hinner : ∀ c, ∑ d, uMat v x d b * Formalism.UG.hform (sigR (Fv F v) σ) (JR (Fv F v) J) (Y c) (Y d) =
      uMat v x (Fin.last r) b * hR (Fv F v) σ J (Y c) (Y (Fin.last r)) := by
    intro c
    rw [Finset.sum_eq_single (Fin.last r)]
    · rfl
    · intro d _ hd
      rw [show Formalism.UG.hform (sigR (Fv F v) σ) (JR (Fv F v) J) (Y c) (Y d) = hR (Fv F v) σ J (Y c) (Y d)
        from rfl, hG0 c d (fun h => hd h.2), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [hinner]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [hlast, hlast]
    show _ = hR (Fv F v) σ J (Y a) (Y b)
    by_cases ha : a = Fin.last r
    · by_cases hb : b = Fin.last r
      · subst ha; subst hb; simp
      · rw [if_neg hb, hG0 a b (fun h => hb h.2)]; simp
    · rw [if_neg ha, hG0 a b (fun h => ha h.1)]; simp
  · intro c _ hc
    rw [hG0 c (Fin.last r) (fun h => hc h.1), mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem unipSplitF (hS : SplitR) (hLs : LatStd) : UnipSplitF :=
  unipSplitF_of gram_matrix_unitary_invariance hS hLs

end PI.LocMassTypW
