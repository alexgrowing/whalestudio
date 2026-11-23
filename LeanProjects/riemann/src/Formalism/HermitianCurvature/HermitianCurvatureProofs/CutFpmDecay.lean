import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.JCx2

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section poly

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def pvar (g : B.Mat k r) : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℂ :=
  Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))

def entL (a b : Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => g a b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

def entLc (a b : Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => star (g a b)
      map_add' := fun g h => by simp [Matrix.add_apply]
      map_smul' := fun c g => by simp [Matrix.smul_apply] }

private theorem deriv_smul_const_at_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : ℝ → ℂ) (T : E) :
    deriv (fun t => φ t • T) 0 = deriv φ 0 • T := by
  by_cases hφ : DifferentiableAt ℝ φ 0
  · exact deriv_smul_const hφ T
  by_cases hT : T = 0
  · simp [hT]
  rw [deriv_zero_of_not_differentiableAt hφ, zero_smul]
  apply deriv_zero_of_not_differentiableAt
  intro hd
  apply hφ

  obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℂ T (norm_ne_zero_iff.2 hT)
  have hℓT : ℓ T ≠ 0 := by
    rw [hℓ]
    exact Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hT)
  have h2 : DifferentiableAt ℝ (fun t => ℓ (φ t • T) / ℓ T) 0 :=
    ((ℓ.restrictScalars ℝ).differentiableAt.comp (0 : ℝ) hd).div_const _
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show φ t = ℓ (φ t • T) / ℓ T
  rw [map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hℓT]

private theorem dLR_smul_const_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : B.Mat k r → ℂ) (T : E)
    (u v : List (B.Mat k r)) : B.dLR u v (fun g => φ g • T) = fun g => B.dLR u v φ g • T := by
  have hR : ∀ v : List (B.Mat k r), B.Rw v (fun g => φ g • T) = fun g => B.Rw v φ g • T := by
    intro v
    induction v with
    | nil => rfl
    | cons X v ih =>
      funext g
      show Formalism.REAL.RdV X (B.Rw v fun g => φ g • T) g = Formalism.REAL.RdV X (B.Rw v φ) g • T
      rw [ih]
      exact deriv_smul_const_at_zero _ T
  unfold B.dLR
  rw [hR v]
  induction u with
  | nil => rfl
  | cons X u ih =>
    funext g
    show B.LdV X (u.foldr B.LdV fun g => B.Rw v φ g • T) g = B.LdV X (u.foldr B.LdV (B.Rw v φ)) g • T
    rw [ih]
    exact deriv_smul_const_at_zero _ T

private theorem ckOn_of_contDiff_infty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (m : ℕ∞) (UU : Set (B.Mat k r)) : B.CkOn m UU f :=
  fun _ _ => ⟨Set.univ, f, isOpen_univ, Set.mem_univ _,
    (hf.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn, fun _ _ _ => rfl⟩

private theorem pdGood_of_isPolyDeg {κ : ℕ} {c : B.Mat k r → ℂ} (hc : U.IsPolyDeg κ c) : pdGood Wp Wq κ c := by
  obtain ⟨hcd, hwb⟩ := PI.UnitaryCorollaryDerivatives.polynomial_bound k r κ c hc
  refine ⟨fun F hF => ?_, fun A m => ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hF g₀ hg₀
    refine ⟨U, fun g => c g • f' g, hU, hgU, hcd.contDiffOn.smul hf', fun g hg hgv => ?_⟩
    simp only [hfe g hg hgv]
  · obtain ⟨C, hC⟩ := hwb m
    refine ⟨2 ^ m * |C|, by positivity, fun F b hF => ?_⟩
    have hab : ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
        u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ (∅ : Set (B.Mat k r)) →
          ‖B.dLR u v (fun g => c g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) g‖ ≤ C * B.gN g ^ (κ : ℝ) := by
      intro u v hu hv hl g hg _
      have h1 := hC u v hu hv hl g hg
      simp only [List.map_append, List.sum_append] at h1
      simp only [dLR_smul_const_right, norm_smul]
      have h1' : ‖B.dLR u v c g‖ ≤ C * B.gN g ^ (κ : ℝ) := by simpa using h1
      calc ‖B.dLR u v c g‖ * ‖ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖ ≤ ‖B.dLR u v c g‖ * 1 :=
            mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ ≤ C * B.gN g ^ (κ : ℝ) := by rw [mul_one]; exact h1'
    obtain ⟨hP1, hP2⟩ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound (O := ∅) (UU := B.GV k r)
      (a := fun g => c g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) isOpen_empty (fun g hg => Or.inr hg)
      (ckOn_of_contDiff_infty _ (hcd.smul contDiff_const) _ _) hab hF (fun g _ h => by simp at h)
    have hfun : Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap (fun g => c g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) F =
        fun g => c g • F g := by
      funext g
      simp [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap]
    rw [hfun] at hP1 hP2
    refine ⟨hP1, fun u v hu hv hl g hg => ?_⟩
    have hb0 : 0 ≤ b := le_trans
      (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _))
      (hF.2 [] [] (by simp) (by simp) (by simp) g hg)
    calc _ ≤ 2 ^ m * (|C| * |b|) := hP2 u v hu hv hl g hg
      _ = 2 ^ m * |C| * b := by rw [abs_of_nonneg hb0]; ring

theorem pd_good_pow {d : ℕ} {c : B.Mat k r → ℂ} (hc : pdGood Wp Wq d c) :
    ∀ e : ℕ, pdGood Wp Wq (d * e) (fun g => c g ^ e)
  | 0 => pd_good_congr (fun g _ => by simp) (pd_good_const (Wp := Wp) (Wq := Wq) (d * 0) (1 : ℂ))
  | e + 1 => pd_good_congr (fun g _ => (pow_succ (c g) e).symm)
      (pd_good_mul (by rw [Nat.mul_succ]) (pd_good_pow hc e) hc)

theorem pd_good_of_poly {κ : ℕ} {c : B.Mat k r → ℂ} (hc : U.IsPolyDeg κ c) : pdGood Wp Wq κ c :=
  pdGood_of_isPolyDeg hc

end poly

section decay

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem pd_good_Gpow (z z' : Fin (2 * r + k + 1) → ℂ) (q : ℕ) :
    pdGood Wp Wq ((2 * r + 2) * q) (fun g : B.Mat k r => ((Gf k r z z' g ^ q : ℝ) : ℂ)) := by
  have := pd_good_pow (Wp := Wp) (Wq := Wq) (pd_good_of_poly (Formalism.FourierDecayAlt.P.gram_function_polynomial k r z z')) q
  simpa only [Complex.ofReal_pow] using this

theorem inCC_Gpow_smul (z z' : Fin (2 * r + k + 1) → ℂ) (q : ℕ) {A₀ : ℝ} {f : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hf : ∀ m : ℕ, B.InCC A₀ m f) :
    ∀ m : ℕ, B.InCC (A₀ - (((2 * r + 2) * q : ℕ) : ℝ)) m (fun g => ((Gf k r z z' g ^ q : ℝ) : ℂ) • f g) := by
  intro m
  obtain ⟨c, hc⟩ := hf m
  obtain ⟨K, -, hb⟩ := (pd_good_Gpow (Wp := Wp) (Wq := Wq) z z' q).2 (A₀ - (((2 * r + 2) * q : ℕ) : ℝ)) m
  exact ⟨K * c, hb f c (by rwa [sub_add_cancel])⟩

theorem ckOn_Gpow_smul (z z' : Fin (2 * r + k + 1) → ℂ) (q : ℕ) {f : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hf : B.CkOn ⊤ (B.GV k r) f) : B.CkOn ⊤ (B.GV k r) (fun g => ((Gf k r z z' g ^ q : ℝ) : ℂ) • f g) :=
  (pd_good_Gpow (Wp := Wp) (Wq := Wq) z z' q).1 f hf

end decay

section fpm

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem fpm_id (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ : ℕ) :
    TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ =
      fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • f g := by
  funext g
  simp only [TBBx4.fpm, ContinuousLinearMap.comp_id]

theorem inCC_fpm_id (p : KB.Pl P Wp Wq) {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (p₀ : ℕ) {A₀ : ℝ}
    (hf : ∀ m : ℕ, B.InCC A₀ m f) :
    ∀ m : ℕ, B.InCC (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) m
      (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) := by
  rw [fpm_id]
  exact inCC_Gpow_smul _ _ p₀ hf

end fpm

end

end Formalism.FourierDecayAlt.P.CutBP
