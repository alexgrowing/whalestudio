import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CurvNormNonneg

noncomputable section

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open scoped ComplexOrder ContDiff

namespace GlobalTheory.HodgeDomain

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem smoothOn_det {n : ℕ} {M : Pt ι p q → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, SmoothOn fun z => M z a b) :
    SmoothOn fun z => (M z).det := by
  unfold SmoothOn at *
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem smoothOn_inv {n : ℕ} {M : Pt ι p q → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, SmoothOn fun z => M z a b)
    (hd : ∀ z ∈ DomI ι p q, (M z).det ≠ 0) (a b : Fin n) : SmoothOn fun z => (M z)⁻¹ a b := by
  have hadj : SmoothOn fun z => (M z).adjugate a b := by
    simp only [adjugate_apply]
    refine smoothOn_det fun i j => ?_
    by_cases e : i = b
    · simp only [e, updateRow_self]; exact contDiffOn_const
    · simp only [updateRow_ne e]; exact h i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact ContDiffOn.mul (ContDiffOn.inv (smoothOn_det h) fun v hv => hd _ hv) hadj

theorem smoothOn_coord (τ : ι) (a : Fin p) (b : Fin q) : SmoothOn fun z : Pt ι p q => z τ a b :=
  (contDiff_apply ℝ ℂ (τ, a, b)).contDiffOn

theorem smoothOn_star {f : Pt ι p q → ℂ} (h : SmoothOn f) : SmoothOn fun z => star (f z) :=
  Complex.conjCLE.contDiff.comp_contDiffOn h

theorem smoothOn_hP (τ : ι) (a b : Fin p) : SmoothOn fun z : Pt ι p q => hP (z τ) a b := by
  simp only [hP, Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply]
  exact contDiffOn_const.sub (ContDiffOn.sum fun k _ =>
    ContDiffOn.mul (smoothOn_coord τ a k) (smoothOn_star (smoothOn_coord τ b k)))

theorem smoothOn_hQ (τ : ι) (a b : Fin q) : SmoothOn fun z : Pt ι p q => hQ (z τ) a b := by
  simp only [hQ, Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply]
  exact contDiffOn_const.sub (ContDiffOn.sum fun k _ =>
    ContDiffOn.mul (smoothOn_star (smoothOn_coord τ k a)) (smoothOn_coord τ k b))

theorem smoothOn_hP_inv (τ : ι) (a b : Fin p) : SmoothOn fun z : Pt ι p q => (hP (z τ))⁻¹ a b :=
  smoothOn_inv (smoothOn_hP τ) (fun _ hz => (hP_posDef (hz τ)).det_pos.ne') a b

theorem smoothOn_hQ_inv (τ : ι) (a b : Fin q) : SmoothOn fun z : Pt ι p q => (hQ (z τ))⁻¹ a b :=
  smoothOn_inv (smoothOn_hQ τ) (fun z hz => (show (hQ (z τ)).PosDef from hz τ).det_pos.ne') a b

def bergman (z : Pt ι p q) : Pt ι p q →ₗ[ℂ] Pt ι p q →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun ξ η => ∑ τ, ((hP (z τ))⁻¹ * ξ τ * (hQ (z τ))⁻¹ * (η τ)ᴴ).trace)
    (fun _ _ _ => by simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum])
    (fun _ _ _ => by simp [Matrix.mul_add, Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum])

theorem bergman_apply (z ξ η : Pt ι p q) :
    bergman z ξ η = ∑ τ, ((hP (z τ))⁻¹ * ξ τ * (hQ (z τ))⁻¹ * (η τ)ᴴ).trace := rfl

theorem trace_pos {A : Matrix (Fin p) (Fin p) ℂ} {B : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (ξ : Matrix (Fin p) (Fin q) ℂ) : 0 ≤ (A * ξ * B * ξᴴ).trace ∧ (ξ ≠ 0 → 0 < (A * ξ * B * ξᴴ).trace) := by
  open MatrixOrder in
  obtain ⟨R, hR, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hA.isStrictlyPositive
  open MatrixOrder in
  obtain ⟨S, hS, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self.1 hB.isStrictlyPositive
  have e : (star R * R * ξ * (S * star S) * ξᴴ).trace = ((R * ξ * S) * (R * ξ * S)ᴴ).trace := by
    simp only [star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e]
  have h0 := (posSemidef_self_mul_conjTranspose (R * ξ * S)).trace_nonneg
  refine ⟨h0, fun hξ => lt_of_le_of_ne h0 fun h => hξ ?_⟩
  have h1 := trace_mul_conjTranspose_self_eq_zero_iff.1 h.symm
  have hR' := (isUnit_iff_isUnit_det _).1 hR
  have hS' := (isUnit_iff_isUnit_det _).1 hS
  have : R⁻¹ * (R * ξ * S) * S⁻¹ = ξ := by
    rw [Matrix.mul_assoc R, nonsing_inv_mul_cancel_left _ _ hR', mul_nonsing_inv_cancel_right _ _ hS']
  rw [← this, h1]; simp

theorem bergman_moeb {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) {z : Pt ι p q} (hz : z ∈ DomI ι p q)
    (ξ η : Pt ι p q) :
    bergman (moebI g z) (fun τ => tanAct (g τ) (z τ) (ξ τ)) (fun τ => tanAct (g τ) (z τ) (η τ)) =
      bergman z ξ η := by
  rw [bergman_apply, bergman_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hu : g τ ∈ Upq p q := hg τ (Set.mem_univ _)
  rw [← hP_inv_moeb hu (hz τ), ← hQ_moeb hu (hz τ), Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [tanAct, conjTranspose_mul, Matrix.mul_assoc, conjTranspose_nonsing_inv, moebI]
  rw [trace_mul_comm (jW (g τ) (z τ))ᴴ]
  simp only [Matrix.mul_assoc]

def invariantData {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (hΓ : Γ ≤ UpqI ι p q) (c : ι → ℝ) (hc : ∀ τ, 0 < c τ) :
    BdData ι p q Γ where
  m := 0
  nrm := fun i => i.elim0
  nrm_pos := fun i => i.elim0
  nrm_le := fun i => i.elim0
  nrm_smooth := fun i => i.elim0
  nrm_inv := fun i => i.elim0
  kae := bergman
  kae_herm := fun z hz ξ η => by
    rw [bergman_apply, bergman_apply, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [starRingEnd_apply, ← trace_conjTranspose]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, (hP_inv_posDef (hz τ)).isHermitian.eq,
      (show (hQ (z τ)).PosDef from hz τ).inv.isHermitian.eq, Matrix.mul_assoc]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  kae_pos := fun z hz ξ hξ => by
    obtain ⟨τ, hτ⟩ := Function.ne_iff.1 hξ
    have H := fun σ => trace_pos (hP_inv_posDef (hz σ)) (show (hQ (z σ)).PosDef from hz σ).inv (ξ σ)
    rw [bergman_apply, Complex.re_sum]
    exact Finset.sum_pos' (fun σ _ => (Complex.nonneg_iff.1 (H σ).1).1)
      ⟨τ, Finset.mem_univ _, (Complex.pos_iff.1 ((H τ).2 hτ)).1⟩
  kae_smooth := fun ξ η => by
    simp only [bergman_apply, trace, diag_apply, Matrix.mul_apply]
    exact ContDiffOn.sum fun τ _ => ContDiffOn.sum fun a _ => ContDiffOn.sum fun b _ => ContDiffOn.mul
      (ContDiffOn.sum fun k _ => ContDiffOn.mul (ContDiffOn.sum fun l _ =>
        ContDiffOn.mul (smoothOn_hP_inv τ a l) contDiffOn_const) (smoothOn_hQ_inv τ k b)) contDiffOn_const
  kae_inv := fun γ hγ z hz ξ η => bergman_moeb (hΓ hγ) hz ξ η
  cst := 1
  cst_pos := one_pos
  cst_small := fun i => i.elim0
  metW := fun z τ => (c τ : ℂ) • (hP (z τ))⁻¹
  metOm := fun z τ => (c τ : ℂ) • hQ (z τ)
  metW_pos := fun z hz τ => (hP_inv_posDef (hz τ)).smul (by exact_mod_cast hc τ)
  metOm_pos := fun z hz τ => PosDef.smul (hz τ) (by exact_mod_cast hc τ)
  metW_smooth := fun τ a b => ContDiffOn.mul contDiffOn_const (smoothOn_hP_inv τ a b)
  metOm_smooth := fun τ a b => ContDiffOn.mul contDiffOn_const (smoothOn_hQ τ a b)
  metW_inv := fun γ hγ z hz τ => by
    rw [Matrix.mul_smul, Matrix.smul_mul, moebI, hP_inv_moeb (hΓ hγ τ (Set.mem_univ _)) (hz τ)]
  metOm_inv := fun γ hγ z hz τ => by
    rw [Matrix.mul_smul, Matrix.smul_mul, moebI, hQ_moeb (hΓ hγ τ (Set.mem_univ _)) (hz τ)]

example (ξ η : Pt ι p q) : bergman 0 ξ η = ∑ τ, (ξ τ * (η τ)ᴴ).trace := by
  simp [bergman_apply, hP, hQ]

end GlobalTheory.HodgeDomain
