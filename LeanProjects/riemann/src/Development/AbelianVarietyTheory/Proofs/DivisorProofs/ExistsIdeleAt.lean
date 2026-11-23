import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumCharacter

theorem exists_factor {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : P * P = P) :
    ∃ (p : ℕ) (U : Matrix (Fin m) (Fin p) ℂ) (V : Matrix (Fin p) (Fin m) ℂ), U * V = P ∧ V * U = 1 := by
  let L := Matrix.toLin' P
  let b := Module.finBasis ℂ (LinearMap.range L)
  let e := Pi.basisFun ℂ (Fin m)
  refine ⟨_, LinearMap.toMatrix b e (LinearMap.range L).subtype, LinearMap.toMatrix e b L.rangeRestrict, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp, LinearMap.subtype_comp_codRestrict, LinearMap.toMatrix_eq_toMatrix']
    exact LinearMap.toMatrix'_toLin' P
  · rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id b]
    congr 1
    ext ⟨_, y, rfl⟩ : 1
    apply Subtype.ext
    show L (L y) = L y
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hP]

theorem det_idem_kron {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : P * P = P) :
    ∃ p : ℕ, P.trace = p ∧ ∀ a : Matrix (Fin n) (Fin n) ℂ,
      (P ⊗ₖ a + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)).det = a.det ^ p := by
  obtain ⟨p, U, V, h1, h2⟩ := exists_factor P hP
  refine ⟨p, by rw [← h1, Matrix.trace_mul_comm, h2]; simp, fun a => ?_⟩
  have e : P ⊗ₖ a + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) =
      1 + (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * (V ⊗ₖ (a - 1)) := by
    rw [← Matrix.mul_kronecker_mul, h1, Matrix.one_mul, ← Matrix.one_kronecker_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply]
    ring
  have e2 : 1 + (V ⊗ₖ (a - 1)) * (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) = (1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ a := by
    rw [← Matrix.mul_kronecker_mul, h2, Matrix.mul_one, ← Matrix.one_kronecker_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply]
    ring
  rw [e, Matrix.det_one_add_mul_comm, e2, Matrix.det_kronecker]
  simp

theorem detPlus_one {m n : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) (hs : s * s = 1) :
    ∃ p : ℕ, s.trace = 2 * p - m ∧ ∀ (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ), s * b = b * s →
      GlobalTheory.WeilParts.detPlus 1 s a b = ((1 / 2 : ℂ) • (1 + s) * b + (1 / 2 : ℂ) • (1 - s)).det ^ n * a.det ^ p ∧
      b.det = ((1 / 2 : ℂ) • (1 + s) * b + (1 / 2 : ℂ) • (1 - s)).det *
        ((1 / 2 : ℂ) • (1 - s) * b + (1 / 2 : ℂ) • (1 + s)).det := by
  obtain ⟨P, hPd⟩ : ∃ P, P = (1 / 2 : ℂ) • (1 + s) := ⟨_, rfl⟩
  have hQ : (1 / 2 : ℂ) • (1 - s) = 1 - P := by rw [hPd]; module
  have hP : P * P = P := by
    rw [hPd, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, mul_add, hs, one_mul, mul_one, one_mul]; module
  obtain ⟨p, hp, hd⟩ := det_idem_kron (n := n) P hP
  refine ⟨p, ?_, fun a b hb => ?_⟩
  · rw [hPd, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at hp
    linear_combination 2 * hp
  have hc : P * b = b * P := by
    rw [hPd, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hb, one_mul, mul_one]
  have hc2 : P * b * P = P * b := by rw [mul_assoc, ← hc, ← mul_assoc, hP]
  rw [← hPd, hQ]
  constructor
  · have e1 : (1 / 2 : ℂ) • ((1 + s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ) * (b ⊗ₖ aᵀ)) +
        (1 / 2 : ℂ) • (1 - s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ) =
        (P * b) ⊗ₖ aᵀ + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← hQ, hPd, Matrix.transpose_one, add_mul, ← Matrix.mul_kronecker_mul, Matrix.smul_mul, add_mul, one_mul, one_mul,
        one_mul, ← Matrix.one_kronecker_one]
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have e2 : (P * b) ⊗ₖ aᵀ + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) =
        ((P * b + (1 - P)) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) *
          (P ⊗ₖ aᵀ + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      have f1 : (P * b + (1 - P)) * P = P * b := by rw [add_mul, hc2, sub_mul, one_mul, hP, sub_self, add_zero]
      have f2 : (P * b + (1 - P)) * (1 - P) = 1 - P := by rw [mul_sub, f1, mul_one]; abel
      rw [mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, f1, f2, one_mul, one_mul]
    unfold GlobalTheory.WeilParts.detPlus
    rw [e1, e2, Matrix.det_mul, hd, Matrix.det_kronecker]
    simp
  · rw [← Matrix.det_mul]
    congr 1
    have f3 : P * b * ((1 - P) * b) = 0 := by
      rw [← mul_assoc, mul_sub, mul_one, hc2, sub_self, zero_mul]
    have f4 : (1 - P) * ((1 - P) * b) = (1 - P) * b := by
      rw [← mul_assoc, sub_mul, mul_sub, mul_sub, hP]; simp
    have f5 : (1 - P) * P = 0 := by rw [sub_mul, hP, one_mul, sub_self]
    rw [add_mul, mul_add, mul_add, f3, f4, f5, hc2, sub_mul]; simp

variable {D : D7}

theorem hasInfExp_twist {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ (1 / 2)) (k : ℕ) : HasInfExp D (χ * (η ^ k)⁻¹) τ (a - k / 2) := by
  obtain ⟨n, hn, h0, h⟩ := hχ
  obtain ⟨n', hn', -, h'⟩ := hη
  have e : n' = 1 := by
    have : (n' : ℚ) = 1 := by rw [hn']; norm_num
    exact_mod_cast this
  subst e
  refine ⟨n - k, by push_cast; rw [hn]; ring, h0, fun θ hθ x h1 h2 => ?_⟩
  have hne : θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ) ≠ 0 := by
    have := h' θ hθ x h1 h2
    rw [zpow_one] at this
    rw [← this]; exact Circle.coe_ne_zero _
  rw [zpow_sub₀ hne, ← h θ hθ x h1 h2, zpow_natCast]
  have := h' θ hθ x h1 h2
  rw [zpow_one] at this
  rw [← this]
  simp [div_eq_mul_inv]

theorem adele_ext {θ : InfFam D} (hθ : IsInfFam θ) {x y : AE D} (h1 : finPart D x = finPart D y)
    (h2 : ∀ τ, θ τ (infPart D x) = θ τ (infPart D y)) : x = y := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  rw [← sub_eq_zero]
  exact hσ.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
    rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]

open Classical in

theorem exists_idele_at {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (w : ℂ) (hw : w ≠ 0) :
    ∃ x : (AE D)ˣ, finPart D (x : AE D) = 1 ∧ ∀ τ', θ τ' (infPart D (x : AE D)) = if τ' = τ then w else 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have key : ∀ w : ℂ, ∃ x : AE D, finPart D x = 1 ∧ ∀ τ', θ τ' (infPart D x) = if τ' = τ then w else 1 := fun w =>
    ⟨1 + σ fun τ' => (if τ' = τ then w else 1) - 1, by rw [RingHom.map_add, hσ.fin, RingHom.map_one, add_zero], fun τ' => by
      rw [RingHom.map_add, RingHom.map_add, hσ.comp, RingHom.map_one, RingHom.map_one]; ring⟩
  obtain ⟨x, hx1, hx2⟩ := key w
  obtain ⟨y, hy1, hy2⟩ := key w⁻¹
  have hxy : x * y = 1 := adele_ext hθ (by rw [RingHom.map_mul, hx1, hy1, RingHom.map_one, one_mul]) fun τ' => by
    rw [RingHom.map_mul, RingHom.map_mul, hx2, hy2, RingHom.map_one, RingHom.map_one]
    split_ifs
    · exact mul_inv_cancel₀ hw
    · exact one_mul 1
  have hyx : y * x = 1 := (mul_comm y x).trans hxy
  refine ⟨⟨x, y, hxy, hyx⟩, ?_, ?_⟩
  · rw [Units.val_mk]; exact hx1
  · rw [Units.val_mk]; exact hx2

theorem det_compAt (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} (M : Matrix (Fin k) (Fin k) (AE D)) :
    (compAt θ τ M).det = θ τ (infPart D M.det) :=
  (RingHom.map_det ((θ τ).comp (infPart D)) M).symm

theorem finPart_cA (z : AE D) (hz : finPart D z = 1) : finPart D (cA D z) = 1 := by
  have key : ∀ z : AE D, finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a x => rfl
  rw [key, hz, map_one]

theorem exists_root {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : ∀ τ, (gramAt D V τ).det ≠ 0)
    (g : GA D V) (hg : g ∈ GinfC V) :
    ∃ x, IsDetRoot V g x ∧ ∀ (ν : (AE D)ˣ →* Circle) (c : D.what₂.Tau → ℤ), (∀ τ, HasInfExp D ν τ (c τ)) →
      ((ν x : Circle) : ℂ) = ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt V g)).det ^ c τ := by
  classical
  have hu : ∀ τ, ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ = 1 := fun τ => by
    have h : (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have h2 := congrArg (fun M => ‖Matrix.det M‖) h
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at h2
    have h3 : ‖(gramAt D V τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hV τ)
    have h4 : ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ ^ 2 = 1 := by
      apply mul_left_cancel₀ h3; linear_combination h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  have hw : ∀ τ, ∃ w : ℂ, w ^ 2 = (compAt θ τ (Formalism.L2.Theta.mt V g)).det ∧ ‖w‖ = 1 := fun τ => by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (compAt θ τ (Formalism.L2.Theta.mt V g)).det two_pos
    refine ⟨w, hw, (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_⟩
    rw [← norm_pow, hw, hu]
  choose w hw1 hw2 using hw
  have hw0 : ∀ τ, w τ ≠ 0 := fun τ h => by simpa [h] using hw2 τ
  choose x hx1 hx2 using fun τ => exists_idele_at hθ τ (w τ) (hw0 τ)
  have hf : finPart D ((∏ τ, x τ : (AE D)ˣ) : AE D) = 1 := by
    rw [Units.coe_prod, map_prod]; exact Finset.prod_eq_one fun τ _ => hx1 τ
  have hi : ∀ τ, θ τ (infPart D ((∏ τ, x τ : (AE D)ˣ) : AE D)) = w τ := fun τ => by
    rw [Units.coe_prod, map_prod, map_prod]
    simp [hx2]
  refine ⟨∏ τ, x τ, ?_, fun ν c hc => ?_⟩
  · refine adele_ext hθ ?_ fun τ => ?_
    · have hd : finPart D (Formalism.L2.Theta.mt V g).det = 1 := by
        have hg' : finHom V g = 1 := hg
        have : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := congrArg Units.val hg'
        rw [RingHom.map_det]
        exact (congrArg Matrix.det this).trans Matrix.det_one
      rw [map_mul, hf]
      exact ((congrArg₂ (· * ·) hd (finPart_cA _ hf)).trans (one_mul 1)).symm
    · rw [map_mul, map_mul, hi]
      have e1 := GlobalTheory.FockCompare.comp_cA hθ τ ((∏ τ, x τ : (AE D)ˣ) : AE D)
      have e2 := det_compAt θ τ (Formalism.L2.Theta.mt V g)
      rw [hi] at e1
      refine Eq.trans ?_ (congrArg₂ (· * ·) e2 e1.symm)
      have : w τ * starRingEnd ℂ (w τ) = 1 := by rw [Complex.mul_conj', hw2]; simp
      rw [← hw1]; linear_combination (-w τ) * this
  · rw [map_prod]
    rw [show ((∏ τ, ν (x τ) : Circle) : ℂ) = ∏ τ, (ν (x τ) : ℂ) from map_prod Circle.coeHom _ _]
    refine Finset.prod_congr rfl fun τ _ => ?_
    obtain ⟨n, hn, -, h⟩ := hc τ
    have e : n = 2 * c τ := by exact_mod_cast hn
    rw [h θ hθ (x τ) (hx1 τ) (fun τ' h' => by rw [hx2, if_neg h']), hx2, if_pos rfl, hw2, e, ← hw1, _root_.zpow_mul]
    simp

end GlobalTheory.VacuumCharacter

end
