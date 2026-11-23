import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LeviCols

theorem key {R : Type} [CommRing R] (c : R →+* R) {n m : ℕ} (J' : Matrix (Fin n) (Fin n) R)
    (J₁' : Matrix (Fin m) (Fin m) R) (Xc Yc : Matrix (Fin n) (Fin 1) R) (I : Matrix (Fin n) (Fin m) R)
    (hXX : Xcᵀ * J' * Xc.map c = 0) (hYX : Ycᵀ * J' * Xc.map c = 1) (hIX : Iᵀ * J' * Xc.map c = 0)
    (hXI : Xcᵀ * J' * I.map c = 0) (hJ1 : Iᵀ * J' * I.map c = J₁') (hdet : IsUnit J₁'.det)
    (span : ∀ z : Fin n → R, ∃ (a b : R) (w : Fin m → R), z = a • (fun i => Xc i 0) + I *ᵥ w + b • (fun i => Yc i 0))
    (Q : Matrix (Fin n) (Fin n) R) (hQ : Qᵀ * J' * Q.map c = J') (a : R) (ha : IsUnit (c a))
    (hQX : Q * Xc = a • Xc) :
    ∃ G0 : Matrix (Fin m) (Fin m) R, IsUnit G0.det ∧ G0ᵀ * J₁' * G0.map c = J₁' ∧
      ∃ A : Matrix (Fin 1) (Fin m) R, Q * I = Xc * A + I * G0 := by
  have hcol : ∀ k : Fin m, ∃ (a b : R) (w : Fin m → R),
      (fun i => (Q * I) i k) = a • (fun i => Xc i 0) + I *ᵥ w + b • (fun i => Yc i 0) := fun k => span _
  choose α β ω hω using hcol
  set A : Matrix (Fin 1) (Fin m) R := Matrix.of fun _ k => α k with hA
  set Bm : Matrix (Fin 1) (Fin m) R := Matrix.of fun _ k => β k with hBm
  set G0 : Matrix (Fin m) (Fin m) R := Matrix.of fun j k => ω k j with hG0
  have hP : Q * I = Xc * A + I * G0 + Yc * Bm := by
    ext i k
    have := congrFun (hω k) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_one, hA, hBm, hG0, Matrix.of_apply, Matrix.mulVec, dotProduct]
    ring
  have hQc : Q.map c * Xc.map c = c a • Xc.map c := by
    rw [← Matrix.map_mul, hQX]; ext i j; simp
  have h1 : c a • (Qᵀ * J' * Xc.map c) = J' * Xc.map c := by
    calc c a • (Qᵀ * J' * Xc.map c) = Qᵀ * J' * (c a • Xc.map c) := by rw [Matrix.mul_smul]
      _ = Qᵀ * J' * (Q.map c * Xc.map c) := by rw [hQc]
      _ = (Qᵀ * J' * Q.map c) * Xc.map c := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQ]
  have h2 : c a • ((Q * I)ᵀ * J' * Xc.map c) = 0 := by
    have e : (Q * I)ᵀ * J' * Xc.map c = Iᵀ * (Qᵀ * J' * Xc.map c) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e, ← Matrix.mul_smul, h1, ← Matrix.mul_assoc, hIX]
  have h3 : (Q * I)ᵀ * J' * Xc.map c = 0 := by
    obtain ⟨u, hu⟩ := ha
    have := congrArg (fun M => ((u⁻¹ : Rˣ) : R) • M) h2
    simpa [smul_smul, ← hu] using this
  have h4 : (Q * I)ᵀ * J' * Xc.map c = Aᵀ * (Xcᵀ * J' * Xc.map c) + G0ᵀ * (Iᵀ * J' * Xc.map c) +
      Bmᵀ * (Ycᵀ * J' * Xc.map c) := by
    rw [hP]; simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.add_mul, Matrix.mul_assoc]
  rw [hXX, hIX, hYX, h3] at h4
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add] at h4
  have hB0 : Bm = 0 := by
    rw [← Matrix.transpose_eq_zero]; exact h4.symm
  have hP' : Q * I = Xc * A + I * G0 := by rw [hP, hB0, Matrix.mul_zero, add_zero]
  have h5 : (Q * I)ᵀ * J' * (Q * I).map c = J₁' := by
    have e : (Q * I)ᵀ * J' * (Q * I).map c = Iᵀ * (Qᵀ * J' * Q.map c) * I.map c := by
      simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    rw [e, hQ, hJ1]
  have h6 : (Q * I)ᵀ * J' * (Q * I).map c = Aᵀ * (Xcᵀ * J' * Xc.map c) * A.map c +
      Aᵀ * (Xcᵀ * J' * I.map c) * G0.map c + G0ᵀ * (Iᵀ * J' * Xc.map c) * A.map c +
      G0ᵀ * (Iᵀ * J' * I.map c) * G0.map c := by
    rw [hP']
    have hm : (Xc * A + I * G0).map c = Xc.map c * A.map c + I.map c * G0.map c := by
      rw [Matrix.map_add _ (map_add c), Matrix.map_mul, Matrix.map_mul]
    rw [hm]
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [hXX, hXI, hIX, hJ1, h5] at h6
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add] at h6
  have hU : G0ᵀ * J₁' * G0.map c = J₁' := h6.symm
  refine ⟨G0, ?_, hU, A, hP'⟩
  have hd := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hmd : (G0.map c).det = c G0.det := (RingHom.map_det c G0).symm
  rw [hmd] at hd
  obtain ⟨u, hu⟩ := hdet
  have h7 : G0.det * c G0.det = 1 := by
    have : G0.det * c G0.det * J₁'.det = 1 * J₁'.det := by linear_combination hd
    rw [← hu] at this
    exact (Units.mul_left_inj u).1 this
  exact ⟨⟨G0.det, c G0.det, h7, by rw [mul_comm]; exact h7⟩, rfl⟩

end GlobalTheory.LeviCols

namespace GlobalTheory.LeviCols

theorem form_entry {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n m l : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin m) E) (B : Matrix (Fin n) (Fin l) E) (k : Fin m) (l' : Fin l) :
    (Aᵀ * J * B.map σ) k l' = form σ J (fun i => A i k) (fun i => B i l') := by
  simp only [form, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_herm {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hσ : ∀ z, σ (σ z) = z) (hJ : ∀ i j, σ (J j i) = J i j) (u v : Fin n → E) :
    form σ J u v = σ (form σ J v u) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hJ j i]
  ring

end GlobalTheory.LeviCols

open GlobalTheory.LeviCols in
theorem GlobalTheory.LeviCols.levi_cols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n n₁ : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E),
    (∀ z, σ (σ z) = z) → (∀ i j, σ (J j i) = J i j) → form σ J x x = 0 → form σ J y y = 0 →
    form σ J x y = 1 → (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) → ιᵀ * J * ι.map σ = J₁ → J₁.det ≠ 0 →
    (∀ z : Fin n → AE F E, ∃ (a b : AE F E) (w : Fin n₁ → AE F E), z = a • incV F x + incM F ι *ᵥ w + b • incV F y) →
    ∀ (q : UA σ J) (a : (AE F E)ˣ), mat q *ᵥ incV F x = (a : AE F E) • incV F x →
      ∃ g₀ : UA σ J₁, ∀ w : Fin n₁ → AE F E, ∃ c : AE F E, mat q *ᵥ (incM F ι *ᵥ w) = incM F ι *ᵥ (mat g₀ *ᵥ w) + c • incV F x := by
  intro F E _ _ _ _ _ σ n n₁ J J₁ x y ι hσ hJ hxx _hyy hxy hι hJ1 hdet hspan q a hq
  let xc : Matrix (Fin n) (Fin 1) E := Matrix.of fun i _ => x i
  let yc : Matrix (Fin n) (Fin 1) E := Matrix.of fun i _ => y i
  have hcol : ∀ k : Fin n₁, (fun i => ι i k) = ι *ᵥ Pi.single k 1 := by
    intro k; ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have e1 : xcᵀ * J * xc.map σ = 0 := by
    ext k l; rw [form_entry]; exact hxx
  have e2 : ycᵀ * J * xc.map σ = 1 := by
    ext k l; rw [form_entry]; fin_cases k; fin_cases l
    show form σ J y x = 1
    rw [form_herm σ J hσ hJ, hxy, map_one]
  have e3 : ιᵀ * J * xc.map σ = 0 := by
    ext k l; rw [form_entry]; show form σ J (fun i => ι i k) x = 0
    rw [hcol]; exact (hι _).1
  have e4 : xcᵀ * J * ι.map σ = 0 := by
    ext k l; rw [form_entry]; show form σ J x (fun i => ι i l) = 0
    rw [form_herm σ J hσ hJ, hcol, (hι _).1, map_zero]
  have hmapc : ∀ {p r : ℕ} (M : Matrix (Fin p) (Fin r) E), (incM F M).map (cA σ) = incM F (M.map σ) := by
    intro p r M; ext i j
    simp [incM, cA, inclR, Matrix.map_apply]
  have hinc : ∀ {p r : ℕ} (A : Matrix (Fin n) (Fin p) E) (B : Matrix (Fin n) (Fin r) E),
      (incM F A)ᵀ * incM F J * (incM F B).map (cA σ) = incM F (Aᵀ * J * B.map σ) := by
    intro p r A B
    rw [hmapc]
    simp only [incM]
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  have hdetU : IsUnit (incM F J₁).det := by
    have : (incM F J₁).det = inclR (F := F) (AF F) J₁.det := (RingHom.map_det _ _).symm
    rw [this]; exact (isUnit_iff_ne_zero.mpr hdet).map _
  have hQX : mat q * incM F xc = (a : AE F E) • incM F xc := by
    ext i j; fin_cases j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, incM, incV, xc] using congrFun hq i
  obtain ⟨G0, hdu, hU, A, hP⟩ := key (cA σ).toRingHom (incM F J) (incM F J₁) (incM F xc) (incM F yc) (incM F ι)
    ((hinc xc xc).trans (by rw [e1]; exact Matrix.map_zero _ (map_zero _)))
    ((hinc yc xc).trans (by rw [e2]; exact Matrix.map_one _ (map_zero _) (map_one _)))
    ((hinc ι xc).trans (by rw [e3]; exact Matrix.map_zero _ (map_zero _)))
    ((hinc xc ι).trans (by rw [e4]; exact Matrix.map_zero _ (map_zero _)))
    ((hinc ι ι).trans (by rw [hJ1]))
    hdetU (fun z => hspan z) (mat q) q.2 (a : AE F E) ((Units.isUnit a).map _) hQX
  refine ⟨⟨Matrix.nonsingInvUnit G0 hdu, hU⟩, fun w => ⟨(A *ᵥ w) 0, ?_⟩⟩
  show mat q *ᵥ (incM F ι *ᵥ w) = incM F ι *ᵥ (G0 *ᵥ w) + (A *ᵥ w) 0 • incV F x
  have hx : ∀ v : Fin 1 → AE F E, incM F xc *ᵥ v = v 0 • incV F x := by
    intro v; ext i; simp [Matrix.mulVec, dotProduct, incM, incV, xc, mul_comm]
  rw [Matrix.mulVec_mulVec, hP, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, add_comm]
