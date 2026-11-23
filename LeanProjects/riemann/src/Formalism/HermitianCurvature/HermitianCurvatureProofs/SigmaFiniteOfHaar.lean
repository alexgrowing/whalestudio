import Formalism.HermitianCurvature.HermitianCurvatureProofs.Imports
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RightSingleRule.PatEntryZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermVectorIdentity

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section psi

variable {k r : ℕ}

theorem psi_mul_nset (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : ℂ) {g h : B.Mat k r}
    (hg : g ∈ QuantumDeterminants.Nset k r) (hh : h ∈ QuantumDeterminants.Nset k r) : psi k r z c (g * h) = psi k r z c g * psi k r z c h := by
  unfold psi
  rw [Formalism.QuantumDeterminants.length_additive_holds k r z hz g hg h hh, mul_add, Complex.add_re, Complex.ofReal_add, mul_add,
    Complex.exp_add]

theorem star_psi_mul (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : B.Mat k r) :
    star (psi k r z c g) * psi k r z c g = 1 := by
  unfold psi
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have : (starRingEnd ℂ) (Complex.I * ((c * ell k r z g).re : ℂ)) + Complex.I * ((c * ell k r z g).re : ℂ) = 0 := by
    simp [Complex.conj_ofReal]
  rw [this, Complex.exp_zero]

end psi

section eq

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem sigmaFinite_of_haar {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem isUnit_det_of_UH {n : B.Mat k r} (hn : n ∈ UH (Hpk k r)) : IsUnit n.det := by
  have hH : IsUnit (Hpk k r).det := IsUnit.of_mul_eq_one (Hpk k r).det
    (by rw [← Matrix.det_mul, Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.det_one])
  have h := congrArg Matrix.det (show nᴴ * Hpk k r * n = Hpk k r from hn)
  rw [Matrix.det_mul, Matrix.det_mul] at h
  have h2 : (nᴴ.det * n.det) * (Hpk k r).det = 1 * (Hpk k r).det := by
    rw [one_mul]
    linear_combination h
  have h3 := hH.mul_right_cancel h2
  exact IsUnit.of_mul_eq_one (nᴴ.det) (by rw [mul_comm]; exact h3)

def lmulHomeo (n : B.Mat k r) (hn : IsUnit n.det) : Mt k r ≃ₜ Mt k r where
  toFun x := n * Matrix.of x
  invFun x := n⁻¹ * Matrix.of x
  left_inv x := by
    show n⁻¹ * (n * Matrix.of x) = x
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hn, Matrix.one_mul]; rfl
  right_inv x := by
    show n * (n⁻¹ * Matrix.of x) = x
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hn, Matrix.one_mul]; rfl
  continuous_toFun := by
    show Continuous fun x : Mt k r => n * Matrix.of x
    exact Continuous.matrix_mul continuous_const continuous_id
  continuous_invFun := by
    show Continuous fun x : Mt k r => n⁻¹ * Matrix.of x
    exact Continuous.matrix_mul continuous_const continuous_id

theorem kr_rightEq (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x n : B.Mat k r)
    (hn : n ∈ QuantumDeterminants.Nset k r) : Kr Bs F (x * n) = psi k r Bs.z' cStd n • Kr Bs F x := by
  have hU : IsUnit n.det := isUnit_det_of_UH hn.1
  haveI := sigmaFinite_of_haar Bs.haarN
  haveI := sigmaFinite_of_haar Bs.haarW'
  set e := (lmulHomeo n hU).toMeasurableEquiv with he
  set Φ : Mt k r × Mt k r ≃ᵐ Mt k r × Mt k r := MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) e with hΦ
  have hmpN : MeasurePreserving e Bs.μN Bs.μN := by
    refine ⟨e.measurable, ?_⟩
    have := Bs.haarN.left n hn
    have ee : ⇑e = lmulM n := by funext x; rfl
    rw [ee]; exact this
  have hmp : MeasurePreserving Φ (Bs.μW'.prod Bs.μN) (Bs.μW'.prod Bs.μN) :=
    (MeasurePreserving.id Bs.μW').prod hmpN

  have h1 : Kr Bs F x = ∫ p : Mt k r × Mt k r, star (psi k r Bs.z' cStd (Matrix.of (Φ p).2)) •
      (F (x * Matrix.of (Φ p).2 * Matrix.of (Φ p).1)).comp (Bs.π' (Matrix.of (Φ p).1)⁻¹) ∂(Bs.μW'.prod Bs.μN) := by
    unfold Kr
    exact (hmp.integral_comp' (fun p : Mt k r × Mt k r => star (psi k r Bs.z' cStd (Matrix.of p.2)) •
      (F (x * Matrix.of p.2 * Matrix.of p.1)).comp (Bs.π' (Matrix.of p.1)⁻¹))).symm

  have hae : ∀ᵐ p ∂(Bs.μW'.prod Bs.μN), p.2 ∈ QuantumDeterminants.Nset k r := by
    have h0 : Bs.μN (QuantumDeterminants.Nset k r)ᶜ = 0 := Bs.haarN.conc
    have : (Bs.μW'.prod Bs.μN) ((Set.univ : Set (Mt k r)) ×ˢ ((QuantumDeterminants.Nset k r)ᶜ : Set (Mt k r))) = 0 := by
      rw [Measure.prod_prod, h0, mul_zero]
    rw [ae_iff]
    refine measure_mono_null (fun p hp => ?_) this
    exact ⟨Set.mem_univ _, hp⟩
  have h2 : Kr Bs F x = star (psi k r Bs.z' cStd n) • Kr Bs F (x * n) := by
    rw [h1]
    unfold Kr
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    have hm : psi k r Bs.z' cStd (Matrix.of (Φ p).2) = psi k r Bs.z' cStd n * psi k r Bs.z' cStd (Matrix.of p.2) :=
      psi_mul_nset Bs.z' Bs.z'_mem cStd hn hp
    have hx : x * Matrix.of (Φ p).2 * Matrix.of (Φ p).1 = x * n * Matrix.of p.2 * Matrix.of p.1 := by
      show x * (n * Matrix.of p.2) * Matrix.of p.1 = _
      rw [Matrix.mul_assoc x n]
    have h1' : Matrix.of (Φ p).1 = Matrix.of p.1 := rfl
    rw [hm, hx, h1', star_mul, smul_smul, mul_comm (star (psi k r Bs.z' cStd (Matrix.of p.2)))]
  rw [h2, smul_smul, mul_comm (psi k r Bs.z' cStd n), star_psi_mul, one_smul]

end eq

section rule

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

open Formalism.FourierDecayAlt.Q.QRR in

theorem rdV_kr (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x : B.Mat k r) (l : Fin r)
    (X : B.Mat k r) (hX : Pat k r l X) (hS : dag k r X = -X) :
    RdV X (Kr Bs F) x = (ell k r Bs.z' X - star (ell k r Bs.z' X)) • Kr Bs F x := by
  unfold RdV
  have hfun : (fun t : ℝ => Kr Bs F (x * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => psi k r Bs.z' cStd (NormedSpace.exp ((t : ℂ) • X)) • Kr Bs F x := by
    funext t
    apply kr_rightEq
    apply (exp_mem_nlev (pat_smul _ hX) _).1
    rw [dag_smul, hS, Complex.star_def, Complex.conj_ofReal, smul_neg]
  rw [hfun]
  exact ((hasDerivAt_psi Bs.z' Bs.z'_mem X).smul_const (Kr Bs F x)).deriv

theorem dEll_eq_ell (z' : Fin (2 * r + k + 1) → ℂ) (X : B.Mat k r) (hr : 1 ≤ r) :
    C3.dEll k r z' X hr = ell k r z' X := by
  unfold C3.dEll ell
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨r - 1, by omega⟩ : Fin r)),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨r - 1, by omega⟩ : Fin r))]
  rw [dif_neg (by simp; omega), dif_neg (by simp; omega), add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ≠ ⟨r - 1, by omega⟩ := Finset.ne_of_mem_erase ha
  have : a.val + 1 < r := by
    have := a.isLt
    have : a.val ≠ r - 1 := fun e => ha' (Fin.ext e)
    omega
  rw [dif_pos this, dif_pos this]

open Formalism.FourierDecayAlt.Q.QRR in
theorem pat_inNp {l : Fin r} {X : B.Mat k r} (hX : Pat k r l X) : ∀ a b, ¬ C3.InNp k r a b → X a b = 0 := by
  intro a b hab
  by_contra hne
  apply hab
  have hl := l.isLt
  rcases hX a b hne with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨by omega, fun h => ?_⟩; omega
  · refine ⟨by omega, fun h => ?_⟩; omega

open Formalism.FourierDecayAlt.Q.QRR in
theorem exists_pat (p q : Fin (2 * r + k + 1)) (h : C3.InNp k r p q) :
    ∃ l : Fin r, Pat k r l (Matrix.single p q (1 : ℂ)) := by
  obtain ⟨hpq, hW⟩ := h
  have hq := q.isLt
  by_cases hp : p.val < r
  · by_cases hq2 : q.val ≤ 2 * r + k - p.val
    · exact ⟨⟨p.val, hp⟩, pat_single _ p q 1 (Or.inl ⟨rfl, hpq, hq2⟩)⟩
    · refine ⟨⟨2 * r + k - q.val, by omega⟩, pat_single _ p q 1 (Or.inr ⟨by simp; omega, by simp; omega, by simp; omega⟩)⟩
  · have hq3 : r + k < q.val := by
      by_contra hc
      exact hW ⟨by omega, by omega, by omega, by omega⟩
    refine ⟨⟨2 * r + k - q.val, by omega⟩, pat_single _ p q 1 (Or.inr ⟨by simp; omega, by simp; omega, by simp; omega⟩)⟩

theorem kr_rule (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x : B.Mat k r)
    (p q : Fin (2 * r + k + 1)) (hpq : C3.InNp k r p q) :
    EabH (Hpk k r) p q (Kr Bs F) x = C3.dpsiP k r Bs.z' p q • Kr Bs F x := by
  obtain ⟨l, hl⟩ := exists_pat p q hpq
  have hr : 1 ≤ r := by have := l.isLt; omega
  set Z : B.Mat k r := Matrix.single p q (1 : ℂ) with hZ
  have h1 := rdV_kr Bs F x l _ (Formalism.FourierDecayAlt.Q.QRR.pat_hpart1 hl) (Formalism.FourierDecayAlt.Q.QRR.skew_hpart1 Z)
  have h2 := rdV_kr Bs F x l _ (Formalism.FourierDecayAlt.Q.QRR.pat_hpart2 hl) (Formalism.FourierDecayAlt.Q.QRR.skew_hpart2 Z)

  set Λ : B.Mat k r → ℂ := fun X => ∑ a, ∑ b, X a b * C3.dpsiP k r Bs.z' a b with hΛ
  have hΛ1 : ell k r Bs.z' (hpart1 (Hpk k r) Z) - star (ell k r Bs.z' (hpart1 (Hpk k r) Z)) = Λ (hpart1 (Hpk k r) Z) := by
    rw [← dEll_eq_ell _ _ hr]
    exact (Formalism.FourierDecayAlt.P.dpsi_is_derivation k r Bs.z' _ hr Bs.z'_mem (Formalism.FourierDecayAlt.P.PBG.hermitian_part_one_mem_lie Z)
      (pat_inNp (Formalism.FourierDecayAlt.Q.QRR.pat_hpart1 hl))).symm
  have hΛ2 : ell k r Bs.z' (hpart2 (Hpk k r) Z) - star (ell k r Bs.z' (hpart2 (Hpk k r) Z)) = Λ (hpart2 (Hpk k r) Z) := by
    rw [← dEll_eq_ell _ _ hr]
    exact (Formalism.FourierDecayAlt.P.dpsi_is_derivation k r Bs.z' _ hr Bs.z'_mem (Formalism.FourierDecayAlt.P.PBG.hermitian_part_two_mem_lie Z)
      (pat_inNp (Formalism.FourierDecayAlt.Q.QRR.pat_hpart2 hl))).symm
  have hsum : hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z = Z := by
    unfold hpart1 hpart2
    rw [smul_smul]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
    rw [this, ← smul_add]
    rw [show Z - (Hpk k r)⁻¹ * Zᴴ * Hpk k r + (Z + (Hpk k r)⁻¹ * Zᴴ * Hpk k r) = (2 : ℂ) • Z by
      rw [two_smul]; abel]
    rw [smul_smul]; norm_num
  have hΛZ : Λ (hpart1 (Hpk k r) Z) + Complex.I * Λ (hpart2 (Hpk k r) Z) = C3.dpsiP k r Bs.z' p q := by
    have hlin : Λ (hpart1 (Hpk k r) Z) + Complex.I * Λ (hpart2 (Hpk k r) Z) =
        Λ (hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z) := by
      simp only [hΛ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, mul_assoc]
    rw [hlin, hsum]
    simp only [hΛ, hZ, Matrix.single_apply]
    rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
    · intro a _ ha; apply Finset.sum_eq_zero; intro b _; simp [Ne.symm ha]
    · simp
  unfold EabH
  rw [h1, h2, hΛ1, hΛ2, smul_smul, ← add_smul, hΛZ]

end rule

section ring

open Classical Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def KrW (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (U₀ : Set (B.Mat k r)) (hU₀ : IsOpen U₀)
    (hK : ∀ g ∈ U₀, g ∈ B.GV k r → Loc (⊤ : ℕ∞) (Kr Bs F) g) : Wsm (E := Wq →L[ℂ] Wp) U₀ :=
  ⟨fun g => if g ∈ U₀ ∧ g ∈ B.GV k r then Kr Bs F g else 0, fun g hg hgG =>
    loc_of_eq (hK g hg hgG) hU₀ hg (fun x hx hxG => by simp [hx, hxG])⟩

def LaK (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (U₀ : Set (B.Mat k r)) (hU₀ : IsOpen U₀)
    (hK : ∀ g ∈ U₀, g ∈ B.GV k r → Loc (⊤ : ℕ∞) (Kr Bs F) g) (x₀ : B.Mat k r) :
    Module.End ℂ (Wsm (E := Wq →L[ℂ] Wp) U₀) →ₗ[ℂ] (Wq →L[ℂ] Wp) where
  toFun X := (X (KrW Bs F U₀ hU₀ hK)).1 x₀
  map_add' X Y := rfl
  map_smul' c X := rfl

end ring

end Formalism.FourierDecayAlt.P.PBG
