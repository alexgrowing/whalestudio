import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.HalfOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KcDual
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.InvContDiffOn

import PositivityTheory.Representations.BoundaryCones.ArchimedeanCones.ConeOverlaps.OpenConeCriteria.OpenConeFormulation.IsOpenConeInvariant

noncomputable section

open Matrix Finset
open scoped ContDiff ComplexOrder

namespace PositivityTheory.RgBcC.LfSt.Kchain.KcHalf2

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem real_smul_clm {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (r : ℝ) (f : V →L[ℂ] V) :
    r • f = (r : ℂ) • f := by
  ext v
  simp [Complex.coe_smul]

theorem trace_real {H : Mat n} (hH : H.IsHermitian) : ((H.trace.re : ℝ) : ℂ) = H.trace := by
  have h : star H.trace = H.trace := by
    rw [← Matrix.trace_conjTranspose, hH.eq]
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

theorem eps_sum_trace (hH : HbFacts) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V)) : ∑ p, ((hb p : Mat n).trace) • ε (hb p) = ε 1 := by
  obtain ⟨hher, -, -, -, -, -, htr, -⟩ := hH n
  have e : ∑ p, ((hb p : Mat n).trace.re) • (hb p : Mat n) = 1 := by
    rw [← htr]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← trace_real (hher p)]
    ext a b
    simp [Complex.real_smul]
  rw [← e, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, real_smul_clm, trace_real (hher p)]

theorem eps_sum_sq (hH : HbFacts) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V)) : ∑ p, ε ((hb p : Mat n) * hb p + hb p * hb p) = ((2 * n : ℕ) : ℂ) • ε 1 := by
  obtain ⟨-, -, -, -, -, hsq, -, -⟩ := hH n
  rw [← map_sum, Finset.sum_add_distrib, hsq]
  have e : (n : ℂ) • (1 : Mat n) + (n : ℂ) • 1 = ((2 * n : ℕ) : ℝ) • (1 : Mat n) := by
    ext a b
    simp [Complex.real_smul]
    ring
  rw [e, map_smul, real_smul_clm]
  norm_cast

theorem gte {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
    {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V} (h : CxData lam E Fr ε ι S Γ T) (H : Mat n) (X : E.V →L[ℂ] E.V) :
    Γ * T * (ε H * X) = -(ε H * (Γ * T * X)) := by
  rw [← mul_assoc, mul_assoc Γ, h.Tε, ← mul_assoc, h.Γε]
  simp only [neg_mul, mul_assoc]

theorem algPsi (hH : HbFacts) (hc : FrComm) {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)}
    {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)} {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}
    (h : CxData lam E Fr ε ι S Γ T) (K0 : E.V →L[ℂ] E.V) (R : Mat n → (E.V →L[ℂ] E.V)) :
    ∑ p, ((((-(2 * n : ℂ)) * (hb p : Mat n).trace) • K0 * Γ * T - R (hb p) * Γ * T -
        K0 * Γ * T * fderiv ℝ Fr 1 (hb p)) * ε (hb p)) =
      (∑ p, (R (hb p) * ε (hb p) - K0 * ε (hb p) * fderiv ℝ Fr 1 (hb p))) * Γ * T := by
  obtain ⟨hher, -⟩ := hH n
  set D0 := ∑ p, ε (hb p) * fderiv ℝ Fr 1 (hb p) with hD0
  have hTD : T * D0 = -(D0 * T) := h.TD
  have hΓdF : ∀ p, Γ * fderiv ℝ Fr 1 (hb p) = fderiv ℝ Fr 1 (hb p) * Γ := fun p =>
    (hc n lam E Fr ε ι S Γ T h (hb p) (hb p) (hher p) (hher p)).2
  have hΓD : Γ * D0 = -(D0 * Γ) := by
    rw [hD0, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← mul_assoc, h.Γε, neg_mul, mul_assoc, hΓdF p, ← mul_assoc]
  have hGTD : Γ * T * D0 = D0 * (Γ * T) := by
    rw [mul_assoc, hTD, mul_neg, ← mul_assoc, hΓD, neg_mul, neg_neg, mul_assoc]
  have hcomm : ∀ p, fderiv ℝ Fr 1 (hb p) * ε (hb p) =
      ε (hb p) * fderiv ℝ Fr 1 (hb p) - ε ((hb p : Mat n) * hb p + hb p * hb p) := fun p =>
    (hc n lam E Fr ε ι S Γ T h (hb p) (hb p) (hher p) (hher p)).1

  have hs : ∀ p, (((-(2 * n : ℂ)) * (hb p : Mat n).trace) • K0 * Γ * T - R (hb p) * Γ * T -
        K0 * Γ * T * fderiv ℝ Fr 1 (hb p)) * ε (hb p) =
      (R (hb p) * ε (hb p) - K0 * ε (hb p) * fderiv ℝ Fr 1 (hb p)) * Γ * T +
        (K0 * (ε (hb p) * fderiv ℝ Fr 1 (hb p)) * (Γ * T) - K0 * (Γ * T * (ε (hb p) * fderiv ℝ Fr 1 (hb p)))) +
        (-(K0 * ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p) * (Γ * T)) -
          K0 * ε ((hb p : Mat n) * hb p + hb p * hb p) * (Γ * T)) := by
    intro p
    have e1 : Γ * T * ε (hb p) = -(ε (hb p) * (Γ * T)) := by
      have := gte h (hb p) 1
      simpa using this
    have e2 : Γ * T * ε ((hb p : Mat n) * hb p + hb p * hb p) =
        -(ε ((hb p : Mat n) * hb p + hb p * hb p) * (Γ * T)) := by
      have := gte h ((hb p : Mat n) * hb p + hb p * hb p) 1
      simpa using this
    have lhs : (((-(2 * n : ℂ)) * (hb p : Mat n).trace) • K0 * Γ * T - R (hb p) * Γ * T -
        K0 * Γ * T * fderiv ℝ Fr 1 (hb p)) * ε (hb p) =
        ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • (K0 * (Γ * T * ε (hb p))) - R (hb p) * (Γ * T * ε (hb p)) -
          K0 * (Γ * T * (fderiv ℝ Fr 1 (hb p) * ε (hb p))) := by
      simp only [sub_mul, smul_mul_assoc, mul_assoc]
    rw [lhs, e1, hcomm p, mul_sub (Γ * T), e2]
    simp only [mul_neg, neg_mul, smul_neg, mul_sub, sub_mul, mul_assoc, mul_smul_comm, smul_mul_assoc]
    abel
  rw [Finset.sum_congr rfl fun p _ => hs p, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have z1 : ∑ p, (K0 * (ε (hb p) * fderiv ℝ Fr 1 (hb p)) * (Γ * T) -
      K0 * (Γ * T * (ε (hb p) * fderiv ℝ Fr 1 (hb p)))) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hD0,
      hGTD, mul_assoc, sub_self]
  have z2 : ∑ p, (-(K0 * ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p) * (Γ * T)) -
      K0 * ε ((hb p : Mat n) * hb p + hb p * hb p) * (Γ * T)) = 0 := by
    have s1 : ∑ p, ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p) = (-(2 * n : ℂ)) • ε 1 := by
      rw [← eps_sum_trace hH ε, Finset.smul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [mul_smul]
    have s2 := eps_sum_sq hH ε
    have : ∑ p, (-(K0 * ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p) * (Γ * T)) -
        K0 * ε ((hb p : Mat n) * hb p + hb p * hb p) * (Γ * T)) =
        -(K0 * (∑ p, ((-(2 * n : ℂ)) * (hb p : Mat n).trace) • ε (hb p)) * (Γ * T)) -
          K0 * (∑ p, ε ((hb p : Mat n) * hb p + hb p * hb p)) * (Γ * T) := by
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
        Finset.sum_mul]
    rw [this, s1, s2]
    push_cast
    simp only [mul_neg, neg_mul, neg_neg, mul_smul_comm, smul_mul_assoc, neg_smul, sub_self]
  rw [z1, z2, add_zero, add_zero, Finset.sum_mul, Finset.sum_mul]

theorem partial_snd {A B Z : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (f : A × B → Z) (a : A) (b : B) (hf : DifferentiableAt ℝ f (a, b)) (h : B) :
    fderiv ℝ f (a, b) (0, h) = fderiv ℝ (fun b' => f (a, b')) b h := by
  have := hf.hasFDerivAt.comp b (hasFDerivAt_prodMk_right a b)
  have e : (fun b' => f (a, b')) = f ∘ Prod.mk a := rfl
  rw [e, this.fderiv]
  simp

theorem hOf_single (i : Fin n × Fin n) : hOf (Pi.single i (1 : ℝ)) = (hb i : Mat n) := by
  unfold hOf
  rw [Finset.sum_eq_single i]
  · simp
  · intro p _ hp
    simp [Pi.single_apply, hp]
  · simp

theorem unit_of {y : Mat n} (hy : y ∈ GLs n) : IsUnit y.det := isUnit_iff_ne_zero.mpr hy

theorem isOpen_cone (hH : HbFacts) : IsOpen (cone n) := PositivityTheory.KcHalf2₂.isOpen_cone_of_hbFacts hH

section Main

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem frInv (h : CxData lam E Fr ε ι S Γ T) {y : Mat n} (hy : y ∈ GLs n) :
    Fr y⁻¹ * Fr y = 1 ∧ Fr y * Fr y⁻¹ = 1 := by
  constructor
  · rw [← h.mul _ (KcInv.inv_mem hy) _ hy, Matrix.nonsing_inv_mul _ (unit_of hy), h.one]
  · rw [← h.mul _ hy _ (KcInv.inv_mem hy), Matrix.mul_nonsing_inv _ (unit_of hy), h.one]

theorem frInvEps (h : CxData lam E Fr ε ι S Γ T) {y : Mat n} (hy : y ∈ GLs n) {H : Mat n} (hH : H.IsHermitian) :
    Fr y⁻¹ * ε H = ε (yᴴ * H * y) * Fr y⁻¹ := by
  have e := h.frε y hy H hH
  calc Fr y⁻¹ * ε H = Fr y⁻¹ * ε H * (Fr y * Fr y⁻¹) := by rw [(frInv h hy).2, mul_one]
    _ = Fr y⁻¹ * (ε H * Fr y) * Fr y⁻¹ := by simp only [mul_assoc]
    _ = Fr y⁻¹ * (Fr y * ε (yᴴ * H * y)) * Fr y⁻¹ := by rw [e]
    _ = ε (yᴴ * H * y) * Fr y⁻¹ := by rw [← mul_assoc (Fr y⁻¹), (frInv h hy).1, one_mul]

def Gf (Fr k : Mat n → (E.V →L[ℂ] E.V)) (Γ T : E.V →L[ℂ] E.V) (c : ℝ) (d x : Mat n) : Mat n → (E.V →L[ℂ] E.V) :=
  fun y' => wt c y' • Kf Fr k Γ T d x y'

theorem Gf_smooth (h : CxData lam E Fr ε ι S Γ T) {k : Mat n → (E.V →L[ℂ] E.V)} (hk : ContDiffOn ℝ ∞ k (GLs n))
    (c : ℝ) {d x : Mat n} (hd : d ∈ GLs n) (hx : x ∈ GLs n) : ContDiffOn ℝ ∞ (Gf Fr k Γ T c d x) (GLs n) := by
  have hW : ContDiffOn ℝ ∞ (fun y' : Mat n => wt c y') (GLs n) := by
    unfold wt
    refine contDiffOn_const.mul (ContDiffOn.inv ?_ fun y hy => pow_ne_zero _ ?_)
    · exact (KcInv.det_contDiff.comp_contDiffOn (KcInv.mul_contDiffOn contDiffOn_id
        KcInv.star_contDiff.contDiffOn)).pow n
    · exact KcInv.mul_mem hy (KcInv.conjT_mem hy)
  have harg : ContDiffOn ℝ ∞ (fun y' : Mat n => x⁻¹ * d * y'ᴴ⁻¹) (GLs n) :=
    KcInv.mul_contDiffOn contDiffOn_const
      (KcInv.inv_contDiffOn.comp KcInv.star_contDiff.contDiffOn fun y hy => KcInv.conjT_mem hy)
  have hargm : ∀ y' ∈ GLs n, x⁻¹ * d * y'ᴴ⁻¹ ∈ GLs n := fun y' hy' =>
    KcInv.mul_mem (KcInv.mul_mem (KcInv.inv_mem hx) hd) (KcInv.inv_mem (KcInv.conjT_mem hy'))
  have hK : ContDiffOn ℝ ∞ (fun y' => Kf Fr k Γ T d x y') (GLs n) := by
    unfold Kf
    exact ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul contDiffOn_const (hk.comp harg hargm))
      contDiffOn_const) contDiffOn_const) (h.smooth.comp KcInv.inv_contDiffOn fun y hy => KcInv.inv_mem hy)
  exact hW.smul hK

theorem Gf_inv (h : CxData lam E Fr ε ι S Γ T) {k : Mat n → (E.V →L[ℂ] E.V)}
    (hkK : ∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂)
    (c : ℝ) {d x : Mat n} (hd : d ∈ GLs n) (hx : x ∈ GLs n) :
    ∀ y ∈ GLs n, ∀ u : Matrix.unitaryGroup (Fin n) ℂ, Gf Fr k Γ T c d x (y * u.1) = Gf Fr k Γ T c d x y := by
  intro y hy u
  have hu1 : u.1 * star u.1 = 1 := (Matrix.mem_unitaryGroup_iff.mp u.2)
  have hu2 : star u.1 * u.1 = 1 := (Matrix.mem_unitaryGroup_iff'.mp u.2)
  have hsu : star u.1 = u.1ᴴ := rfl
  have huG : u.1 ∈ GLs n := by
    show u.1.det ≠ 0
    intro h0
    have := congrArg Matrix.det hu2
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hsuG : star u.1 ∈ GLs n := by rw [hsu]; exact KcInv.conjT_mem huG
  have e1 : (y * u.1) * (y * u.1)ᴴ = y * yᴴ := by
    rw [Matrix.conjTranspose_mul, ← hsu, Matrix.mul_assoc, ← Matrix.mul_assoc u.1, hu1, Matrix.one_mul]
  have e2 : (y * u.1)ᴴ⁻¹ = yᴴ⁻¹ * u.1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_inv_rev, ← hsu, Matrix.inv_eq_left_inv hu1]
  have e3 : (y * u.1)⁻¹ = star u.1 * y⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hu2]
  have hw : x⁻¹ * d * yᴴ⁻¹ ∈ GLs n :=
    KcInv.mul_mem (KcInv.mul_mem (KcInv.inv_mem hx) hd) (KcInv.inv_mem (KcInv.conjT_mem hy))
  have ek : k (x⁻¹ * d * (y * u.1)ᴴ⁻¹) = k (x⁻¹ * d * yᴴ⁻¹) * E.ρ u := by
    have := hkK _ hw 1 u
    rw [Submonoid.coe_one, Matrix.one_mul, map_one, one_mul] at this
    rw [e2, ← Matrix.mul_assoc, this]
  have ef : Fr (y * u.1)⁻¹ = E.ρ u⁻¹ * Fr y⁻¹ := by
    rw [e3, h.mul _ hsuG _ (KcInv.inv_mem hy)]
    congr 1
    rw [← h.onK]
    congr 1
  have hρΓ : E.ρ u * Γ = Γ * E.ρ u := by rw [← h.onK]; exact (h.ΓFr _ huG).symm
  have hρT : E.ρ u * T = T * E.ρ u := (h.TK u).symm
  have hρρ : E.ρ u * E.ρ u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  unfold Gf wt Kf
  rw [e1, ek, ef]
  congr 1
  calc Fr x * (k (x⁻¹ * d * yᴴ⁻¹) * E.ρ u) * Γ * T * (E.ρ u⁻¹ * Fr y⁻¹)
      = Fr x * k (x⁻¹ * d * yᴴ⁻¹) * (E.ρ u * Γ) * T * (E.ρ u⁻¹ * Fr y⁻¹) := by simp only [mul_assoc]
    _ = Fr x * k (x⁻¹ * d * yᴴ⁻¹) * Γ * (E.ρ u * T) * (E.ρ u⁻¹ * Fr y⁻¹) := by rw [hρΓ]; simp only [mul_assoc]
    _ = Fr x * k (x⁻¹ * d * yᴴ⁻¹) * Γ * T * ((E.ρ u * E.ρ u⁻¹) * Fr y⁻¹) := by rw [hρT]; simp only [mul_assoc]
    _ = Fr x * k (x⁻¹ * d * yᴴ⁻¹) * Γ * T * Fr y⁻¹ := by rw [hρρ, one_mul]

end Main

def psiL {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (K0 : V →L[ℂ] V) (Dk DF : Mat n →L[ℝ] (V →L[ℂ] V))
    (w0 : Mat n) (Γ T : V →L[ℂ] V) : Mat n →ₗ[ℝ] (V →L[ℂ] V) where
  toFun X := ((-(2 * n : ℂ)) * X.trace) • K0 * Γ * T - Dk (w0 * X) * Γ * T - K0 * Γ * T * DF X
  map_add' X Y := by
    simp only [Matrix.trace_add, mul_add, add_smul, add_mul, Matrix.mul_add, map_add]
    abel
  map_smul' r X := by
    simp only [Matrix.trace_smul, Matrix.mul_smul, map_smul, RingHom.id_apply]
    rw [real_smul_clm r (Dk (w0 * X)), real_smul_clm r (DF X), real_smul_clm r]
    have e : ((-(2 * n : ℂ)) * (r • X.trace)) = (r : ℂ) * ((-(2 * n : ℂ)) * X.trace) := by
      rw [Complex.real_smul]; ring
    rw [e, mul_smul]
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub]

theorem conjT_inv_inv {y : Mat n} : (yᴴ⁻¹)ᴴ = y⁻¹ := by
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose]

theorem halfTwo_of (hH : HbFacts) (hF : FrameDer) (hc : FrComm) (h2 : DerTwo) (hD : DualSum) : HalfTwo := by
  intro n lam E Fr ε ι S Γ T h σ hσs hσ k hk hkK d hd c v hv w hw
  obtain ⟨hher, horth, -, hcoV, -, -, -, -⟩ := hH n
  have hgl := KcInv.coneGL n σ hσ
  have hx : σ v ∈ GLs n := (hgl v hv).1
  have hy : σ w ∈ GLs n := (hgl w hw).1
  have hyu : IsUnit (σ w).det := unit_of hy
  have hyHu : IsUnit (σ w)ᴴ.det := unit_of (KcInv.conjT_mem hy)
  have hKs := KcInv.kcSmooth n E.V σ c Fr k Γ T d hd hσs hσ h.smooth hk
  have hop : IsOpen (cone n) := isOpen_cone hH
  have hmem : (v, w) ∈ cone n ×ˢ cone n := ⟨hv, hw⟩
  have hnh : cone n ×ˢ cone n ∈ nhds (v, w) := (hop.prod hop).mem_nhds hmem
  have hca : ContDiffAt ℝ ∞ (Kc σ c Fr k Γ T d) (v, w) := hKs.contDiffAt hnh
  have hdiff : DifferentiableAt ℝ (Kc σ c Fr k Γ T d) (v, w) := hca.differentiableAt (by norm_num)
  set Ψ := psiL (k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹)) (fderiv ℝ k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹)) (fderiv ℝ Fr 1)
    ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) Γ T with hΨ
  set A : Fin n × Fin n → Mat n := fun i => (σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹ with hA
  set A' : Fin n × Fin n → Mat n := fun i => (σ w)ᴴ * hb i * σ w with hA'
  have hAh : ∀ i, (A i).IsHermitian := fun i => by
    show ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹)ᴴ = (σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, conjT_inv_inv, (hher i).eq,
      Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
  have hA'h : ∀ i, (A' i).IsHermitian := fun i => by
    show ((σ w)ᴴ * hb i * σ w)ᴴ = (σ w)ᴴ * hb i * σ w
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, (hher i).eq,
      Matrix.mul_assoc]
  have htr : ∀ i j, (A i * A' j).trace = if i = j then 1 else 0 := fun i j => by
    show ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹ * ((σ w)ᴴ * hb j * σ w)).trace = _
    have e : (σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹ * ((σ w)ᴴ * hb j * σ w) = (σ w)⁻¹ * (hb i * hb j * σ w) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((σ w)ᴴ⁻¹), Matrix.nonsing_inv_mul _ hyHu, Matrix.one_mul]
    rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hyu, Matrix.mul_one, horth]
  have hpart : ∀ i, fderiv ℝ (Kc σ c Fr k Γ T d) (v, w) (0, Pi.single i 1) =
      wt c (σ w) • (Fr (σ v) * Ψ ((1 / 2 : ℝ) • A i) * Fr (σ w)⁻¹) := by
    intro i
    rw [partial_snd _ v w hdiff]
    have heq : (fun w' => Kc σ c Fr k Γ T d (v, w')) =ᶠ[nhds w] fun w' => Gf Fr k Γ T c d (σ v) (σ w') := by
      filter_upwards [hop.mem_nhds hw] with w' hw'
      simp only [Kc, Gf, wt]
      rw [hσ w' hw']
    rw [heq.fderiv_eq]
    have hXh : ((1 / 2 : ℝ) • A i).IsHermitian := by
      show ((1 / 2 : ℝ) • A i)ᴴ = (1 / 2 : ℝ) • A i
      rw [Matrix.conjTranspose_smul, (hAh i).eq]
      simp
    have hdir : coords ((2 : ℂ) • (σ w * ((1 / 2 : ℝ) • A i) * (σ w)ᴴ)) = Pi.single i 1 := by
      have e : (2 : ℂ) • (σ w * ((1 / 2 : ℝ) • A i) * (σ w)ᴴ) = hb i := by
        show (2 : ℂ) • (σ w * ((1 / 2 : ℝ) • ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹)) * (σ w)ᴴ) = hb i
        rw [Matrix.mul_smul, Matrix.smul_mul]
        have e2 : σ w * ((σ w)⁻¹ * hb i * (σ w)ᴴ⁻¹) * (σ w)ᴴ = hb i := by
          simp only [Matrix.mul_assoc]
          rw [Matrix.nonsing_inv_mul _ hyHu, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hyu,
            Matrix.one_mul]
        rw [e2]
        ext a b
        simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
        push_cast
        ring
      rw [e, ← hOf_single, hcoV]
    have hFD := hF n (E.V →L[ℂ] E.V) σ (Gf Fr k Γ T c d (σ v)) hσs hσ (Gf_smooth h hk c hd hx)
      (Gf_inv h hkK c hd hx) w hw (σ w) hy (hσ w hw) _ hXh
    rw [hdir] at hFD
    rw [hFD]
    exact h2 n lam E Fr ε ι S Γ T h k hk c d (σ v) hd hx (σ w) hy _ hXh
  have hsum : ∑ i, fderiv ℝ (Kc σ c Fr k Γ T d) (v, w) (0, Pi.single i 1) * ε (hb i) =
      wt c (σ w) • (Fr (σ v) * ((1 / 2 : ℂ) • ∑ i, Ψ (A i) * ε (A' i)) * Fr (σ w)⁻¹) := by
    rw [Finset.smul_sum, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpart i, map_smul, real_smul_clm, smul_mul_assoc]
    congr 1
    rw [mul_assoc (Fr (σ v) * _) (Fr (σ w)⁻¹), frInvEps h hy (hher i), ← mul_assoc, mul_assoc (Fr (σ v)),
      smul_mul_assoc]
    have hc2 : (((1 / 2 : ℝ)) : ℂ) = (1 / 2 : ℂ) := by norm_num
    rw [hc2]
  rw [hsum, hD n E.V Ψ ε A A' hAh hA'h htr]
  have halg := algPsi hH hc h (k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹)) (fun X => Rd X k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹))
  have e : ∑ p, Ψ (hb p) * ε (hb p) =
      (∑ p, (Rd (hb p) k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * ε (hb p) -
        k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * ε (hb p) * fderiv ℝ Fr 1 (hb p))) * Γ * T := halg
  rw [e]
  have hwt : wt c (σ w) = (c : ℂ) * ((hOf w).det ^ n)⁻¹ := by simp only [wt]; rw [hσ w hw]
  rw [hwt]
  simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]

end PositivityTheory.RgBcC.LfSt.Kchain.KcHalf2
