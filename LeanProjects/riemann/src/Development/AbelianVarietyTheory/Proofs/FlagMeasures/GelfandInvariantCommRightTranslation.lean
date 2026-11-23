import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceTransposePow

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section
namespace GlobalTheory.Dec.GelfAd

variable {n : ℕ}

private lemma conj_apply_lemma {A : Type} [Ring A] [Algebra ℂ A] (P Q : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) A) (a b : Fin n) :
    (P.map (algebraMap ℂ A) * X * Q.map (algebraMap ℂ A)) a b = ∑ c, ∑ d, (P a c * Q d b) • X c d := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Algebra.smul_def, map_mul, mul_assoc, ← Algebra.commutes (Q d b) (X c d), ← mul_assoc]

private lemma sum_diag_conj_eq_sum_diag {A : Type} [Ring A] [Algebra ℂ A] (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (X : Matrix (Fin n) (Fin n) A) :
    ∑ a, (P.map (algebraMap ℂ A) * X * Q.map (algebraMap ℂ A)) a a = ∑ a, X a a := by
  simp only [conj_apply_lemma]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have hd : ∀ d, ∑ a, P a c * Q d a = (1 : Matrix (Fin n) (Fin n) ℂ) d c := fun d => by
    rw [← hQP, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  simp [hd, Matrix.one_apply]

private lemma conj_pow_of_mul_eq_one' {A : Type} [Ring A] [Algebra ℂ A] (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (X : Matrix (Fin n) (Fin n) A) (m : ℕ) :
    (P.map (algebraMap ℂ A) * X * Q.map (algebraMap ℂ A)) ^ m =
      P.map (algebraMap ℂ A) * X ^ m * Q.map (algebraMap ℂ A) := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have h1 : Q.map (algebraMap ℂ A) * P.map (algebraMap ℂ A) = 1 := by
    rw [← Matrix.map_mul, hQP]
    simp
  have h2 : P.map (algebraMap ℂ A) * Q.map (algebraMap ℂ A) = 1 := by
    rw [← Matrix.map_mul, hPQ]
    simp
  induction m with
  | zero => rw [pow_zero, pow_zero, mul_one, h2]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc (Q.map (algebraMap ℂ A)) (P.map (algebraMap ℂ A)), h1, one_mul]

private lemma pow_apply_mul_eq_mul_pow_apply {A : Type} [Ring A] (M N : Matrix (Fin n) (Fin n) A) (R : A)
    (h : ∀ a b, M a b * R = R * N a b) (m : ℕ) :
    ∀ a b, (M ^ m) a b * R = R * (N ^ m) a b := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  | succ m ih =>
    intro a b
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_assoc, h c b, ← mul_assoc ((M ^ m) a c), ih a c, mul_assoc]

lemma trace_pow_comm {A : Type} [Ring A] [Algebra ℂ A] (E : Fin n → Fin n → A) (R : A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (h : ∀ a b, E a b * R = R * ∑ c, ∑ d, (P a c * Q d b) • E c d) (m : ℕ) :
    (∑ c, (Matrix.of E ^ m) c c) * R = R * ∑ c, (Matrix.of E ^ m) c c := by
  have hN : ∀ a b, Matrix.of E a b * R =
      R * (P.map (algebraMap ℂ A) * Matrix.of E * Q.map (algebraMap ℂ A)) a b := by
    intro a b
    rw [conj_apply_lemma]
    exact h a b
  calc (∑ c, (Matrix.of E ^ m) c c) * R
      = ∑ c, R * ((P.map (algebraMap ℂ A) * Matrix.of E * Q.map (algebraMap ℂ A)) ^ m) c c := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => pow_apply_mul_eq_mul_pow_apply _ _ R hN m c c
    _ = R * ∑ c, (Matrix.of E ^ m) c c := by
        rw [← Finset.mul_sum, conj_pow_of_mul_eq_one' P Q hQP, sum_diag_conj_eq_sum_diag P Q hQP]

lemma inv_mul_of_UJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) :
    Jm ε * kᴴ * Jm ε * k = 1 := by
  unfold inUJ at hk
  rw [Matrix.mul_assoc (Jm ε * kᴴ), Matrix.mul_assoc (Jm ε), ← Matrix.mul_assoc kᴴ, hk,
    Formalism.REAL.Jm_mul_self]

lemma Rd_right (X k g : Matrix (Fin n) (Fin n) ℂ) (hk : IsUnit k) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Rd X (fun x => f (x * k)) g = Rd (k⁻¹ * X * k) f (g * k) := by
  have hd : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det k).mp hk
  simp only [Rd]
  congr 1
  funext t
  congr 1
  rw [show ((t : ℂ) • (k⁻¹ * X * k)) = k⁻¹ * ((t : ℂ) • X) * k by
    rw [Matrix.mul_smul, Matrix.smul_mul], Matrix.exp_conj' k _ hk]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc g k k⁻¹, Matrix.mul_nonsing_inv k hd, Matrix.mul_one]

private lemma isUnit_of_inUJ_flag_measures {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) :
    IsUnit k :=
  (Matrix.isUnit_iff_isUnit_det k).mpr (Matrix.isUnit_det_of_left_inverse (inv_mul_of_UJ hk))

private lemma Jm_conjTranspose_conj_of_inUJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (k⁻¹ * Z * k)ᴴ * Jm ε = k⁻¹ * (Jm ε * Zᴴ * Jm ε) * k := by
  have hinv : k⁻¹ = Jm ε * kᴴ * Jm ε := Matrix.inv_eq_left_inv (inv_mul_of_UJ hk)
  have hL : Jm ε * kᴴ = k⁻¹ * Jm ε := by
    rw [hinv]
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
  have hR : (k⁻¹)ᴴ * Jm ε = Jm ε * k := by
    rw [hinv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [hR, ← Matrix.mul_assoc (Jm ε) kᴴ, hL]
  simp only [Matrix.mul_assoc]

private lemma cpart1_conj_of_inUJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z : Matrix (Fin n) (Fin n) ℂ) : cpart1 ε (k⁻¹ * Z * k) = k⁻¹ * cpart1 ε Z * k := by
  rw [cpart1, cpart1, Jm_conjTranspose_conj_of_inUJ hk, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_smul,
    Matrix.smul_mul]

private lemma cpart2_conj_of_inUJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z : Matrix (Fin n) (Fin n) ℂ) : cpart2 ε (k⁻¹ * Z * k) = k⁻¹ * cpart2 ε Z * k := by
  rw [cpart2, cpart2, Jm_conjTranspose_conj_of_inUJ hk, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.mul_smul,
    Matrix.smul_mul]

lemma Ec_right {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z g : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Ec ε Z (fun x => f (x * k)) g = Ec ε (k⁻¹ * Z * k) f (g * k) := by
  have hu := isUnit_of_inUJ_flag_measures hk
  simp only [Ec]
  rw [Rd_right _ _ _ hu f, Rd_right _ _ _ hu f, cpart1_conj_of_inUJ hk, cpart2_conj_of_inUJ hk]

private lemma inUJ_mul_flag_measures' {ε : Fin n → Bool} {g k : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (hk : inUJ ε k) : inUJ ε (g * k) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc kᴴ * gᴴ * Jm ε * (g * k) = kᴴ * (gᴴ * Jm ε * g) * k := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hk]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
lemma smooth_right {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) : SmoothOnG ε (fun x => f (x * k)) := by
  have hc : ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x * k) :=
    (LinearMap.mulRight ℝ k).toContinuousLinearMap.contDiff
  unfold SmoothOnG at hf ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hmem, hF, hfF⟩ := hf (g₀ * k) (inUJ_mul_flag_measures' hg₀ hk)
  exact ⟨(fun x => x * k) ⁻¹' U, fun x => F (x * k), hU.preimage hc.continuous, hmem,
    hF.comp hc.contDiffOn (fun _ hx => hx), fun g hg hgJ => hfF (g * k) hg (inUJ_mul_flag_measures' hgJ hk)⟩

open GlobalTheory.CapelliCentral in

def rightEnd {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) :
    Module.End ℂ (smoothSpace ε ℂ) where
  toFun F := mk (fun x => F.1 (x * k)) (smooth_right hk F.2.1)
  map_add' F F' := by
    apply ext_on
    intro g hg
    exact (mk_apply _ (smooth_right hk (F + F').2.1) hg).trans
      (congrArg₂ (· + ·) (mk_apply _ (smooth_right hk F.2.1) hg).symm
        (mk_apply _ (smooth_right hk F'.2.1) hg).symm)
  map_smul' c F := by
    apply ext_on
    intro g hg
    exact (mk_apply _ (smooth_right hk (c • F).2.1) hg).trans
      (congrArg (c • ·) (mk_apply _ (smooth_right hk F.2.1) hg).symm)

open GlobalTheory.CapelliCentral in
lemma rightEnd_apply {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (F : smoothSpace ε ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    (rightEnd hk F).1 g = F.1 (g * k) := by
  simp only [rightEnd, LinearMap.coe_mk, AddHom.coe_mk]
  exact mk_apply _ _ hg

private lemma Ec_eq_EcV (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Ec ε Z f g = EcV ε Z f g := by
  simp only [Ec, EcV, rdV_eq, smul_eq_mul]

private lemma mul_single_mul_apply' (M N : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (M * Matrix.single a b (1 : ℂ) * N : Matrix (Fin n) (Fin n) ℂ) c d = M c a * N b d := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

open GlobalTheory.CapelliCentral in
lemma eabEnd_rightEnd {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) (a b : Fin n) :
    eabEnd ε ℂ a b * rightEnd hk =
      rightEnd hk * ∑ c, ∑ d, ((k⁻¹)ᵀ a c * kᵀ d b) • eabEnd ε ℂ c d := by
  apply LinearMap.ext
  intro F
  apply ext_on
  intro g hg
  have hgk : inUJ ε (g * k) := inUJ_mul_flag_measures' hg hk
  rw [Module.End.mul_apply, Module.End.mul_apply, rightEnd_apply hk _ hg,
    eabEnd_apply (f := fun x => F.1 (x * k)) a b (rightEnd hk F) (fun x hx => rightEnd_apply hk F hx) hg,
    eabV_eq, Eab, Ec_right hk _ g F.1, Ec_eq_EcV, ecSumV n ε ℂ F.1 _ (g * k) F.2.1 hgk]
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul, Pi.smul_apply, eabEnd_apply (f := F.1) _ _ F (fun _ _ => rfl) hgk,
    mul_single_mul_apply', Matrix.transpose_apply]

theorem gelf_right : ∀ (n : ℕ) (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (k g : Matrix (Fin n) (Fin n) ℂ), SmoothOnG ε f → k ∈ UJset ε → g ∈ UJset ε →
    gelf ε m (fun x => f (x * k)) g = gelf ε m f (g * k) := by
  intro n ε m f k g hf hk hg
  have hkU : inUJ ε k := hk
  have hgU : inUJ ε g := hg
  have hd : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det k).mp (isUnit_of_inUJ_flag_measures hkU)
  have hQP : kᵀ * (k⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul k hd, Matrix.transpose_one]
  have hfV : SmoothOnGV ε f := (smoothOnGV_iff ε f).mpr hf
  let F : GlobalTheory.CapelliCentral.smoothSpace ε ℂ := GlobalTheory.CapelliCentral.mk f hfV
  have hFf : ∀ x, inUJ ε x → F.1 x = f x := fun x hx => GlobalTheory.CapelliCentral.mk_apply f hfV hx
  have hcomm := trace_pow_comm (GlobalTheory.CapelliCentral.eabEnd ε ℂ) (rightEnd hkU) (k⁻¹)ᵀ kᵀ hQP
    (eabEnd_rightEnd hkU) (m + 1)
  have h1 := congrArg (fun T : Module.End ℂ (GlobalTheory.CapelliCentral.smoothSpace ε ℂ) => (T F).1 g) hcomm
  simp only [Module.End.mul_apply] at h1
  rw [GlobalTheory.Dec.FormF.gelf_apply (f := fun x => f (x * k)) m (rightEnd hkU F)
      (fun x hx => (rightEnd_apply hkU F hx).trans (hFf _ (inUJ_mul_flag_measures' hx hkU))) hgU,
    rightEnd_apply hkU _ hgU,
    GlobalTheory.Dec.FormF.gelf_apply m F hFf (inUJ_mul_flag_measures' hgU hkU)] at h1
  exact h1

end GlobalTheory.Dec.GelfAd
