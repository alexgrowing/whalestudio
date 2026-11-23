import Formalism.HermitianCurvature.HermitianCurvatureProofs.JDomBoundOfNnMaj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfJqSmoothOfNnMaj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LastLevelSliceOfScalar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormBallVolumes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting

open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.HeisenbergLevelMinors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def NNMinor : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (K : Set (Mat k r)), IsCompact K →
    (∀ g ∈ K, g ∈ GV k r ∧ ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0) →
    ∃ C : ℝ, ∀ g ∈ K, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ n' ∈ Formalism.QuantumDeterminants.Nset k r,
      gN n ≤ C * gN (n⁻¹ * g * n') ^ (3 * r) ∧ gN n' ≤ C * gN (n⁻¹ * g * n') ^ (3 * r)

def NNVol : Prop :=
  ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ →
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      μ {x | gN (Matrix.of x : Mat k r) ≤ R} ≤ ENNReal.ofReal (C * R ^ (((2 * r + k + 1 : ℕ) : ℝ) ^ 2))

variable {k r : ℕ}

lemma list_prod_le : ∀ (l : List ℝ) (b : ℝ), (∀ x ∈ l, 0 ≤ x ∧ x ≤ b) → 0 ≤ l.prod ∧ l.prod ≤ b ^ l.length
  | [], b, _ => by simp
  | x :: l, b, h => by
    obtain ⟨h1, h2⟩ := list_prod_le l b (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (by simp)
    rw [List.prod_cons, List.length_cons, pow_succ]
    refine ⟨mul_nonneg hx.1 h1, ?_⟩
    calc x * l.prod ≤ b * b ^ l.length := mul_le_mul hx.2 h2 h1 (le_trans hx.1 hx.2)
      _ = b ^ l.length * b := by ring

lemma norm_le_gN (M : Mat k r) : ‖M‖ ≤ gN M := by
  have hg : gN M = Real.sqrt (∑ i, ∑ j, Complex.normSq (M i j)) := rfl
  rw [hg, Matrix.norm_le_iff (Real.sqrt_nonneg _)]
  intro i j
  have h2 : ‖M i j‖ ^ 2 ≤ ∑ i, ∑ j, Complex.normSq (M i j) := by
    rw [← Complex.normSq_eq_norm_sq]
    calc Complex.normSq (M i j) ≤ ∑ j', Complex.normSq (M i j') :=
          Finset.single_le_sum (f := fun j' => Complex.normSq (M i j'))
            (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', Complex.normSq (M i' j') :=
          Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (M i' j'))
            (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  calc ‖M i j‖ = |‖M i j‖| := (abs_of_nonneg (norm_nonneg _)).symm
    _ ≤ _ := Real.abs_le_sqrt h2

lemma gN_unit {X : Mat k r} (hX : ∀ i j, ‖X i j‖ ≤ 1) : gN X ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
  have hg : gN X = Real.sqrt (∑ i, ∑ j, Complex.normSq (X i j)) := rfl
  have h1 : ∀ i j, Complex.normSq (X i j) ≤ 1 := fun i j => by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hX i j, norm_nonneg (X i j)]
  have hs : (∑ i, ∑ j, Complex.normSq (X i j)) ≤
      ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
    calc (∑ i, ∑ j, Complex.normSq (X i j))
        ≤ ∑ _i : Fin (2 * r + k + 1), ∑ _j : Fin (2 * r + k + 1), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
      _ = ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hg]
  calc Real.sqrt _ ≤ Real.sqrt (((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ)) :=
        Real.sqrt_le_sqrt hs
    _ = _ := Real.sqrt_mul_self (Nat.cast_nonneg _)

lemma gN_conjT (M : Mat k r) : gN Mᴴ = gN M := by
  show Real.sqrt _ = Real.sqrt _
  congr 1
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

private lemma gN_mul_le_hermitian_curvature (A B : Mat k r) : gN (A * B) ≤ gN A * gN B := by
  have hA : gN A = Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) := rfl
  have hB : gN B = Real.sqrt (∑ i, ∑ j, Complex.normSq (B i j)) := rfl
  have hAB : gN (A * B) = Real.sqrt (∑ i, ∑ j, Complex.normSq ((A * B) i j)) := rfl
  have hSA : 0 ≤ ∑ i, ∑ j, Complex.normSq (A i j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have entry : ∀ i j, Complex.normSq (∑ l, A i l * B l j) ≤
      (∑ l, Complex.normSq (A i l)) * (∑ l, Complex.normSq (B l j)) := by
    intro i j
    rw [Complex.normSq_eq_norm_sq]
    have h1 : ‖∑ l, A i l * B l j‖ ≤ ∑ l, ‖A i l‖ * ‖B l j‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => norm_mul _ _))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖A i l‖) (fun l => ‖B l j‖)
    have h3 : ∀ l, Complex.normSq (A i l) = ‖A i l‖ ^ 2 := fun l => Complex.normSq_eq_norm_sq _
    have h4 : ∀ l, Complex.normSq (B l j) = ‖B l j‖ ^ 2 := fun l => Complex.normSq_eq_norm_sq _
    simp only [h3, h4]
    have h5 : ‖∑ l, A i l * B l j‖ ^ 2 ≤ (∑ l, ‖A i l‖ * ‖B l j‖) ^ 2 := by
      have := norm_nonneg (∑ l, A i l * B l j)
      nlinarith
    exact h5.trans h2
  have hS : (∑ i, ∑ j, Complex.normSq ((A * B) i j)) ≤
      (∑ i, ∑ j, Complex.normSq (A i j)) * (∑ i, ∑ j, Complex.normSq (B i j)) := by
   calc (∑ i, ∑ j, Complex.normSq ((A * B) i j))
      = ∑ i, ∑ j, Complex.normSq (∑ l, A i l * B l j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          congrArg Complex.normSq Matrix.mul_apply
    _ ≤ ∑ i, ∑ j, (∑ l, Complex.normSq (A i l)) * (∑ l, Complex.normSq (B l j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => entry i j
    _ = (∑ i, ∑ l, Complex.normSq (A i l)) * (∑ j, ∑ l, Complex.normSq (B l j)) := by
        rw [Finset.sum_mul_sum]
    _ = (∑ i, ∑ j, Complex.normSq (A i j)) * (∑ i, ∑ j, Complex.normSq (B i j)) := by
        rw [Finset.sum_comm (f := fun j l => Complex.normSq (B l j))]
  rw [hA, hB, hAB]
  exact (Real.sqrt_le_sqrt hS).trans (le_of_eq (Real.sqrt_mul hSA _))

lemma gN_inv_le {g : Mat k r} (hg : g ∈ GV k r) : gN g⁻¹ ≤ gN (Hpk k r) ^ 2 * gN g := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  rw [Matrix.inv_eq_left_inv hl]
  have h0 : ∀ M : Mat k r, 0 ≤ gN M := fun M => Real.sqrt_nonneg _
  calc gN (Hpk k r * gᴴ * Hpk k r) ≤ gN (Hpk k r * gᴴ) * gN (Hpk k r) := gN_mul_le_hermitian_curvature _ _
    _ ≤ gN (Hpk k r) * gN gᴴ * gN (Hpk k r) :=
        mul_le_mul_of_nonneg_right (gN_mul_le_hermitian_curvature _ _) (h0 _)
    _ = gN (Hpk k r) ^ 2 * gN g := by rw [gN_conjT]; ring

lemma uw_bound {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ h ∈ UWset k r z, gN h ≤ C := by
  obtain ⟨C, hC⟩ := (B2x3.compactW k r z hz hT).exists_bound_of_continuousOn B6.gN_continuous.continuousOn
  refine ⟨max C 1, le_max_right _ _, fun h hh => ?_⟩
  have := hC h hh
  rw [Real.norm_eq_abs] at this
  exact le_trans (le_abs_self _) (le_trans this (le_max_left _ _))

lemma intN (hV : NNVol) {μ : Measure (Mt k r)} (hμ : IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ) {β : ℝ}
    (hβ : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < β) :
    Integrable (fun x : Mt k r => gN (Matrix.of x : Mat k r) ^ (-β)) μ := by
  obtain ⟨C, hC⟩ := hV k r μ hμ
  have hge : ∀ᵐ x ∂μ, 1 ≤ gN (Matrix.of x : Mat k r) := by
    filter_upwards [B6.haar_ae hμ] with x hx using BetaSesquilinearity.gN_ge_one (B6.Nset_sub k r hx)
  have hlin := NormBallVolumes.shellInt (Mt k r) μ (fun x => gN (Matrix.of x : Mat k r)) C _ β (NormBallVolumes.gN_meas k r) hge
    (by positivity) hC hβ
  refine ⟨((NormBallVolumes.gN_meas k r).pow_const _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => Real.rpow_nonneg (B6.gN_nonneg _) _)]
  exact hlin

lemma letter_bound {s1 s2 X : Mat k r} {CW CI CN : ℝ} (hCI : 0 ≤ CI) (hCN : 0 ≤ CN)
    (hX : unitLie k r X) (hi : gN s2⁻¹ ≤ CI) (hw : gN s2 ≤ CW) (hN : gN s1⁻¹ ≤ CN * gN s1) :
    ‖(s1 * s2)⁻¹ * X * (s1 * s2)‖ ≤ CI * CN * CW * ((2 * r + k + 1 : ℕ) : ℝ) * gN s1 ^ 2 := by
  have h0 : ∀ M : Mat k r, 0 ≤ gN M := fun M => Real.sqrt_nonneg _
  have hn : gN X ≤ ((2 * r + k + 1 : ℕ) : ℝ) := gN_unit hX.2
  have ha : gN (s2⁻¹ * s1⁻¹ * X) ≤ CI * (CN * gN s1) * ((2 * r + k + 1 : ℕ) : ℝ) := by
    calc gN (s2⁻¹ * s1⁻¹ * X) ≤ gN (s2⁻¹ * s1⁻¹) * gN X := gN_mul_le_hermitian_curvature _ _
      _ ≤ (gN s2⁻¹ * gN s1⁻¹) * gN X := mul_le_mul_of_nonneg_right (gN_mul_le_hermitian_curvature _ _) (h0 _)
      _ ≤ (CI * (CN * gN s1)) * ((2 * r + k + 1 : ℕ) : ℝ) :=
          mul_le_mul (mul_le_mul hi hN (h0 _) hCI) hn (h0 _)
            (mul_nonneg hCI (mul_nonneg hCN (h0 _)))
  have hb : gN (s1 * s2) ≤ gN s1 * CW :=
    (gN_mul_le_hermitian_curvature _ _).trans (mul_le_mul_of_nonneg_left hw (h0 _))
  rw [Matrix.mul_inv_rev]
  calc ‖s2⁻¹ * s1⁻¹ * X * (s1 * s2)‖ ≤ gN (s2⁻¹ * s1⁻¹ * X * (s1 * s2)) := norm_le_gN _
    _ ≤ gN (s2⁻¹ * s1⁻¹ * X) * gN (s1 * s2) := gN_mul_le_hermitian_curvature _ _
    _ ≤ (CI * (CN * gN s1) * ((2 * r + k + 1 : ℕ) : ℝ)) * (gN s1 * CW) :=
        mul_le_mul ha hb (h0 _)
          (mul_nonneg (mul_nonneg hCI (mul_nonneg hCN (h0 _))) (Nat.cast_nonneg _))
    _ = CI * CN * CW * ((2 * r + k + 1 : ℕ) : ℝ) * gN s1 ^ 2 := by ring

lemma neg_rpow_bound {y s c A : ℝ} (hy : 0 < y) (hs : 0 < s) (hc : 0 < c) (hA : 0 < A) (h : y ≤ c * s) :
    s ^ (-A) ≤ c ^ A * y ^ (-A) := by
  have h1 : y ^ A ≤ (c * s) ^ A := Real.rpow_le_rpow hy.le h hA.le
  rw [Real.mul_rpow hc.le hs.le] at h1
  have hsA : 0 < s ^ A := Real.rpow_pos_of_pos hs A
  have hyA : 0 < y ^ A := Real.rpow_pos_of_pos hy A
  have hcA : 0 < c ^ A := Real.rpow_pos_of_pos hc A
  have key : 1 / (c ^ A * s ^ A) ≤ 1 / y ^ A := one_div_le_one_div_of_le hyA h1
  rw [Real.rpow_neg hs.le, Real.rpow_neg hy.le]
  have e1 : (s ^ A)⁻¹ = c ^ A * (1 / (c ^ A * s ^ A)) := by
    field_simp
  rw [e1, ← one_div]
  exact mul_le_mul_of_nonneg_left key hcA.le

lemma split_bound {x a a' C β : ℝ} (e : ℕ) (hx : 1 ≤ x) (ha : 0 < a) (ha' : 0 < a') (hC : 0 < C)
    (hβ : 0 ≤ β) (h1 : a ≤ C * x ^ e) (h2 : a' ≤ C * x ^ e) :
    x ^ (-(2 * (e : ℝ) * β)) ≤ C ^ β * C ^ β * (a ^ (-β) * a' ^ (-β)) := by
  have hx0 : 0 < x := by linarith
  have hxe : 0 < x ^ e := pow_pos hx0 e
  have hCb : 0 < C ^ β := Real.rpow_pos_of_pos hC β
  have hxb : 0 < x ^ ((e : ℝ) * β) := Real.rpow_pos_of_pos hx0 _
  have one : ∀ b : ℝ, 0 < b → b ≤ C * x ^ e → x ^ (-((e : ℝ) * β)) ≤ C ^ β * b ^ (-β) := by
    intro b hb hbC
    have h := Real.rpow_le_rpow hb.le hbC hβ
    rw [Real.mul_rpow hC.le hxe.le, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le] at h
    have hbb : 0 < b ^ β := Real.rpow_pos_of_pos hb β
    have key : 1 / (C ^ β * x ^ ((e : ℝ) * β)) ≤ 1 / b ^ β := one_div_le_one_div_of_le hbb h
    rw [Real.rpow_neg hx0.le, Real.rpow_neg hb.le]
    have e1 : (x ^ ((e : ℝ) * β))⁻¹ = C ^ β * (1 / (C ^ β * x ^ ((e : ℝ) * β))) := by
      field_simp
    rw [e1, ← one_div]
    exact mul_le_mul_of_nonneg_left key hCb.le
  have k1 := one a ha h1
  have k2 := one a' ha' h2
  have hsplit : x ^ (-(2 * (e : ℝ) * β)) = x ^ (-((e : ℝ) * β)) * x ^ (-((e : ℝ) * β)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [hsplit]
  calc x ^ (-((e : ℝ) * β)) * x ^ (-((e : ℝ) * β))
      ≤ (C ^ β * a ^ (-β)) * (C ^ β * a' ^ (-β)) :=
        mul_le_mul k1 k2 (Real.rpow_nonneg hx0.le _)
          (mul_nonneg hCb.le (Real.rpow_nonneg ha.le _))
    _ = C ^ β * C ^ β * (a ^ (-β) * a' ^ (-β)) := by ring

theorem nnMaj_of_parts : NNMinor → NNVol → Formalism.FourierDecayAlt.P.JFxDs2.NNMaj := by
  intro hM hV k r Wp Wq _ _ _ _ D A m hThr K hK hKO
  have hnn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hT := hThr
  unfold TransportedAlt at hT
  rw [lt_div_iff₀ (by positivity)] at hT
  have hrm : 0 ≤ 6 * (r : ℝ) * (m : ℝ) := by positivity
  have hA2pos : 0 < A - 6 * (r : ℝ) * (m : ℝ) := by nlinarith
  have hApos : 0 < A := by linarith
  have he0 : (0 : ℝ) < ((3 * (r + 1) : ℕ) : ℝ) := by positivity
  set β : ℝ := (A - 6 * (r : ℝ) * (m : ℝ)) / (2 * ((3 * (r + 1) : ℕ) : ℝ)) with hβ
  have hcast : ((3 * (r + 1) : ℕ) : ℝ) = 3 * ((r : ℝ) + 1) := by push_cast; ring
  have hβn : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < β := by
    rw [hβ, lt_div_iff₀ (by positivity), hcast]
    have : 0 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * ((r : ℝ) + 1) := by positivity
    nlinarith
  have hβ0 : 0 ≤ β := le_trans (sq_nonneg _) hβn.le
  have h2eβ : 2 * ((3 * (r + 1) : ℕ) : ℝ) * β = A - 6 * (r : ℝ) * (m : ℝ) := by
    rw [hβ]; field_simp
  obtain ⟨CW1, hCW1, hW1⟩ := uw_bound D.z_mem D.T_pos
  obtain ⟨CW2, hCW2, hW2⟩ := uw_bound D.z'_mem D.T'_pos
  set CW : ℝ := max CW1 CW2 with hCWd
  have hCW : 1 ≤ CW := le_trans hCW1 (le_max_left _ _)
  set CH : ℝ := gN (Hpk k r) ^ 2 with hCHd
  have hCH : 0 ≤ CH := sq_nonneg _
  set CI : ℝ := max (CH * CW) 1 with hCId
  have hCI : 1 ≤ CI := le_max_right _ _
  set CN : ℝ := max CH 1 with hCNd
  have hCN : 1 ≤ CN := le_max_right _ _
  obtain ⟨Cm, hCm⟩ := hM k r D.z D.z' K hK (fun g hg => ⟨(hKO hg).1, (hKO hg).2.1⟩)
  set Cm' : ℝ := max Cm 1 with hCmd
  have hCm' : 1 ≤ Cm' := le_max_right _ _
  set a : ℝ := max (CI * CN * CW * ((2 * r + k + 1 : ℕ) : ℝ) * Cm' ^ 2) 1 with had
  have ha : 1 ≤ a := le_max_right _ _
  set c : ℝ := CW * CI with hcd
  have hc : 1 ≤ c := by nlinarith
  set K0 : ℝ := a ^ m * c ^ A * (Cm' ^ β * Cm' ^ β) with hK0
  have haa : CI * CN * CW * ((2 * r + k + 1 : ℕ) : ℝ) * Cm' ^ 2 ≤ a := le_max_left _ _
  have hCmle : Cm ≤ Cm' := le_max_left _ _
  have hCNle : CH ≤ CN := le_max_left _ _
  have hCIle : CH * CW ≤ CI := le_max_left _ _
  have hCW1le : CW1 ≤ CW := le_max_left _ _
  have hCW2le : CW2 ≤ CW := le_max_right _ _
  clear_value K0 c a Cm' CN CI CH CW

  have hWb : ∀ h, h ∈ UWset k r D.z ∨ h ∈ UWset k r D.z' → gN h ≤ CW ∧ gN h⁻¹ ≤ CI := by
    intro h hh
    have hG : h ∈ GV k r := by rcases hh with hh | hh <;> exact hh.1
    have h1 : gN h ≤ CW := by
      rcases hh with hh | hh
      · exact le_trans (hW1 h hh) hCW1le
      · exact le_trans (hW2 h hh) hCW2le
    refine ⟨h1, le_trans (gN_inv_le hG) (le_trans ?_ hCIle)⟩
    rw [← hCHd]; exact mul_le_mul_of_nonneg_left h1 hCH
  refine ⟨fun p => K0 * (gN (Matrix.of p.1.2 : Mat k r) ^ (-β) * gN (Matrix.of p.2.2 : Mat k r) ^ (-β)), ?_, ?_⟩
  · have hfW : IsFiniteMeasure D.μW := RankOneEmbeddings.R1.haar_finite B2x3.compactW D.z_mem D.T_pos D.haarW
    have hfW' : IsFiniteMeasure D.μW' := RankOneEmbeddings.R1.haar_finite B2x3.compactW D.z'_mem D.T'_pos D.haarW'
    have hsN := B5.haar_sigmaFinite D.haarN
    have hN := intN hV D.haarN hβn
    have i1 : Integrable (fun q : Mt k r × Mt k r => (1 : ℝ) * gN (Matrix.of q.2 : Mat k r) ^ (-β))
        (D.μW.prod D.μN) := (integrable_const (1 : ℝ)).mul_prod hN
    have i2 : Integrable (fun q : Mt k r × Mt k r => (1 : ℝ) * gN (Matrix.of q.2 : Mat k r) ^ (-β))
        (D.μW'.prod D.μN) := (integrable_const (1 : ℝ)).mul_prod hN
    have i3 := (i1.mul_prod i2).const_mul K0
    unfold RealPlaceData.μSS
    refine i3.congr (Eventually.of_forall fun p => ?_)
    simp only [one_mul]
  · intro u v hu hv hl g hg
    filter_upwards [B5.ae_inSS D] with p hp
    have hgG : g ∈ GV k r := (hKO hg).1
    obtain ⟨hh, hn, hh', hn'⟩ := hp
    have hnG : (Matrix.of p.1.2 : Mat k r) ∈ GV k r := hn.1
    have hn'G : (Matrix.of p.2.2 : Mat k r) ∈ GV k r := hn'.1
    have hxG : (Matrix.of p.1.2 : Mat k r)⁻¹ * g * Matrix.of p.2.2 ∈ GV k r :=
      WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hnG) hgG) hn'G
    set x : Mat k r := (Matrix.of p.1.2 : Mat k r)⁻¹ * g * Matrix.of p.2.2 with hxd
    have hx1 : 1 ≤ gN x := BetaSesquilinearity.gN_ge_one hxG
    have hx0 : 0 < gN x := by linarith
    obtain ⟨hm1, hm2⟩ := hCm g hg _ hn _ hn'
    have hxp : 0 ≤ gN x ^ (3 * r) := pow_nonneg (B6.gN_nonneg _) _
    have hn1 : gN (Matrix.of p.1.2 : Mat k r) ≤ Cm' * gN x ^ (3 * r) :=
      le_trans hm1 (mul_le_mul_of_nonneg_right hCmle hxp)
    have hn2 : gN (Matrix.of p.2.2 : Mat k r) ≤ Cm' * gN x ^ (3 * r) :=
      le_trans hm2 (mul_le_mul_of_nonneg_right hCmle hxp)

    have hsq : ∀ y : Mat k r, 0 ≤ gN y → gN y ≤ Cm' * gN x ^ (3 * r) →
        CI * CN * CW * ((2 * r + k + 1 : ℕ) : ℝ) * gN y ^ 2 ≤ a * gN x ^ (6 * r) := by
      intro y hy0 hy
      have h1 : gN y ^ 2 ≤ Cm' ^ 2 * gN x ^ (6 * r) := by
        calc gN y ^ 2 ≤ (Cm' * gN x ^ (3 * r)) ^ 2 := pow_le_pow_left₀ hy0 hy 2
          _ = Cm' ^ 2 * gN x ^ (6 * r) := by rw [mul_pow, ← pow_mul]; ring_nf
      have h0 : 0 ≤ CI * CN * CW * ((2 * r + k + 1 : ℕ) : ℝ) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) (Nat.cast_nonneg _)
      calc CI * CN * CW * ((2 * r + k + 1 : ℕ) : ℝ) * gN y ^ 2
          ≤ CI * CN * CW * ((2 * r + k + 1 : ℕ) : ℝ) * (Cm' ^ 2 * gN x ^ (6 * r)) :=
            mul_le_mul_of_nonneg_left h1 h0
        _ = (CI * CN * CW * ((2 * r + k + 1 : ℕ) : ℝ) * Cm' ^ 2) * gN x ^ (6 * r) := by ring
        _ ≤ a * gN x ^ (6 * r) :=
            mul_le_mul_of_nonneg_right haa (pow_nonneg (B6.gN_nonneg _) _)
    have hnInv : ∀ y : Mat k r, y ∈ GV k r → gN y⁻¹ ≤ CN * gN y := fun y hy =>
      le_trans (gN_inv_le hy) (by rw [← hCHd]; exact mul_le_mul_of_nonneg_right hCNle (B6.gN_nonneg _))
    set L : ℝ := a * gN x ^ (6 * r) with hLd
    have hL1 : 1 ≤ L := by
      have : 1 ≤ gN x ^ (6 * r) := one_le_pow₀ hx1
      nlinarith
    have hU : ∀ X ∈ u, 0 ≤ ‖AdL p X‖ ∧ ‖AdL p X‖ ≤ L := by
      intro X hX
      refine ⟨norm_nonneg _, le_trans ?_ (hsq _ (B6.gN_nonneg _) hn1)⟩
      exact letter_bound (by linarith) (by linarith) (hu X hX) (hWb _ (Or.inl hh)).2 (hWb _ (Or.inl hh)).1
        (hnInv _ hnG)
    have hV' : ∀ X ∈ v, 0 ≤ ‖AdR p X‖ ∧ ‖AdR p X‖ ≤ L := by
      intro X hX
      refine ⟨norm_nonneg _, le_trans ?_ (hsq _ (B6.gN_nonneg _) hn2)⟩
      exact letter_bound (by linarith) (by linarith) (hv X hX) (hWb _ (Or.inr hh')).2 (hWb _ (Or.inr hh')).1
        (hnInv _ hn'G)
    obtain ⟨pu0, pu⟩ := list_prod_le (u.map fun X => ‖AdL p X‖) L (by
      intro y hy; obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hy; exact hU X hX)
    obtain ⟨pv0, pv⟩ := list_prod_le (v.map fun X => ‖AdR p X‖) L (by
      intro y hy; obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hy; exact hV' X hX)
    rw [List.length_map] at pu pv
    have hUV : (u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod ≤ a ^ m * gN x ^ (6 * r * m) := by
      calc _ ≤ L ^ u.length * L ^ v.length := mul_le_mul pu pv pv0 (pow_nonneg (by linarith) _)
        _ = L ^ (u.length + v.length) := (pow_add _ _ _).symm
        _ ≤ L ^ m := pow_le_pow_right₀ hL1 hl
        _ = a ^ m * gN x ^ (6 * r * m) := by rw [hLd, mul_pow, ← pow_mul]

    have hsG : sgs p g ∈ GV k r := B7.sgs_mem D ⟨hh, hn, hh', hn'⟩ hgG
    have hs0 : 0 < gN (sgs p g) := B6.gN_pos hsG
    have hhu := WeylGroupFacts.isUnit_of_uh hh.1
    have hh'u := WeylGroupFacts.isUnit_of_uh hh'.1
    have hxe : x = Matrix.of p.1.1 * sgs p g * (Matrix.of p.2.1 : Mat k r)⁻¹ := by
      rw [hxd]; unfold sgs
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hhu, Matrix.mul_nonsing_inv _ hh'u, Matrix.mul_one]
    have hxs : gN x ≤ c * gN (sgs p g) := by
      rw [hxe]
      calc gN (Matrix.of p.1.1 * sgs p g * (Matrix.of p.2.1 : Mat k r)⁻¹)
          ≤ gN (Matrix.of p.1.1 * sgs p g) * gN (Matrix.of p.2.1 : Mat k r)⁻¹ := B6.gN_mul_le _ _
        _ ≤ (gN (Matrix.of p.1.1 : Mat k r) * gN (sgs p g)) * gN (Matrix.of p.2.1 : Mat k r)⁻¹ :=
            mul_le_mul_of_nonneg_right (B6.gN_mul_le _ _) (B6.gN_nonneg _)
        _ ≤ (CW * gN (sgs p g)) * CI :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hWb _ (Or.inl hh)).1 (B6.gN_nonneg _))
              (hWb _ (Or.inr hh')).2 (B6.gN_nonneg _) (mul_nonneg (by linarith) (B6.gN_nonneg _))
        _ = c * gN (sgs p g) := by rw [hcd]; ring
    have hS := neg_rpow_bound hx0 hs0 (by linarith) hApos hxs

    have hsplit := split_bound (3 * (r + 1)) hx1 (B6.gN_pos hnG) (B6.gN_pos hn'G) (by linarith : (0 : ℝ) < Cm') hβ0
      (le_trans hn1 (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 (show 3 * r ≤ 3 * (r + 1) by omega))
        (by linarith : (0 : ℝ) ≤ Cm')))
      (le_trans hn2 (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 (show 3 * r ≤ 3 * (r + 1) by omega))
        (by linarith : (0 : ℝ) ≤ Cm')))
    rw [h2eβ] at hsplit
    have hcomb : gN x ^ (6 * r * m) * gN x ^ (-A) = gN x ^ (-(A - 6 * (r : ℝ) * (m : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0]; congr 1; push_cast; ring
    have ham : 0 ≤ a ^ m * gN x ^ (6 * r * m) := mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (B6.gN_nonneg _) _)
    calc (u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * gN (sgs p g) ^ (-A)
        ≤ (a ^ m * gN x ^ (6 * r * m)) * (c ^ A * gN x ^ (-A)) :=
          mul_le_mul hUV hS (Real.rpow_nonneg hs0.le _) ham
      _ = a ^ m * c ^ A * (gN x ^ (6 * r * m) * gN x ^ (-A)) := by ring
      _ = a ^ m * c ^ A * gN x ^ (-(A - 6 * (r : ℝ) * (m : ℝ))) := by rw [hcomb]
      _ ≤ a ^ m * c ^ A * (Cm' ^ β * Cm' ^ β * (gN (Matrix.of p.1.2 : Mat k r) ^ (-β) *
            gN (Matrix.of p.2.2 : Mat k r) ^ (-β))) :=
          mul_le_mul_of_nonneg_left hsplit (mul_nonneg (pow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _))
      _ = _ := by rw [hK0]; ring

theorem nnSlice_of_parts : NNMinor → NNVol → Formalism.FourierDecayAlt.P.JFxDs5.NNSlice := by
  intro hM hV k r Wp Wq _ _ _ _ D A m hThr c hc μ hμ
  have hnn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hT := hThr
  unfold TransportedAlt at hT
  rw [lt_div_iff₀ (by positivity)] at hT
  have hrm : 0 ≤ 6 * (r : ℝ) * (m : ℝ) := by positivity
  have hApos : 0 < A := by nlinarith
  have he0 : (0 : ℝ) < ((3 * (r + 1) : ℕ) : ℝ) := by positivity
  set β : ℝ := A / (2 * ((3 * (r + 1) : ℕ) : ℝ)) with hβ
  have hcast : ((3 * (r + 1) : ℕ) : ℝ) = 3 * ((r : ℝ) + 1) := by push_cast; ring
  have hβn : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < β := by
    rw [hβ, lt_div_iff₀ (by positivity), hcast]
    have : 0 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * ((r : ℝ) + 1) := by positivity
    nlinarith
  have hβ0 : 0 ≤ β := le_trans (sq_nonneg _) hβn.le
  have h2eβ : 2 * ((3 * (r + 1) : ℕ) : ℝ) * β = A := by rw [hβ]; field_simp
  have hg0G : bigCell k r c (castW μ) ∈ GV k r := big_cell_mem_holds k r c (castW μ) hc (JFxDs5.castW_mem hμ)
  have hmin := big_cell_minors_holds k r D.z D.z' c (castW μ) D.z_mem D.z'_mem
  have hD : ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r D.z D.z' (bigCell k r c (castW μ)) l ≠ 0 := by
    intro l hl
    have h := hmin.1 ⟨l.val, by omega⟩
    have hl' : (⟨(⟨l.val, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Fin (r + 2)) = l := Fin.ext rfl
    rw [← hl', h]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  obtain ⟨Cm, hCm⟩ := hM k r D.z D.z' {bigCell k r c (castW μ)} isCompact_singleton
    (fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact ⟨hg0G, hD⟩)
  set Cm' : ℝ := max Cm 1 with hCmd
  have hCm' : 1 ≤ Cm' := le_max_right _ _
  have hCmle : Cm ≤ Cm' := le_max_left _ _
  clear_value Cm'
  have hsN := B5.haar_sigmaFinite D.haarN
  have hN := intN hV D.haarN hβn
  have ib : Integrable (fun nn : Mt k r × Mt k r => (Cm' ^ β * Cm' ^ β) *
      (gN (Matrix.of nn.1 : Mat k r) ^ (-β) * gN (Matrix.of nn.2 : Mat k r) ^ (-β))) (D.μN.prod D.μN) :=
    (hN.mul_prod hN).const_mul _
  have hae : ∀ᵐ nn ∂(D.μN.prod D.μN), (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧
      (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae (B5.haar_ae D.haarN)).and
      (Measure.quasiMeasurePreserving_snd.ae (B5.haar_ae D.haarN))
  have c2 : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} := B6.isClosed_Nset k r
  have hTc : IsClosed {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧
      (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} :=
    (c2.preimage continuous_fst).inter (c2.preimage continuous_snd)
  have h1c : Continuous fun nn : Mt k r × Mt k r => (Matrix.of nn.1 : Mat k r) := continuous_fst
  have h2c : Continuous fun nn : Mt k r × Mt k r => (Matrix.of nn.2 : Mat k r) := continuous_snd
  have hy : ContinuousOn (fun nn : Mt k r × Mt k r =>
      (Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2)
      {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧
        (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} :=
    B6.continuousOn_matrix_mul (B6.continuousOn_matrix_mul
      ((B6.inv_continuousOn k r).comp h1c.continuousOn (fun nn h => B6.Nset_sub _ _ h.1)) continuousOn_const)
      h2c.continuousOn
  have hyG : ∀ nn ∈ {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧
      (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r},
      (Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2 ∈ GV k r := fun nn h =>
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv (B6.Nset_sub _ _ h.1)) hg0G) (B6.Nset_sub _ _ h.2)
  have hcont : ContinuousOn (fun nn : Mt k r × Mt k r =>
      gN ((Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ^ (-A))
      {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧
        (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} :=
    (B6.gN_continuous.comp_continuousOn hy).rpow_const fun nn h => Or.inl (B6.gN_pos (hyG nn h)).ne'
  have hmeas : AEStronglyMeasurable (fun nn : Mt k r × Mt k r =>
      gN ((Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ^ (-A)) (D.μN.prod D.μN) := by
    have := hcont.aestronglyMeasurable (μ := D.μN.prod D.μN) hTc.measurableSet
    have hr : (D.μN.prod D.μN).restrict {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧
        (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} = D.μN.prod D.μN :=
      Measure.restrict_eq_self_of_ae_mem hae
    rwa [hr] at this
  refine Integrable.mono' ib hmeas ?_
  filter_upwards [hae] with nn hnn
  have hxG := hyG nn hnn
  have hx1 : 1 ≤ gN ((Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) := BetaSesquilinearity.gN_ge_one hxG
  obtain ⟨hm1, hm2⟩ := hCm _ (Set.mem_singleton _) _ hnn.1 _ hnn.2
  have hxp : 0 ≤ gN ((Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ^ (3 * r) :=
    pow_nonneg (B6.gN_nonneg _) _
  have hpw : gN ((Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ^ (3 * r) ≤
      gN ((Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ^ (3 * (r + 1)) :=
    pow_le_pow_right₀ hx1 (by omega)
  have hsplit := split_bound (3 * (r + 1)) hx1 (B6.gN_pos (B6.Nset_sub _ _ hnn.1))
    (B6.gN_pos (B6.Nset_sub _ _ hnn.2)) (by linarith : (0 : ℝ) < Cm') hβ0
    (le_trans hm1 (le_trans (mul_le_mul_of_nonneg_right hCmle hxp)
      (mul_le_mul_of_nonneg_left hpw (by linarith))))
    (le_trans hm2 (le_trans (mul_le_mul_of_nonneg_right hCmle hxp)
      (mul_le_mul_of_nonneg_left hpw (by linarith))))
  rw [h2eβ] at hsplit
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (B6.gN_nonneg _) _)]
  exact hsplit

section vol

open Formalism.FourierDecayAlt.P.B2x6

variable {k r' : ℕ}

lemma heisLev_mid (x : Formalism.FourierDecayAlt.B2.HPar k r') (g : Mat k r') (i j : Fin (2 * r' + k + 1)) :
    (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' i) (lv k r' j) = g i j := by
  have hw1 : (ιLev k 1 r' g *ᵥ bvec (lv k r' j)) (iL k r') = 0 := by
    rw [lev_mulVec_L]; exact Pi.single_eq_of_ne (lv_ne_iL j).symm _
  have hw2 : res (ιLev k 1 r' g *ᵥ bvec (lv k r' j)) = g *ᵥ bvec j := by
    rw [lev_mulVec_res, bvec_lv, lift_res]
  rw [ent (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' i) (lv k r' j), ← Matrix.mulVec_mulVec]
  calc (Formalism.FourierDecayAlt.B2.heis0 k r' x *ᵥ (ιLev k 1 r' g *ᵥ bvec (lv k r' j))) (lv k r' i)
      = res (Formalism.FourierDecayAlt.B2.heis0 k r' x *ᵥ (ιLev k 1 r' g *ᵥ bvec (lv k r' j))) i := rfl
    _ = (res (ιLev k 1 r' g *ᵥ bvec (lv k r' j)) + (ιLev k 1 r' g *ᵥ bvec (lv k r' j)) (iL k r') • x.1) i := by
        rw [heis_res]
    _ = (g *ᵥ bvec j) i := by rw [hw2, hw1, zero_smul, add_zero]
    _ = g i j := (ent g i j).symm

lemma lev_bvec_iL (g : Mat k r') : ιLev k 1 r' g *ᵥ bvec (iL k r') = bvec (iL k r') := by
  have h0 : res (bvec (iL k r')) = 0 := funext fun j => Pi.single_eq_of_ne (lv_ne_iL j) _
  apply vext
  · rw [lev_mulVec_F]
  · rw [lev_mulVec_res, h0, Matrix.mulVec_zero]
  · rw [lev_mulVec_L]

lemma heisLev_col (x : Formalism.FourierDecayAlt.B2.HPar k r') (g : Mat k r') (j : Fin (2 * r' + k + 1)) :
    (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' j) (iL k r') = x.1 j := by
  have h0 : res (bvec (iL k r')) = 0 := funext fun j => Pi.single_eq_of_ne (lv_ne_iL j) _
  have h1 : bvec (iL k r') (iL k r') = 1 := Pi.single_eq_same _ _
  rw [ent (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' j) (iL k r'), ← Matrix.mulVec_mulVec,
    lev_bvec_iL]
  calc (Formalism.FourierDecayAlt.B2.heis0 k r' x *ᵥ bvec (iL k r')) (lv k r' j)
      = res (Formalism.FourierDecayAlt.B2.heis0 k r' x *ᵥ bvec (iL k r')) j := rfl
    _ = (res (bvec (iL k r')) + bvec (iL k r') (iL k r') • x.1) j := by rw [heis_res]
    _ = x.1 j := by rw [h0, h1, one_smul, zero_add]

lemma heisLev_corner (x : Formalism.FourierDecayAlt.B2.HPar k r') (g : Mat k r') :
    ((Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (iF k r') (iL k r')).im = x.2 := by
  rw [ent (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (iF k r') (iL k r'), ← Matrix.mulVec_mulVec,
    lev_bvec_iL, ← ent]
  have h := B2x5.heis_col k r' x (iF k r')
  have e1 : Formalism.FourierDecayAlt.P.B2x6.iL k r' = Formalism.FourierDecayAlt.P.B2x5.iL k r' := rfl
  have e2 : Formalism.FourierDecayAlt.P.B2x6.iF k r' = Formalism.FourierDecayAlt.P.B2x5.i0 k r' := rfl
  rw [e1, h, e2]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, B2x5.dual_base_vector_first_zero, B2x5.lifted_vector_first, B2x5.base_vector_first_one, zero_add, mul_one]
  simp [Formalism.FourierDecayAlt.B2.hb]

lemma sum_lv_le (f : Fin (2 * (1 + r') + k + 1) → ℝ) (hf : ∀ p, 0 ≤ f p) :
    ∑ j, f (lv k r' j) ≤ ∑ p, f p := by
  have hinj : Function.Injective (lv k r') := by
    intro a b h
    apply Fin.ext
    have h2 : (lv k r' a).val = (lv k r' b).val := congrArg Fin.val h
    have ea : (lv k r' a).val = a.val + 1 := rfl
    have eb : (lv k r' b).val = b.val + 1 := rfl
    omega
  calc ∑ j, f (lv k r' j) = ∑ p ∈ Finset.univ.map ⟨lv k r', hinj⟩, f p := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ p, f p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hf p)

lemma gN_lev_le (x : Formalism.FourierDecayAlt.B2.HPar k r') (g : Mat k r') :
    gN g ≤ gN (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) := by
  have hM := heisLev_mid x g
  show Real.sqrt _ ≤ Real.sqrt _
  apply Real.sqrt_le_sqrt
  calc ∑ i, ∑ j, Complex.normSq (g i j)
      = ∑ i, ∑ j, Complex.normSq ((Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' i) (lv k r' j)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hM i j]
    _ ≤ ∑ i, ∑ q, Complex.normSq ((Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' i) q) :=
        Finset.sum_le_sum fun i _ =>
          sum_lv_le (fun q => Complex.normSq ((Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' i) q))
            (fun q => Complex.normSq_nonneg _)
    _ ≤ ∑ p, ∑ q, Complex.normSq ((Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) p q) :=
        sum_lv_le (fun p => ∑ q, Complex.normSq ((Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) p q))
          (fun p => Finset.sum_nonneg fun q _ => Complex.normSq_nonneg _)

lemma coord_le (x : Formalism.FourierDecayAlt.B2.HPar k r') (g : Mat k r') :
    ‖x‖ ≤ gN (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) := by
  have hE : ∀ p q, ‖(Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) p q‖ ≤
      gN (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) := fun p q =>
    (Matrix.norm_entry_le_entrywise_sup_norm _).trans (norm_le_gN _)
  have h0 : 0 ≤ gN (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) := Real.sqrt_nonneg _
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
    rw [← heisLev_col x g j]
    exact hE _ _
  · rw [Real.norm_eq_abs, ← heisLev_corner x g]
    refine le_trans ?_ (hE (iF k r') (iL k r'))
    set z := (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (iF k r') (iL k r')
    have hz : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      nlinarith [sq_nonneg z.re]
    calc |z.im| = Real.sqrt (z.im ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (‖z‖ ^ 2) := Real.sqrt_le_sqrt hz
      _ = ‖z‖ := Real.sqrt_sq (norm_nonneg _)

end vol

def heisM (k r' : ℕ) (x : Formalism.FourierDecayAlt.B2.HPar k r') : Mt k (1 + r') := Formalism.FourierDecayAlt.B2.heis0 k r' x

theorem unipotent_volume_growth : NNVol := by
  intro k r
  induction r using Nat.strong_induction_on with
  | _ r ih => ?_
  intro μ hμ
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hb : Formalism.QuantumDeterminants.Nset k 0 = {1} := Formalism.FourierDecayAlt.P.unipotent_haar_base_case k
    have hc : μ ((({1} : Set (Mat k 0)) : Set (Mt k 0))ᶜ) = 0 := by rw [← hb]; exact hμ.conc
    have h1 : μ Set.univ ≤ μ (({1} : Set (Mat k 0)) : Set (Mt k 0)) + μ ((({1} : Set (Mat k 0)) : Set (Mt k 0))ᶜ) := by
      have h2 : (Set.univ : Set (Mt k 0)) = (({1} : Set (Mat k 0)) : Set (Mt k 0)) ∪ (({1} : Set (Mat k 0)) : Set (Mt k 0))ᶜ :=
        (Set.union_compl_self _).symm
      exact h2 ▸ measure_union_le _ _
    have hfin : μ Set.univ ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ h1
      rw [hc, add_zero]
      exact (hμ.finite_compact _ isCompact_singleton).ne
    refine ⟨(μ Set.univ).toReal, fun R hR => ?_⟩
    calc μ {x | gN (Matrix.of x : Mat k 0) ≤ R} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal (μ Set.univ).toReal := (ENNReal.ofReal_toReal hfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right ENNReal.toReal_nonneg
          (Real.one_le_rpow hR (by positivity)))
  obtain ⟨r', rfl⟩ : ∃ r', r = 1 + r' := ⟨r - 1, by omega⟩
  obtain ⟨μ', hμ'⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r'
  obtain ⟨C', hC'⟩ := ih r' (by omega) μ' hμ'
  have hsf' := B5.haar_sigmaFinite hμ'
  have hR0 := Formalism.FourierDecayAlt.P.unipotent_haar_recursion k r' μ' hμ'
  obtain ⟨c, hc⟩ := B2x1.haarUnique k (1 + r') _ _ μ (Formalism.FourierDecayAlt.P.unipotent_radical_closed k (1 + r')) hR0 hμ.conc hμ.left
    hμ.finite_compact
  have hh0 : Measurable (heisM k r') := by
    have : Continuous (heisM k r') := B2x5.continuous_heis0 k r'
    exact this.measurable
  have hμH : Formalism.FourierDecayAlt.B2.μHeis k r' = (volume : Measure (Formalism.FourierDecayAlt.B2.HPar k r')).map (heisM k r') := rfl
  have hlev : Measurable (Formalism.FourierDecayAlt.B2.levM k r') := (B2x2.levM_cont k r').measurable
  have hAH : (volume : Measure (Formalism.FourierDecayAlt.B2.HPar k r')).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨v, hv0, hV⟩ : ∃ v : ℝ, 0 ≤ v ∧
      (volume : Measure (Formalism.FourierDecayAlt.B2.HPar k r')) (Metric.ball 0 1) = ENNReal.ofReal v :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal (measure_ball_lt_top).ne).symm⟩
  have hdim : Module.finrank ℝ (Formalism.FourierDecayAlt.B2.HPar k r') = 2 * (2 * r' + k + 1) + 1 := by
    simp [Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex]; ring
  refine ⟨(c : ℝ) * (v * max C' 0), fun R hR => ?_⟩
  have hR0' : (0 : ℝ) ≤ R := by linarith
  set E : Set (Mt k (1 + r')) := {x | gN (Matrix.of x : Mat k (1 + r')) ≤ R} with hEd
  have hE : MeasurableSet E := measurableSet_le (NormBallVolumes.gN_meas _ _) measurable_const
  have hsub : (Prod.map (heisM k r') (Formalism.FourierDecayAlt.B2.levM k r')) ⁻¹' (Formalism.FourierDecayAlt.B2.mulM ⁻¹' E) ⊆
      Metric.closedBall (0 : Formalism.FourierDecayAlt.B2.HPar k r') R ×ˢ {y : Mt k r' | gN (Matrix.of y : Mat k r') ≤ R} := by
    intro p hp
    have hp' : gN (Formalism.FourierDecayAlt.B2.heis0 k r' p.1 * ιLev k 1 r' (Matrix.of p.2)) ≤ R := hp
    exact ⟨mem_closedBall_zero_iff.2 (le_trans (coord_le p.1 _) hp'), le_trans (gN_lev_le p.1 _) hp'⟩
  have hmeas0 : ((Formalism.FourierDecayAlt.B2.μHeis k r').prod (μ'.map (Formalism.FourierDecayAlt.B2.levM k r'))).map Formalism.FourierDecayAlt.B2.mulM E ≤
      ENNReal.ofReal (R ^ (2 * (2 * r' + k + 1) + 1)) * ENNReal.ofReal v * ENNReal.ofReal (C' * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2)) := by
    rw [Measure.map_apply B2x1.mulM_cont.measurable hE]
    rw [hμH, Measure.map_prod_map _ _ hh0 hlev, Measure.map_apply (hh0.prodMap hlev) (hE.preimage B2x1.mulM_cont.measurable)]
    calc _ ≤ ((volume : Measure (Formalism.FourierDecayAlt.B2.HPar k r')).prod μ')
          (Metric.closedBall (0 : Formalism.FourierDecayAlt.B2.HPar k r') R ×ˢ {y : Mt k r' | gN (Matrix.of y : Mat k r') ≤ R}) :=
          measure_mono hsub
      _ = (volume : Measure (Formalism.FourierDecayAlt.B2.HPar k r')) (Metric.closedBall 0 R) *
            μ' {y : Mt k r' | gN (Matrix.of y : Mat k r') ≤ R} := Measure.prod_prod _ _
      _ ≤ _ := by
          rw [Measure.addHaar_closedBall _ _ hR0', hdim, hV]
          gcongr
          exact hC' R hR
  rw [hc, Measure.smul_apply]
  have hpow : R ^ (2 * (2 * r' + k + 1) + 1) * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2) ≤
      R ^ (((2 * (1 + r') + k + 1 : ℕ) : ℝ) ^ 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith)]
    apply Real.rpow_le_rpow_of_exponent_le hR
    push_cast; nlinarith
  have hC'' : C' * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2) ≤ max C' 0 * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hR0' _)
  calc c • (((Formalism.FourierDecayAlt.B2.μHeis k r').prod (μ'.map (Formalism.FourierDecayAlt.B2.levM k r'))).map Formalism.FourierDecayAlt.B2.mulM E)
      ≤ (c : ℝ≥0∞) * (ENNReal.ofReal (R ^ (2 * (2 * r' + k + 1) + 1)) * ENNReal.ofReal v *
          ENNReal.ofReal (max C' 0 * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2))) := by
        rw [ENNReal.smul_def, smul_eq_mul]
        gcongr
        exact le_trans hmeas0 (by gcongr)
    _ = ENNReal.ofReal ((c : ℝ) * (v * max C' 0 *
          (R ^ (2 * (2 * r' + k + 1) + 1) * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2)))) := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have h0 : 0 ≤ (c : ℝ) * (v * max C' 0) :=
          mul_nonneg c.2 (mul_nonneg hv0 (le_max_right _ _))
        calc (c : ℝ) * (v * max C' 0 * (R ^ (2 * (2 * r' + k + 1) + 1) * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2)))
            = ((c : ℝ) * (v * max C' 0)) *
                (R ^ (2 * (2 * r' + k + 1) + 1) * R ^ (((2 * r' + k + 1 : ℕ) : ℝ) ^ 2)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow h0

theorem nnMaj_of_minor : NNMinor → Formalism.FourierDecayAlt.P.JFxDs2.NNMaj := fun h => nnMaj_of_parts h unipotent_volume_growth

theorem nnSlice_of_minor : NNMinor → Formalism.FourierDecayAlt.P.JFxDs5.NNSlice := fun h => nnSlice_of_parts h unipotent_volume_growth

def NNMinorL : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (K : Set (Mat k r)), IsCompact K →
    (∀ g ∈ K, g ∈ GV k r ∧ ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0) →
    ∃ C : ℝ, ∀ g ∈ K, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ n' ∈ Formalism.QuantumDeterminants.Nset k r,
      gN n ≤ C * gN (n⁻¹ * g * n') ^ (3 * r)

lemma zhat_inv {g : Mat k r} (hg : g ∈ GV k r) (z z' : Fin (2 * r + k + 1) → ℂ) :
    Zhat k r z' z g⁻¹ = (Zhat k r z z' g)ᴴ := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  unfold Zhat
  have hu := WeylGroupFacts.isUnit_of_uh hg
  calc herm (Hpk k r) (g⁻¹ *ᵥ fvec k r z b) (fvec k r z' a)
      = herm (Hpk k r) (g *ᵥ (g⁻¹ *ᵥ fvec k r z b)) (g *ᵥ fvec k r z' a) := (B2x5.herm_UH _ hg _ _).symm
    _ = herm (Hpk k r) (fvec k r z b) (g *ᵥ fvec k r z' a) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    _ = star (herm (Hpk k r) (g *ᵥ fvec k r z' a) (fvec k r z b)) :=
        (B2x4.herm_symm _ (B2x5.Hherm k r) _ _).symm

lemma dmin_inv {g : Mat k r} (hg : g ∈ GV k r) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    Dmin k r z' z g⁻¹ l = star (Dmin k r z z' g l) := by
  simp only [Dmin]
  rw [zhat_inv hg z z', ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]

theorem nnMinor_of_left : NNMinorL → NNMinor := by
  intro hL k r z z' K hK hKD
  obtain ⟨C1, h1⟩ := hL k r z z' K hK hKD
  have hKG : K ⊆ GV k r := fun g hg => (hKD g hg).1
  have hK' : IsCompact ((fun g : Mat k r => g⁻¹) '' K) :=
    hK.image_of_continuousOn ((B6.inv_continuousOn k r).mono hKG)
  obtain ⟨C2, h2⟩ := hL k r z' z _ hK' (by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨WeylGroupFacts.uh_inv (hKG hg), fun l hl => ?_⟩
    rw [dmin_inv (hKG hg)]; exact star_ne_zero.2 ((hKD g hg).2 l hl))
  refine ⟨max C1 (max C2 0 * gN (Hpk k r) ^ (2 * (3 * r))), fun g hg n hn n' hn' => ⟨?_, ?_⟩⟩
  · exact le_trans (h1 g hg n hn n' hn')
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (B6.gN_nonneg _) _))
  · have hgG := hKG hg
    have hx := WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hn.1) hgG) hn'.1
    have hinv : (n⁻¹ * g * n')⁻¹ = n'⁻¹ * g⁻¹ * n := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hn.1),
        Matrix.mul_assoc]
    have e2 := h2 g⁻¹ ⟨g, hg, rfl⟩ n' hn' n hn
    rw [← hinv] at e2
    have hb : gN (n⁻¹ * g * n')⁻¹ ≤ gN (Hpk k r) ^ 2 * gN (n⁻¹ * g * n') := gN_inv_le hx
    calc gN n' ≤ C2 * gN (n⁻¹ * g * n')⁻¹ ^ (3 * r) := e2
      _ ≤ max C2 0 * gN (n⁻¹ * g * n')⁻¹ ^ (3 * r) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (B6.gN_nonneg _) _)
      _ ≤ max C2 0 * (gN (Hpk k r) ^ 2 * gN (n⁻¹ * g * n')) ^ (3 * r) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (B6.gN_nonneg _) hb _) (le_max_right _ _)
      _ = (max C2 0 * gN (Hpk k r) ^ (2 * (3 * r))) * gN (n⁻¹ * g * n') ^ (3 * r) := by
          rw [mul_pow, ← pow_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (B6.gN_nonneg _) _)

theorem nnMaj_of_minorL : NNMinorL → Formalism.FourierDecayAlt.P.JFxDs2.NNMaj := fun h => nnMaj_of_minor (nnMinor_of_left h)

theorem nnSlice_of_minorL : NNMinorL → Formalism.FourierDecayAlt.P.JFxDs5.NNSlice := fun h => nnSlice_of_minor (nnMinor_of_left h)

theorem _root_.Formalism.FourierDecayAlt.P.jf_jDom_of_nMinor : NNMinor → Formalism.FourierDecayAlt.JF.JDom := fun h =>
  Formalism.FourierDecayAlt.P.jf_jDom_of_nnMaj (nnMaj_of_minor h)

theorem _root_.Formalism.FourierDecayAlt.P.jf_jConv_of_nMinor : NNMinor → Formalism.FourierDecayAlt.JF.JConv := fun h =>
  Formalism.FourierDecayAlt.P.jf_jConv_of_nnMaj (nnMaj_of_minor h)

theorem _root_.Formalism.FourierDecayAlt.P.jf_jWords_of_nMinor : NNMinor → Formalism.FourierDecayAlt.JF.JWords := fun h =>
  Formalism.FourierDecayAlt.P.jf_jWords_of_nnMaj (nnMaj_of_minor h)

theorem _root_.Formalism.FourierDecayAlt.P.jf_jqSmooth_of_nMinor : NNMinor → Formalism.FourierDecayAlt.JF.JqSmooth := fun h =>
  Formalism.FourierDecayAlt.P.jf_jqSmooth_of_nnMaj (nnMaj_of_minor h)

theorem _root_.Formalism.FourierDecayAlt.P.last_level_slice_of_minor_bound : NNMinor → Formalism.FourierDecayAlt.P.JFxDs5.SliceRegularityClauses → Formalism.FourierDecayAlt.JF.LastLevelDiagonalSlice :=
  fun h h23 => Formalism.FourierDecayAlt.P.last_level_slice_of_scalar (nnSlice_of_minor h) h23

end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
