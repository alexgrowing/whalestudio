import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace ThmIExists

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem hermLine_ext {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

theorem tensor_right_comm (A B C : HermLine ι) :
    (A.tensor B).tensor C = (A.tensor C).tensor B :=
  hermLine_ext (add_right_comm _ _ _) (funext fun _ => mul_right_comm _ _ _)

theorem tensor_tensor_comm (A B C D : HermLine ι) :
    (A.tensor B).tensor (C.tensor D) = (A.tensor C).tensor (B.tensor D) :=
  hermLine_ext (add_add_add_comm _ _ _ _) (funext fun _ => mul_mul_mul_comm _ _ _ _)

theorem smooth_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  hA.mul hB

def segreLine (m : ℕ) : HermLine ι :=
  HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun _ => (m : ℤ))

theorem segreLine_a (m : ℕ) : (segreLine m : HermLine ι).a = fun _ => (m : ℤ) := rfl

theorem isSmoothHerm_segreLine (m : ℕ) : IsSmoothHerm (segreLine m : HermLine ι) := by
  have hfun : (segreLine m : HermLine ι).h =
      fun z => ∏ k, Real.sqrt (∑ i : ι k, ‖z ⟨k, i⟩‖ ^ 2) ^ m := by
    funext z
    simp only [segreLine, HermLine.ofMetrics, fsMetric, zpow_natCast, EuclideanSpace.norm_eq]
  unfold IsSmoothHerm
  rw [hfun]
  refine contDiffOn_prod fun k _ => (ContDiffOn.sqrt ?_ fun z hz => ?_).pow m
  · exact (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))).contDiffOn
  · obtain ⟨i, hi⟩ := hz k
    exact (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩).ne'

theorem exists_form {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (b : K → ℕ) :
    ∃ s : MRing ι, IsMultiHomog s b ∧ s ∉ P := by
  classical
  have hrel := hP.2.1.2.2
  have hpr : P.IsPrime := hP.2.1.1
  refine ⟨ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow (fun k => (hrel k).choose) b,
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow _ _, fun h => ?_⟩
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow, Ideal.IsPrime.prod_mem_iff] at h
  obtain ⟨k, _, hk⟩ := h
  exact (hrel k).choose_spec (hpr.mem_of_pow_mem _ hk)

open Classical in

def secOf (P : Ideal (MRing ι)) (b : K → ℕ) : MRing ι :=
  if h : ∃ s : MRing ι, IsMultiHomog s b ∧ s ∉ P then h.choose else 0

theorem secOf_spec {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (b : K → ℕ) :
    IsMultiHomog (secOf P b) b ∧ secOf P b ∉ P := by
  have h := exists_form hP b
  rw [secOf, dif_pos h]
  exact h.choose_spec

theorem sec_mul {P : Ideal (MRing ι)} (hpr : P.IsPrime) {A B : HermLine ι} {s t : MRing ι}
    (hs : IsSectionOn P A s) (ht : IsSectionOn P B t) : IsSectionOn P (A.tensor B) (s * t) := by
  obtain ⟨a, ha, has, hsP⟩ := hs
  obtain ⟨b, hb, hbt, htP⟩ := ht
  refine ⟨a + b, fun k => ?_, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul has hbt, fun h => ?_⟩
  · simp [HermLine.tensor, ha, hb]
  · rcases hpr.mem_or_mem h with h | h
    exacts [hsP h, htP h]

theorem sec_congr {P : Ideal (MRing ι)} {A B : HermLine ι} {s : MRing ι} (h : A = B)
    (hs : IsSectionOn P A s) : IsSectionOn P B s := h ▸ hs

def shift (A : HermLine ι) : ℕ := ∑ k, (A.a k).natAbs

def upDeg (A : HermLine ι) : K → ℕ := fun k => (A.a k + shift A).toNat

theorem upDeg_cast (A : HermLine ι) (k : K) : ((upDeg A k : ℕ) : ℤ) = A.a k + shift A := by
  rw [upDeg, Int.toNat_of_nonneg]
  have h1 : (A.a k).natAbs ≤ shift A :=
    Finset.single_le_sum (f := fun k => (A.a k).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have h2 : -((A.a k).natAbs : ℤ) ≤ A.a k := by
    rw [Int.natCast_natAbs]; exact neg_abs_le _
  omega

theorem isSectionOn_up {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (A : HermLine ι) :
    IsSectionOn P (A.tensor (segreLine (shift A))) (secOf P (upDeg A)) :=
  ⟨upDeg A, fun _ => by simp [HermLine.tensor, segreLine_a, upDeg_cast], (secOf_spec hP _).1,
    (secOf_spec hP _).2⟩

theorem isSectionOn_segre {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (m : ℕ) :
    IsSectionOn P (segreLine m) (secOf P fun _ => m) :=
  ⟨fun _ => m, fun _ => rfl, (secOf_spec hP _).1, (secOf_spec hP _).2⟩

def lift {n : ℕ} (J : Ideal (MRing ι) → (Fin n → HermLine ι) → ℝ) :
    Ideal (MRing ι) → (m : ℕ) → (Fin m → HermLine ι) → ℝ :=
  fun W m L => if h : m = n then J W (L ∘ Fin.cast h.symm) else 0

theorem lift_self {n : ℕ} (J : Ideal (MRing ι) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι))
    (L : Fin n → HermLine ι) : lift J W n L = J W L := by
  simp only [lift]
  rfl

theorem recR_congr {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {n : ℕ}
    (h : ∀ W L, I W n L = J W n L) (P : Ideal (MRing ι)) (L : Fin n → HermLine ι) (A : HermLine ι)
    (s : MRing ι) : recR I P L A s = recR J P L A s := by
  unfold recR
  simp only [h]

def step {n : ℕ} (J : Ideal (MRing ι) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    (L : Fin n → HermLine ι) (A : HermLine ι) : ℝ :=
  recR (lift J) P L (A.tensor (segreLine (shift A))) (secOf P (upDeg A)) -
    recR (lift J) P L (segreLine (shift A)) (secOf P fun _ => shift A)

def fam : (n : ℕ) → Ideal (MRing ι) → (Fin n → HermLine ι) → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun P L => step (fam n) P (Fin.init L) (L (Fin.last n))

def famI : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ := fun P n L => fam n P L

theorem famI_snoc (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) :
    famI P (n + 1) (Fin.snoc L A) =
      recR famI P L (A.tensor (segreLine (shift A))) (secOf P (upDeg A)) -
        recR famI P L (segreLine (shift A)) (secOf P fun _ => shift A) := by
  have hc : ∀ (B : HermLine ι) (s : MRing ι), recR (lift (fam n)) P L B s = recR famI P L B s :=
    fun B s => recR_congr (fun W L' => lift_self (fam n) W L') P L B s
  have hs : famI P (n + 1) (Fin.snoc L A) = step (fam n) P L A := by
    simp only [famI, fam, Fin.init_snoc, Fin.snoc_last]
  rw [hs, step, hc, hc]

def LastAddAt (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (P : Ideal (MRing ι)) (L : Fin n → HermLine ι) (A B : HermLine ι),
    IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    I P (n + 1) (Fin.snoc L (A.tensor B)) = I P (n + 1) (Fin.snoc L A) + I P (n + 1) (Fin.snoc L B)

def WDAt (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (P : Ideal (MRing ι)) (L : Fin n → HermLine ι) (B : HermLine ι) (s t : MRing ι),
    IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B →
    IsSectionOn P B s → IsSectionOn P B t → recR I P L B s = recR I P L B t

section Steps

variable (hMul : RMulStatement) {n : ℕ} (hwd : WDAt (famI (ι := ι)) n)
include hMul hwd

theorem famI_eq_diff {P : Ideal (MRing ι)} (hP : IsArithVar P (n + 1)) {L : Fin n → HermLine ι}
    (hL : ∀ j, IsSmoothHerm (L j)) {A C : HermLine ι} (hA : IsSmoothHerm A) (hC : IsSmoothHerm C)
    {t c : MRing ι} (ht : IsSectionOn P (A.tensor C) t) (hc : IsSectionOn P C c) :
    famI P (n + 1) (Fin.snoc L A) = recR famI P L (A.tensor C) t - recR famI P L C c := by
  have hpr : P.IsPrime := hP.2.1.1
  set H : HermLine ι := segreLine (shift A)
  have hH : IsSmoothHerm H := isSmoothHerm_segreLine _
  have hu := isSectionOn_segre hP (shift A)
  have ht0 := isSectionOn_up hP A
  have e1 := hMul K ι famI P n L (A.tensor H) C _ _ hP hL (smooth_tensor hA hH) hC ht0 hc
  have e2 := hMul K ι famI P n L (A.tensor C) H _ _ hP hL (smooth_tensor hA hC) hH ht hu
  have e3 : recR famI P L ((A.tensor H).tensor C) (secOf P (upDeg A) * c) =
      recR famI P L ((A.tensor C).tensor H) (t * secOf P fun _ => shift A) := by
    rw [tensor_right_comm A H C]
    exact hwd P L _ _ _ hP hL (smooth_tensor (smooth_tensor hA hC) hH)
      (sec_congr (tensor_right_comm A H C) (sec_mul hpr ht0 hc)) (sec_mul hpr ht hu)
  rw [famI_snoc]
  linarith

theorem hasRAt_famI : HasRAt (famI (ι := ι)) n := by
  intro P L A s hP hL hA hs
  have hpr : P.IsPrime := hP.2.1.1
  have hH : IsSmoothHerm (segreLine (shift A) : HermLine ι) := isSmoothHerm_segreLine _
  have hu := isSectionOn_segre hP (shift A)
  rw [famI_eq_diff hMul hwd hP hL hA hH (sec_mul hpr hs hu) hu,
    hMul K ι famI P n L A _ s _ hP hL hA hH hs hu]
  ring

theorem lastAddAt_famI : LastAddAt (famI (ι := ι)) n := by
  intro P L A B hP hL hA hB
  have hpr : P.IsPrime := hP.2.1.1
  set Ha : HermLine ι := segreLine (shift A)
  set Hb : HermLine ι := segreLine (shift B)
  have hHa : IsSmoothHerm Ha := isSmoothHerm_segreLine _
  have hHb : IsSmoothHerm Hb := isSmoothHerm_segreLine _
  have hua := isSectionOn_segre hP (shift A)
  have hub := isSectionOn_segre hP (shift B)
  have hta := isSectionOn_up hP A
  have htb := isSectionOn_up hP B
  have htab : IsSectionOn P ((A.tensor B).tensor (Ha.tensor Hb))
      (secOf P (upDeg A) * secOf P (upDeg B)) :=
    sec_congr (tensor_tensor_comm A Ha B Hb) (sec_mul hpr hta htb)
  rw [famI_eq_diff hMul hwd hP hL (smooth_tensor hA hB) (smooth_tensor hHa hHb) htab (sec_mul hpr hua hub),
    famI_eq_diff hMul hwd hP hL hA hHa hta hua, famI_eq_diff hMul hwd hP hL hB hHb htb hub,
    tensor_tensor_comm A B Ha Hb,
    hMul K ι famI P n L _ _ _ _ hP hL (smooth_tensor hA hHa) (smooth_tensor hB hHb) hta htb,
    hMul K ι famI P n L _ _ _ _ hP hL hHa hHb hua hub]
  ring

end Steps

theorem wdAt_zero (hD1 : RegularityIndependence.Statement) : WDAt (famI (ι := ι)) 0 := by
  intro P L B s t hP _ _ hs ht
  have hL : L = Fin.elim0 := funext fun j => j.elim0
  subst hL
  exact hD1 K ι famI P B s t hP hs ht

theorem all_dims (hD1 : RegularityIndependence.Statement) (hMul : RMulStatement)
    (hstep : ∀ n, HasRAt (famI (ι := ι)) n → LastAddAt (famI (ι := ι)) n → WDAt (famI (ι := ι)) (n + 1))
    (n : ℕ) : WDAt (famI (ι := ι)) n ∧ HasRAt (famI (ι := ι)) n ∧ LastAddAt (famI (ι := ι)) n := by
  induction n with
  | zero =>
    have h0 := wdAt_zero (ι := ι) hD1
    exact ⟨h0, hasRAt_famI hMul h0, lastAddAt_famI hMul h0⟩
  | succ n ih =>
    have h1 := hstep n ih.2.1 ih.2.2
    exact ⟨h1, hasRAt_famI hMul h1, lastAddAt_famI hMul h1⟩

theorem isRFamily_famI (hD1 : RegularityIndependence.Statement) (hMul : RMulStatement)
    (hstep : ∀ n, HasRAt (famI (ι := ι)) n → LastAddAt (famI (ι := ι)) n → WDAt (famI (ι := ι)) (n + 1)) :
    IsRFamily (famI (ι := ι)) :=
  ⟨fun P n L A B hP hL hA hB => (all_dims hD1 hMul hstep n).2.2 P L A B hP hL hA hB,
    fun P n L A s a hP hL hA ha hs hsP =>
      (all_dims hD1 hMul hstep n).2.1 P L A s hP hL hA ⟨a, ha, hs, hsP⟩⟩

end ThmIExists

end

end GroundTheory.Heights₂.Heights.Inter
