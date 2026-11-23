import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

noncomputable section

open NumberField IsDedekindDomain Matrix Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Size

theorem le_sup {ι : Type} [Finite ι] (f : ι → ℝ) (p : ι) : f p ≤ ⨆ q, f q :=
  le_ciSup (Set.finite_range f).bddAbove p

theorem sz_nonneg {K ι κ : Type} [NormedField K] (g : Matrix ι κ K) : 0 ≤ sz g :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem sz_mul_le {K : Type} [NormedField K] [IsUltrametricDist K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) : sz (A * B) ≤ sz A * sz B := by
  have hA := sz_nonneg A
  have hB := sz_nonneg B
  refine Real.iSup_le (fun p => ?_) (mul_nonneg hA hB)
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hA hB) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (le_sup (fun q : Fin n × Fin n => ‖A q.1 q.2‖) (p.1, k))
    (le_sup (fun q : Fin n × Fin n => ‖B q.1 q.2‖) (k, p.2)) (norm_nonneg _) hA

def s2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ := ⨆ p : Fin n × Fin n, ‖A p.1 p.2‖ ^ 2

theorem max_sq_entry_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ s2 A :=
  Real.iSup_nonneg fun _ => sq_nonneg _

theorem norm_entry_le_sqrt_max_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖A i j‖ ≤ √(s2 A) :=
  Real.le_sqrt_of_sq_le (le_sup (fun q : Fin n × Fin n => ‖A q.1 q.2‖ ^ 2) (i, j))

theorem max_sq_entry_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    s2 (A * B) ≤ (n : ℝ) ^ 2 * s2 A * s2 B := by
  have hA := max_sq_entry_nonneg A
  have hB := max_sq_entry_nonneg B
  refine Real.iSup_le (fun p => ?_) (mul_nonneg (mul_nonneg (sq_nonneg _) hA) hB)
  have h1 : ‖(A * B) p.1 p.2‖ ≤ n * (√(s2 A) * √(s2 B)) := by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖A p.1 k * B k p.2‖ ≤ ∑ _k : Fin n, √(s2 A) * √(s2 B) :=
          Finset.sum_le_sum fun k _ => by
            rw [norm_mul]
            exact mul_le_mul (norm_entry_le_sqrt_max_sq A _ _) (norm_entry_le_sqrt_max_sq B _ _) (norm_nonneg _)
              (Real.sqrt_nonneg _)
      _ = n * (√(s2 A) * √(s2 B)) := by simp
  calc ‖(A * B) p.1 p.2‖ ^ 2 ≤ (n * (√(s2 A) * √(s2 B))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (n : ℝ) ^ 2 * s2 A * s2 B := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB, mul_assoc]

theorem finsum_mono {α : Type} {f g : α → ℝ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) (h : ∀ a, f a ≤ g a) : ∑ᶠ a, f a ≤ ∑ᶠ a, g a := by
  classical
  rw [finsum_eq_sum_of_support_subset f (s := hf.toFinset ∪ hg.toFinset) (by simp),
    finsum_eq_sum_of_support_subset g (s := hf.toFinset ∪ hg.toFinset) (by simp)]
  exact Finset.sum_le_sum fun a _ => h a

theorem posLog_max_one {x : ℝ} (hx : 0 ≤ x) : Real.posLog (max x 1) = Real.posLog x := by
  rcases le_total x 1 with h | h
  · rw [max_eq_right h, (Real.posLog_eq_zero_iff x).2 (by rwa [abs_of_nonneg hx])]
    simp
  · rw [max_eq_left h]

section Global

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

theorem logSizeM_eq (A : Matrix (Fin n) (Fin n) (Ad E)) :
    logSizeM A = ∑ v, Real.posLog (s2 (A.map (cV v))) + ∑ᶠ w, Real.posLog (sz (A.map (cW w))) :=
  rfl

theorem logSizeM_nonneg (A : Matrix (Fin n) (Fin n) (Ad E)) : 0 ≤ logSizeM A :=
  add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg)
    (finsum_nonneg fun _ => Real.posLog_nonneg)

theorem supp_fin (hS : SzFin) (A : Matrix (Fin n) (Fin n) (Ad E)) :
    (Function.support fun w => Real.posLog (sz (A.map (cW w)))).Finite := by
  refine (hS E (Fin n) (Fin n) A).subset fun w hw => ?_
  by_contra h
  exact hw ((Real.posLog_eq_zero_iff _).2 (by rw [abs_of_nonneg (sz_nonneg _)]; exact not_lt.1 h))

theorem logSizeM_mul (hS : SzFin) (A B : Matrix (Fin n) (Fin n) (Ad E)) :
    logSizeM (A * B) ≤ logSizeM A + logSizeM B +
      Fintype.card (InfinitePlace E) * Real.posLog ((n : ℝ) ^ 2) := by
  have hinf : ∑ v, Real.posLog (s2 ((A * B).map (cV v))) ≤
      ∑ v, Real.posLog (s2 (A.map (cV v))) + ∑ v, Real.posLog (s2 (B.map (cV v))) +
        Fintype.card (InfinitePlace E) * Real.posLog ((n : ℝ) ^ 2) := by
    have : ∀ v, Real.posLog (s2 ((A * B).map (cV v))) ≤
        Real.posLog (s2 (A.map (cV v))) + Real.posLog (s2 (B.map (cV v))) +
          Real.posLog ((n : ℝ) ^ 2) := fun v => by
      rw [Matrix.map_mul]
      refine (Real.posLog_le_posLog (max_sq_entry_nonneg _) (max_sq_entry_mul_le _ _)).trans ?_
      refine Real.posLog_mul.trans ?_
      have := Real.posLog_mul (x := (n : ℝ) ^ 2) (y := s2 (A.map (cV v)))
      linarith
    refine (Finset.sum_le_sum fun v _ => this v).trans (le_of_eq ?_)
    simp [Finset.sum_add_distrib]
  have hfin : ∑ᶠ w, Real.posLog (sz ((A * B).map (cW w))) ≤
      ∑ᶠ w, Real.posLog (sz (A.map (cW w))) + ∑ᶠ w, Real.posLog (sz (B.map (cW w))) := by
    rw [← finsum_add_distrib (supp_fin hS A) (supp_fin hS B)]
    refine finsum_mono (supp_fin hS _) (((supp_fin hS A).union (supp_fin hS B)).subset
      (Function.support_add _ _)) fun w => ?_
    rw [Matrix.map_mul]
    exact (Real.posLog_le_posLog (sz_nonneg _) (sz_mul_le _ _)).trans Real.posLog_mul
  rw [logSizeM_eq, logSizeM_eq, logSizeM_eq]
  linarith

theorem continuous_cV (v : InfinitePlace E) : Continuous (cV v : Ad E → ℂ) :=
  (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (IsTotallyComplex.isComplex v)).continuous.comp ((continuous_apply v).comp continuous_fst)

theorem eventually_fin (a₀ : Ad E) :
    ∀ᶠ a in 𝓝 a₀, ∀ w, ‖cW w a‖ ≤ max ‖cW w a₀‖ 1 := by
  have hU : IsOpen {f : Af E | ∀ w, f w ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E))} :=
    RestrictedProduct.isOpen_forall_mem fun w => Valued.isOpen_valuationSubring _
  have hc : Continuous fun a : Ad E => pFin E a - pFin E a₀ :=
    (continuous_snd).sub continuous_const
  have h0 : (fun a : Ad E => pFin E a - pFin E a₀) a₀ ∈
      {f : Af E | ∀ w, f w ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E))} := by
    intro w
    change (pFin E a₀ - pFin E a₀) w ∈ w.adicCompletionIntegers E
    rw [sub_self]
    exact zero_mem (w.adicCompletionIntegers E)
  filter_upwards [hc.continuousAt.eventually (hU.mem_nhds h0)] with a ha w
  have h1 : ‖cW w a - cW w a₀‖ ≤ 1 := by
    have := ha w
    exact Valued.toNormedField.norm_le_one_iff.2 this
  have h2 : cW w a = (cW w a - cW w a₀) + cW w a₀ := by ring
  rw [h2]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact h1.trans (le_max_right _ _)
  · exact le_max_left _ _

theorem logSizeM_locBdd (hS : SzFin) (A₀ : Matrix (Fin n) (Fin n) (Ad E)) :
    ∃ r, ∀ᶠ A in 𝓝 A₀, logSizeM A ≤ r := by
  refine ⟨∑ v, Real.posLog (⨆ p : Fin n × Fin n, (‖cV v (A₀ p.1 p.2)‖ + 1) ^ 2) +
    ∑ᶠ w, Real.posLog (sz (A₀.map (cW w))), ?_⟩
  have hev : ∀ p : Fin n × Fin n, ∀ᶠ A : Matrix (Fin n) (Fin n) (Ad E) in 𝓝 A₀,
      (∀ v, ‖cV v (A p.1 p.2)‖ ≤ ‖cV v (A₀ p.1 p.2)‖ + 1) ∧
        ∀ w, ‖cW w (A p.1 p.2)‖ ≤ max ‖cW w (A₀ p.1 p.2)‖ 1 := fun p => by
    have hc : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) => A p.1 p.2 :=
      continuous_id.matrix_elem p.1 p.2
    refine Filter.Eventually.and ?_ (hc.continuousAt.eventually (eventually_fin (A₀ p.1 p.2)))
    refine Filter.eventually_all.2 fun v => ?_
    have hc' : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) => ‖cV v (A p.1 p.2)‖ :=
      ((continuous_cV v).comp hc).norm
    exact (hc'.continuousAt.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ h => h.le
  filter_upwards [Filter.eventually_all.2 hev] with A hA
  rw [logSizeM_eq]
  refine add_le_add (Finset.sum_le_sum fun v _ => ?_) ?_
  · refine Real.posLog_le_posLog (max_sq_entry_nonneg _) (Real.iSup_le (fun p => ?_)
      (Real.iSup_nonneg fun _ => sq_nonneg _))
    exact (pow_le_pow_left₀ (norm_nonneg _) ((hA p).1 v) 2).trans
      (le_sup (fun q : Fin n × Fin n => (‖cV v (A₀ q.1 q.2)‖ + 1) ^ 2) p)
  · refine finsum_mono (supp_fin hS A) (supp_fin hS A₀) fun w => ?_
    rw [← posLog_max_one (sz_nonneg (A₀.map (cW w)))]
    refine Real.posLog_le_posLog (sz_nonneg _) (Real.iSup_le (fun p => ?_) (by positivity))
    exact ((hA p).2 w).trans (max_le_max_right 1
      (le_sup (fun q : Fin n × Fin n => ‖cW w (A₀ q.1 q.2)‖) p))

theorem logSize_compact (hS : SzFin) (C : Set (GA E n)) (hC : IsCompact C) :
    ∃ r, ∀ g ∈ C, logSize g ≤ r := by
  refine hC.induction_on (p := fun S => ∃ r, ∀ g ∈ S, logSize g ≤ r) ⟨0, by simp⟩
    (fun s t hst ⟨r, hr⟩ => ⟨r, fun g hg => hr g (hst hg)⟩)
    (fun s t ⟨r, hr⟩ ⟨r', hr'⟩ => ⟨max r r', fun g hg => hg.elim
      (fun h => (hr g h).trans (le_max_left _ _)) (fun h => (hr' g h).trans (le_max_right _ _))⟩)
    fun x _ => ?_
  obtain ⟨r₁, h₁⟩ := logSizeM_locBdd hS x.val
  obtain ⟨r₂, h₂⟩ := logSizeM_locBdd hS (x⁻¹ : GA E n).val
  have e₁ := (Units.continuous_val (M := Matrix (Fin n) (Fin n) (Ad E))).continuousAt.eventually h₁
  have e₂ := (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (Ad E))).continuousAt.eventually h₂
  refine ⟨{g | logSize g ≤ r₁ + r₂}, mem_nhdsWithin_of_mem_nhds ?_, ⟨r₁ + r₂, fun g hg => hg⟩⟩
  filter_upwards [e₁, e₂] with g a b
  exact add_le_add a b

end Global

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem logSizeM_conj (hC : ConjPlaces) (A : Matrix (Fin n) (Fin n) (Ad E)) :
    logSizeM ((A.map (conjAd E))ᵀ) = logSizeM A := by
  obtain ⟨h1, -, π, ψ, hψ, h3⟩ := hC E
  have hinf : ∀ v, (⨆ p : Fin n × Fin n, ‖cV v ((A.map (conjAd E))ᵀ p.1 p.2)‖ ^ 2) =
      ⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2 := fun v => by
    rw [← (Equiv.prodComm (Fin n) (Fin n)).iSup_comp
      (g := fun p : Fin n × Fin n => ‖cV v (A p.1 p.2)‖ ^ 2)]
    refine iSup_congr fun p => ?_
    simp [h1, Matrix.transpose_apply]
  have hfin : ∀ w, (⨆ p : Fin n × Fin n, ‖cW w ((A.map (conjAd E))ᵀ p.1 p.2)‖) =
      ⨆ p : Fin n × Fin n, ‖cW (π w) (A p.1 p.2)‖ := fun w => by
    rw [← (Equiv.prodComm (Fin n) (Fin n)).iSup_comp
      (g := fun p : Fin n × Fin n => ‖cW (π w) (A p.1 p.2)‖)]
    refine iSup_congr fun p => ?_
    simp [h3, hψ, Matrix.transpose_apply]
  unfold logSizeM
  simp only [hinf, hfin]
  congr 1
  exact finsum_comp_equiv π
    (f := fun w => Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖))

theorem inv_thetaR_val {A : Type} [CommRing A] (σ : A →+* A) (g : GL (Fin n) A) :
    ((thetaR σ n g)⁻¹ : GL (Fin n) A).val = (g.val.map σ)ᵀ := rfl

end CM

theorem sizeBasic : SzFin → ConjPlaces → SizeBasic := by
  intro hS hC E _ _ _ n
  refine ⟨logSize_compact hS, fun g => add_nonneg (logSizeM_nonneg _) (logSizeM_nonneg _),
    fun g => ?_, 2 * (Fintype.card (InfinitePlace E) * Real.posLog ((n : ℝ) ^ 2)), fun g h => ?_⟩
  · change logSizeM (thetaR (conjAd E) n g).val + logSizeM ((thetaR (conjAd E) n g)⁻¹ : GA E n).val = _
    rw [inv_thetaR_val, thetaR_val, logSizeM_conj hC, logSizeM_conj hC, logSize, add_comm]
  · have a := logSizeM_mul hS g.val h.val
    have b := logSizeM_mul hS (h⁻¹ : GA E n).val (g⁻¹ : GA E n).val
    simp only [logSize, _root_.mul_inv_rev, Units.val_mul]
    linarith

end GlobalTheory.CompanionTheory.Size

end
