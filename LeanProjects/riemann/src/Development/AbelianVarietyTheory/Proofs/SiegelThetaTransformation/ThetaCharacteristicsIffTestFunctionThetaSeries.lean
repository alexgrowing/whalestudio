import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableNormSiegelThetaSeriesTerms
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardToMultisetEqDegree
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumPrincipalTorusAtOrthonormalFrame

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.CharLink

noncomputable section

variable {n g : ℕ}

def chi (a b : Fin n → Fin g → ℚ) : TF n g := fun m =>
  if ∀ k i, IsIntegral ℤ (m k i - a k i) then cexp (2 * π * I * ((∑ k, m k ⬝ᵥ b k : ℚ) : ℂ)) else 0

theorem isIntegral_iff_int (q : ℚ) : IsIntegral ℤ q ↔ ∃ z : ℤ, (z : ℚ) = q :=
  IsIntegrallyClosed.isIntegral_iff

theorem exists_den (a : Fin n → Fin g → ℚ) :
    ∃ R : ℕ, 0 < R ∧ ∀ k i, ∃ z : ℤ, (z : ℚ) = R * a k i := by
  refine ⟨∏ p : Fin n × Fin g, (a p.1 p.2).den, Finset.prod_pos fun p _ => (a p.1 p.2).den_pos,
    fun k i => ?_⟩
  obtain ⟨c, hc⟩ : (a k i).den ∣ ∏ p : Fin n × Fin g, (a p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : Fin n × Fin g => (a p.1 p.2).den) (Finset.mem_univ (k, i))
  refine ⟨c * (a k i).num, ?_⟩
  rw [hc]
  push_cast
  rw [← Rat.den_mul_eq_num]
  ring

theorem isSB_chi (a b : Fin n → Fin g → ℚ) : IsSB (chi a b) := by
  obtain ⟨R, hR, ha⟩ := exists_den a
  obtain ⟨S, hS, hb⟩ := exists_den b
  choose u hu using ha
  choose v hv using hb
  refine ⟨R * S, Nat.mul_pos hR hS, fun x hx k i => ?_, fun x y hy => ?_⟩
  · have h : ∀ k i, IsIntegral ℤ (x k i - a k i) := by
      by_contra h
      exact hx (if_neg h)
    obtain ⟨z, hz⟩ := (isIntegral_iff_int _).1 (h k i)
    refine (isIntegral_iff_int _).2 ⟨R * S * z + S * u k i, ?_⟩
    simp only [Matrix.smul_apply, smul_eq_mul]
    push_cast
    rw [hz, hu]
    ring
  · choose w hw using fun k i => (isIntegral_iff_int _).1 (hy k i)
    have h1 : (∀ k i, IsIntegral ℤ ((x + ((R * S : ℕ) : ℚ) • y) k i - a k i)) ↔
        ∀ k i, IsIntegral ℤ (x k i - a k i) := by
      refine forall₂_congr fun k i => ?_
      simp only [isIntegral_iff_int, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← hw]
      constructor
      · rintro ⟨z, hz⟩
        exact ⟨z - R * S * w k i, by push_cast at hz ⊢; linarith⟩
      · rintro ⟨z, hz⟩
        exact ⟨z + R * S * w k i, by push_cast; linarith⟩
    have h2 : ∑ k, (x + ((R * S : ℕ) : ℚ) • y) k ⬝ᵥ b k =
        ∑ k, x k ⬝ᵥ b k + ((∑ k, ∑ i, R * w k i * v k i : ℤ) : ℚ) := by
      push_cast
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [dotProduct, ← Finset.sum_add_distrib, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, hw, hv]
      exact Finset.sum_congr rfl fun i _ => by ring
    unfold chi
    rw [if_congr h1 rfl rfl, h2, Rat.cast_add, mul_add, Complex.exp_add, Rat.cast_intCast,
      mul_comm (2 * π * I) ((_ : ℤ) : ℂ), Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem thS_chi (a b : Fin n → Fin g → ℚ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : (τ.map Complex.im).PosDef) (ζ : Fin n → Fin g → ℂ) :
    thS (chi a b) τ ζ = ∏ k, Geo.Tor.thetaChar τ (fun i => ((a k i : ℝ) : ℂ))
      (fun i => ((b k i : ℝ) : ℂ)) (ζ k) := by
  have h := CanTh.hasSum_prod_thTerm (τ := fun _ : Fin n => τ)
    (fun _ => CanTh.mem_thetaDomain hτ) (fun k i => (a k i : ℝ)) (fun k i => (b k i : ℝ)) ζ
  rw [← h.tsum_eq, thS]
  let f : (Fin n → Fin g → ℤ) → Matrix (Fin n) (Fin g) ℚ := fun m k i => m k i + a k i
  have hf : Function.Injective f := fun m m' e => by
    funext k i
    have := congrFun (congrFun e k) i
    simp only [f, add_left_inj] at this
    exact_mod_cast this
  rw [← hf.tsum_eq]
  · refine tsum_congr fun m => ?_
    have h1 : ∀ k i, IsIntegral ℤ (f m k i - a k i) := fun k i =>
      (isIntegral_iff_int _).2 ⟨m k i, by simp [f]⟩
    simp only [CanTh.thTerm]
    rw [chi, if_pos h1, ← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    have h2 : ∀ k, ((fun i => (m k i : ℂ)) + fun i => (((a k i : ℚ) : ℝ) : ℂ)) = qv (f m k) :=
      fun k => by funext i; simp [qv, f]
    have h3 : ∀ k, ((f m k ⬝ᵥ b k : ℚ) : ℂ) = qv (f m k) ⬝ᵥ fun i => (((b k i : ℚ) : ℝ) : ℂ) :=
      fun k => by simp [qv, dotProduct]
    simp only [h2, Rat.cast_sum, h3, dotProduct_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  · intro x hx
    have h1 : ∀ k i, IsIntegral ℤ (x k i - a k i) := by
      by_contra h
      exact hx (by simp only [chi, if_neg h, zero_mul])
    choose z hz using fun k i => (isIntegral_iff_int _).1 (h1 k i)
    exact ⟨z, by ext k i; simp [f, hz]⟩

def spanChi (n g : ℕ) : Submodule ℂ (TF n g) :=
  Submodule.span ℂ (Set.range fun p : (Fin n → Fin g → ℚ) × (Fin n → Fin g → ℚ) => chi p.1 p.2)

theorem mul_exp_mem {f : TF n g} (hf : f ∈ spanChi n g) (b : Fin n → Fin g → ℚ) :
    (fun m => f m * cexp (2 * π * I * ((∑ k, m k ⬝ᵥ b k : ℚ) : ℂ))) ∈ spanChi n g := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine Submodule.subset_span ⟨(p.1, p.2 + b), funext fun m => ?_⟩
    simp only [chi]
    split_ifs
    · rw [← Complex.exp_add]
      simp only [Pi.add_apply, dotProduct_add, Finset.sum_add_distrib, Rat.cast_add, mul_add]
    · rw [zero_mul]
  | zero => convert (spanChi n g).zero_mem using 1; funext m; simp
  | add x y _ _ hx hy => convert (spanChi n g).add_mem hx hy using 1; funext m; simp [add_mul]
  | smul c x _ hx => convert (spanChi n g).smul_mem c hx using 1; funext m; simp [mul_assoc]

def avg (R : ℕ) (q : ℚ) : ℂ := (R : ℂ)⁻¹ * ∑ s ∈ Finset.range R, cexp (2 * π * I * (q / R)) ^ s

theorem avg_int {R : ℕ} (hR : 0 < R) (z : ℤ) : avg R z = if (R : ℤ) ∣ z then 1 else 0 := by
  have hq : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have h1 : cexp (2 * π * I * ((z : ℚ) / R)) = 1 ↔ (R : ℤ) ∣ z := by
    rw [Complex.exp_eq_one_iff]
    refine exists_congr fun c => ?_
    rw [mul_comm (c : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero, div_eq_iff hq, mul_comm]
    norm_cast
  unfold avg
  split_ifs with h
  · rw [h1.2 h]
    simp [hq]
  · rw [geom_sum_eq (mt h1.1 h), ← Complex.exp_nat_mul]
    have : (R : ℂ) * (2 * π * I * ((z : ℚ) / R)) = z * (2 * π * I) := by
      push_cast
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
    simp

theorem mul_avg_mem {f : TF n g} (hf : f ∈ spanChi n g) (R : ℕ) (c : ℚ) (k : Fin n) (i : Fin g) :
    (fun m => f m * avg R (m k i - c)) ∈ spanChi n g := by
  have h := (spanChi n g).smul_mem (R : ℂ)⁻¹ ((spanChi n g).sum_mem fun s (_ : s ∈ Finset.range R) =>
    (spanChi n g).smul_mem (cexp (2 * π * I * (-c / R)) ^ s)
      (mul_exp_mem hf (Pi.single k (Pi.single i ((s : ℚ) / R)))))
  convert h using 1
  funext m
  have h1 : ∀ t : ℚ, ∑ l, m l ⬝ᵥ (Pi.single k (Pi.single i t) : Fin n → Fin g → ℚ) l =
      m k i * t := fun t => by
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      simp [hl]
    · simp
  simp only [avg, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_left_comm (f m), mul_left_comm (_ ^ s) (f m), ← Complex.exp_nat_mul,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 3
  push_cast
  ring

theorem ind_mem {R : ℕ} (hR : 0 < R) (c : Fin n → Fin g → ℚ) :
    (fun m : Matrix (Fin n) (Fin g) ℚ =>
      if ∀ k i, ∃ z : ℤ, m k i - c k i = R * z then (1 : ℂ) else 0) ∈ spanChi n g := by
  have h : ∀ s : Finset (Fin n × Fin g),
      (fun m => chi c 0 m * ∏ p ∈ s, avg R (m p.1 p.2 - c p.1 p.2)) ∈ spanChi n g := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, mul_one]
      exact Submodule.subset_span ⟨(c, 0), rfl⟩
    | insert p s hp ih =>
      convert mul_avg_mem ih R (c p.1 p.2) p.1 p.2 using 2 with m
      rw [Finset.prod_insert hp]
      ring
  convert h Finset.univ using 2 with m
  by_cases h1 : ∀ k i, IsIntegral ℤ (m k i - c k i)
  · choose z hz using fun k i => (isIntegral_iff_int _).1 (h1 k i)
    have h2 : (∀ k i, ∃ w : ℤ, m k i - c k i = R * w) ↔ ∀ p : Fin n × Fin g, (R : ℤ) ∣ z p.1 p.2 := by
      rw [Prod.forall]
      refine forall₂_congr fun k i => exists_congr fun w => ?_
      rw [← hz]
      norm_cast
    rw [chi, if_pos h1, if_congr h2 rfl rfl]
    simp only [← hz, avg_int hR, Finset.prod_boole]
    simp
  · rw [chi, if_neg h1, zero_mul, if_neg]
    intro h2
    refine h1 fun k i => ?_
    obtain ⟨z, hz⟩ := h2 k i
    exact (isIntegral_iff_int _).2 ⟨R * z, by rw [hz]; push_cast; rfl⟩

theorem mem_spanChi {φ : TF n g} (hφ : IsSB φ) : φ ∈ spanChi n g := by
  obtain ⟨R, hR, h0, hp⟩ := hφ
  have hq : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hz : (0 : ℤ) < R * R := by positivity
  let T : Finset (Fin n → Fin g → ℤ) :=
    Fintype.piFinset fun _ => Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) (R * R)
  have h := (spanChi n g).sum_mem fun c (_ : c ∈ T) => (spanChi n g).smul_mem
    (φ fun k i => (c k i : ℚ) / R) (ind_mem hR fun k i => (c k i : ℚ) / R)
  convert h using 1
  funext m
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h1 : IntM ((R : ℚ) • m)
  · choose z hzm using fun k i => (isIntegral_iff_int _).1 (h1 k i)
    simp only [Matrix.smul_apply, smul_eq_mul] at hzm
    have h2 : ∀ k i, m k i - ((z k i % (R * R) : ℤ) : ℚ) / R = R * ((z k i / (R * R) : ℤ) : ℚ) := by
      intro k i
      rw [Int.emod_def]
      generalize z k i / (R * R) = w
      push_cast
      rw [hzm]
      field_simp
      ring
    rw [Finset.sum_eq_single_of_mem (fun k i => z k i % (R * R))]
    · rw [if_pos fun k i => ⟨_, h2 k i⟩, mul_one,
        ← hp (fun k i => ((z k i % (R * R) : ℤ) : ℚ) / R) (fun k i => ((z k i / (R * R) : ℤ) : ℚ))
          fun k i => (isIntegral_iff_int _).2 ⟨_, rfl⟩]
      congr 1
      ext k i
      change m k i = ((z k i % (R * R) : ℤ) : ℚ) / R + R * ((z k i / (R * R) : ℤ) : ℚ)
      linear_combination h2 k i
    · simp only [T, Fintype.mem_piFinset, Finset.mem_Ico]
      exact fun k i => ⟨Int.emod_nonneg _ hz.ne', Int.emod_lt_of_pos _ hz⟩
    · intro c hc hne
      rw [if_neg, mul_zero]
      intro h3
      refine hne (funext fun k => funext fun i => ?_)
      simp only [T, Fintype.mem_piFinset, Finset.mem_Ico] at hc
      obtain ⟨w, hw⟩ := h3 k i
      have h4 : z k i = c k i + R * R * w := by
        have : (z k i : ℚ) = c k i + R * R * w := by
          rw [hzm]
          field_simp at hw
          linear_combination hw
        exact_mod_cast this
      rw [h4, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (hc k i).1 (hc k i).2]
  · rw [not_not.1 (mt (h0 m) h1), Finset.sum_eq_zero]
    intro c _
    rw [if_neg, mul_zero]
    intro h3
    refine h1 fun k i => ?_
    obtain ⟨w, hw⟩ := h3 k i
    refine (isIntegral_iff_int _).2 ⟨c k i + R * R * w, ?_⟩
    simp only [Matrix.smul_apply, smul_eq_mul]
    push_cast
    field_simp at hw
    linear_combination -hw

theorem thS_sum {m : ℕ} (t : Fin m → ℂ) (φ : Fin m → TF n g) (hφ : ∀ j, IsSB (φ j))
    {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ Siegel (Fin g)) (ζ : Fin n → Fin g → ℂ) :
    thS (∑ j, t j • φ j) τ ζ = ∑ j, t j * thS (φ j) τ ζ := by
  unfold thS
  simp only [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun j _ =>
    (SiegelSum.summable_norm_thetaTerm _ _ (φ j) (hφ j) τ hτ ζ).of_norm.mul_left (t j)]
  refine tsum_congr fun x => ?_
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r q0 : ℕ} {X : Data E r}
  (hr : X.p0 + q0 = r) {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem thA_chi (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (a b : Fin n → Fin g → ℚ)
    (z : Fin n → Fin g → ℂ) :
    thA X bas idx (chi a b) x z = (hMat X bas idx x).det ^ (n / 2) *
      ∏ k, canFn X bas idx (fun i => (a k i : ℝ)) (fun i => (b k i : ℝ)) x (z k) := by
  rw [thA, thS_chi a b (tauMat_im_posDef idx hs hx), Finset.mul_sum, Complex.exp_sum, mul_assoc,
    ← Finset.prod_mul_distrib]
  rfl

theorem theta_sum_smul_chi (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {m : ℕ}
    (a b : Fin m → Fin n → Fin g → ℚ) (t : Fin m → ℂ) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thP X hr bas idx (∑ j, t j • chi (a j) (b j)) P x =
      ∑ j, t j * thFr X hr bas idx n (fun k i => (a j k i : ℝ)) (fun k i => (b j k i : ℝ)) P x := by
  have h : thA X bas idx (∑ j, t j • chi (a j) (b j)) x = fun z =>
      ∑ j, (t j * (hMat X bas idx x).det ^ (n / 2)) *
        ∏ k, canFn X bas idx (fun i => (a j k i : ℝ)) (fun i => (b j k i : ℝ)) x (z k) := by
    funext z
    simp only [mul_assoc, ← thA_chi idx hs hx]
    simp only [thA]
    rw [thS_sum t _ (fun j => isSB_chi _ _)
      ⟨tauMat_isSymm idx hs hx, tauMat_im_posDef idx hs hx⟩, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [thP, h, Jet.polyDeriv_sum_fun P _ _ _
    (fun j (z : Fin n → Fin g → ℂ) =>
      ∏ k, canFn X bas idx (fun i => (a j k i : ℝ)) (fun i => (b j k i : ℝ)) x (z k))
    fun j _ => differentiable_prod_col fun k => differentiable_canFn idx hs hx _ _]
  exact Finset.sum_congr rfl fun j _ => by rw [thFr, mul_assoc]

theorem harmonicTheta_eq_sum_thetaCharacteristic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → (∀ (a b : Fin n → Fin g → ℚ), ∃ φ : TF n g, IsSB φ ∧ (∀ m : Matrix (Fin n) (Fin g) ℚ, φ m = if ∀ k i, IsIntegral ℤ (m k i - a k i) then cexp (2 * π * I * ((∑ k, m k ⬝ᵥ b k : ℚ) : ℂ)) else 0) ∧ ∀ P, ∀ x ∈ X.dom, thP X hr bas idx φ P x = thFr X hr bas idx n (fun k i => (a k i : ℝ)) (fun k i => (b k i : ℝ)) P x) ∧ ∀ φ : TF n g, IsSB φ → ∃ (m : ℕ) (a b : Fin m → Fin n → Fin g → ℚ) (t : Fin m → ℂ), ∀ P, ∀ x ∈ X.dom, thP X hr bas idx φ P x = ∑ j, t j * thFr X hr bas idx n (fun k i => (a j k i : ℝ)) (fun k i => (b j k i : ℝ)) P x := by
  intro E _ _ _ r X g q0 hr bas idx n hs _
  refine ⟨fun a b => ⟨chi a b, isSB_chi a b, fun _ => rfl, fun P x hx => ?_⟩, fun φ hφ => ?_⟩
  · simpa using theta_sum_smul_chi hr idx hs hx (fun _ : Fin 1 => a) (fun _ => b) (fun _ => 1) P
  · obtain ⟨m, t, f, rfl⟩ := Submodule.mem_span_set'.1 (mem_spanChi hφ)
    choose p hp using fun j => (f j).2
    refine ⟨m, fun j => (p j).1, fun j => (p j).2, t, fun P x hx => ?_⟩
    rw [← theta_sum_smul_chi hr idx hs hx]
    simp only [hp]

end

end GlobalTheory.SW.CharLink
