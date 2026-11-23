import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrtStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValuesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugateStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaAlgebraic

section Germs

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type}

inductive Gen (v : ι → V) : (V → ℂ) → Prop
  | const (c : ℂ) (hc : c ∈ Qbar) : Gen v (fun _ => c)
  | lin (g : ℂ → ℂ) (hg : Differentiable ℂ g) (hc : ∀ n, iteratedDeriv n g 0 ∈ Qbar)
      (l : V →L[ℂ] ℂ) (hl : ∀ k, l (v k) ∈ Qbar) : Gen v (fun z => g (l z))
  | add (F G : V → ℂ) (hF : Gen v F) (hG : Gen v G) : Gen v (fun z => F z + G z)
  | mul (F G : V → ℂ) (hF : Gen v F) (hG : Gen v G) : Gen v (fun z => F z * G z)

variable {v : ι → V}

theorem Gen.contDiff {G : V → ℂ} (h : Gen v G) (n : WithTop ℕ∞) : ContDiff ℂ n G := by
  induction h with
  | const c _ => exact contDiff_const
  | lin g hg _ l _ => exact hg.contDiff.comp l.contDiff
  | add F G _ _ hF hG => exact hF.add hG
  | mul F G _ _ hF hG => exact hF.mul hG

theorem Gen.differentiable {G : V → ℂ} (h : Gen v G) : Differentiable ℂ G :=
  (h.contDiff 1).differentiable (by simp)

theorem Gen.val_mem {G : V → ℂ} (h : Gen v G) : G 0 ∈ Qbar := by
  induction h with
  | const c hc => exact hc
  | lin g _ hc l _ => simpa using hc 0
  | add F G _ _ hF hG => exact add_mem hF hG
  | mul F G _ _ hF hG => exact mul_mem hF hG

theorem Gen.deriv {G : V → ℂ} (h : Gen v G) (k : ι) : Gen v (fun y => fderiv ℂ G y (v k)) := by
  induction h with
  | const c hc => simpa using Gen.const (v := v) 0 (zero_mem _)
  | lin g hg hc l hl =>
    have e : (fun y => fderiv ℂ (fun z => g (l z)) y (v k)) =
        fun y => _root_.deriv g (l y) * l (v k) := by
      funext y
      have := ((hg (l y)).hasDerivAt.comp_hasFDerivAt y l.hasFDerivAt).fderiv
      rw [show (fun z => g (l z)) = g ∘ l from rfl, this]
      simp
    rw [e]
    refine Gen.mul _ _ (Gen.lin _ hg.deriv (fun n => ?_) l hl) (Gen.const _ (hl k))
    rw [← iteratedDeriv_succ']
    exact hc _
  | add F G hF hG iF iG =>
    have e : (fun y => fderiv ℂ (fun z => F z + G z) y (v k)) =
        fun y => fderiv ℂ F y (v k) + fderiv ℂ G y (v k) := by
      funext y
      rw [fderiv_fun_add (hF.differentiable y) (hG.differentiable y)]
      simp
    rw [e]
    exact Gen.add _ _ iF iG
  | mul F G hF hG iF iG =>
    have e : (fun y => fderiv ℂ (fun z => F z * G z) y (v k)) =
        fun y => F y * fderiv ℂ G y (v k) + G y * fderiv ℂ F y (v k) := by
      funext y
      rw [fderiv_fun_mul (hF.differentiable y) (hG.differentiable y)]
      simp
    rw [e]
    exact Gen.add _ _ (Gen.mul _ _ hF iG) (Gen.mul _ _ hG iF)

theorem Gen.iterated_mem (n : ℕ) : ∀ {G : V → ℂ}, Gen v G → ∀ κ : Fin n → ι,
    iteratedFDeriv ℂ n G 0 (fun i => v (κ i)) ∈ Qbar := by
  induction n with
  | zero => intro G h κ; simpa using h.val_mem
  | succ n ih =>
    intro G h κ
    rw [iteratedFDeriv_succ_apply_right,
      ← iteratedFDeriv_clm_apply_const_apply (n := n) ((h.contDiff (n + 1)).fderiv_right le_rfl) le_rfl]
    exact ih (h.deriv (κ (Fin.last n))) (fun i => κ i.castSucc)

theorem Gen.sum {α : Type} (s : Finset α) (F : α → V → ℂ) (h : ∀ a ∈ s, Gen v (F a)) :
    Gen v (fun z => ∑ a ∈ s, F a z) := by
  induction s using Finset.induction_on with
  | empty => simpa using Gen.const (v := v) 0 (zero_mem _)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact Gen.add _ _ (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem Gen.prod {α : Type} (s : Finset α) (F : α → V → ℂ) (h : ∀ a ∈ s, Gen v (F a)) :
    Gen v (fun z => ∏ a ∈ s, F a z) := by
  induction s using Finset.induction_on with
  | empty => simpa using Gen.const (v := v) 1 (one_mem _)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact Gen.mul _ _ (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

end Germs

theorem exp_rat_mem (q : ℚ) : Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  refine IsAlgebraic.of_pow (n := 2 * q.den) (by have := q.den_pos; omega) ?_
  have : Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) ^ (2 * q.den) = 1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I q.num]
    congr 1
    have : (q.num : ℂ) = q * q.den := by exact_mod_cast (Rat.mul_den_eq_num q).symm
    rw [this]; push_cast; ring
  rw [this]; exact isAlgebraic_one

theorem sqrt_nat_mem (n : ℕ) : ((Real.sqrt (n : ℝ) : ℝ) : ℂ) ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  refine IsAlgebraic.of_pow (n := 2) (by norm_num) ?_
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa using isAlgebraic_nat (R := ℚ) (A := ℂ) n

theorem hom_mem {E : Type} [Field E] [NumberField E] (σ : E →+* ℂ) (x : E) : σ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom

variable {D : D7} {N N' : ℕ}

theorem Gen.coefIn {G : VC D N N' → ℂ} (h : Gen (coordV D) G) : CoefIn D G Qbar := by
  intro α
  refine div_mem (h.iterated_mem _ _) ?_
  exact prod_mem fun k _ => natCast_mem _ _

def sq (z w : VC D N N') : ℂ := ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)

theorem sq_smul_left (c : ℂ) (z w : VC D N N') : sq (c • z) w = c * sq z w := by
  simp [sq, Finset.mul_sum, mul_assoc]

theorem sq_add_left (z z' w : VC D N N') : sq (z + z') w = sq z w + sq z' w := by
  simp [sq, add_mul, Finset.sum_add_distrib]

theorem sq_conj (z w : VC D N N') : sq w z = (starRingEnd ℂ) (sq z w) := by
  simp [sq, map_sum, mul_comm]

theorem sq_smul_right (c : ℂ) (z w : VC D N N') : sq z (c • w) = sq z w * (starRingEnd ℂ) c := by
  rw [sq_conj, sq_smul_left, map_mul, ← sq_conj, mul_comm]

theorem sq_add_right (z w w' : VC D N N') : sq z (w + w') = sq z w + sq z w' := by
  simp [sq, mul_add, Finset.sum_add_distrib]

def sqL (w : VC D N N') : VC D N N' →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => sq z w
      map_add' := fun z z' => sq_add_left z z' w
      map_smul' := fun c z => sq_smul_left c z w }

theorem sqL_apply (z w : VC D N N') : sqL w z = sq z w := rfl

theorem sq_sum_left {α : Type} (s : Finset α) (x : α → VC D N N') (w : VC D N N') :
    sq (∑ a ∈ s, x a) w = ∑ a ∈ s, sq (x a) w := map_sum (sqL w) x s

theorem sq_sum_right {α : Type} (s : Finset α) (x : α → VC D N N') (w : VC D N N') :
    sq w (∑ a ∈ s, x a) = ∑ a ∈ s, sq w (x a) := by
  rw [sq_conj, sq_sum_left, map_sum]
  exact Finset.sum_congr rfl fun a _ => (sq_conj _ _).symm

theorem Hf_eq (T : Tor D) (z w : VC D N N') : Hf D T z w = sq z w / (area T.abelian₂ : ℂ) := rfl

theorem Hf_conj (T : Tor D) (z w : VC D N N') : Hf D T w z = (starRingEnd ℂ) (Hf D T z w) := by
  rw [Hf_eq, Hf_eq, sq_conj, map_div₀, Complex.conj_ofReal]

theorem Hf_nsmul (T : Tor D) (m n : ℕ) (z w : VC D N N') :
    Hf D T (m • z) (n • w) = (m * n : ℝ) * Hf D T z w := by
  rw [Hf_eq, Hf_eq, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, sq_smul_left,
    sq_smul_right]
  simp only [map_natCast]
  push_cast
  ring

theorem qH_nsmul (T : Tor D) (m : ℕ) (z : VC D N N') : qH D T (m • z) = (m : ℝ) ^ 2 * qH D T z := by
  rw [qH, qH, Hf_nsmul, Complex.re_ofReal_mul]
  ring

theorem U_zero (T : Tor D) (G : VC D N N' → ℂ) : U D T 0 G = G := by
  funext z
  simp [U, Hf]

theorem U_U (T : Tor D) (x t : VC D N N') (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (U D T t G) z =
      Complex.exp ((Real.pi : ℂ) * Complex.I * (-((Hf D T x t).im : ℂ))) * U D T (x + t) G z := by
  have h : Complex.I * ((Hf D T x t).im : ℂ) = (Hf D T x t - Hf D T t x) / 2 := by
    rw [Hf_conj T x t, Complex.sub_conj]
    push_cast
    ring
  simp only [U]
  rw [add_assoc z x t, mul_assoc (G _), ← Complex.exp_add, mul_left_comm _ (G _), ← Complex.exp_add]
  congr 2
  rw [mul_neg, mul_assoc, h]
  simp only [Hf_eq, sq_add_left, sq_add_right]
  ring

variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)

theorem embV_apply (x : Matrix (Fin N') (Fin N) D.host.E) (τ i j) :
    embV D (tor0 D cc δ) x τ i j = embT D τ (x i j) := rfl

theorem sq_embV (hG : admG1 D) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    sq (embV D (tor0 D cc δ) x) (embV D (tor0 D cc δ) y) =
      D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) := by
  rw [hYY, ← hG.2]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [map_sum, map_mul, embV_apply]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Formalism.HC.HostAx.conjE_apply D.host.toHostAx]

theorem embV_smul (hG : admG1 D) (a : D.host.K) (x : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (a • x) = D.host.φ₀ (a : D.host.E) • embV D (tor0 D cc δ) x := by
  funext τ i j
  simp only [embV_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, ← hG.1 τ a, ← map_mul]
  rfl

theorem embV_sum {ι : Type} (s : Finset ι) (x : ι → Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (∑ i ∈ s, x i) = ∑ i ∈ s, embV D (tor0 D cc δ) (x i) := by
  funext τ i j
  simp [embV_apply, Matrix.sum_apply, Finset.sum_apply]

theorem lam_mul (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ lamOf D cc δ) :
    D.host.φ₀ ((a : D.host.K) : D.host.E) * w ∈ lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
    push_cast [map_mul]
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem la_mul (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (a : 𝓞 D.host.K) {x : VC D N N'}
    (hx : x ∈ La D (tor0 D cc δ) L L') :
    D.host.φ₀ ((a : D.host.K) : D.host.E) • x ∈ La D (tor0 D cc δ) L L' := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨_, lam_mul cc δ a hw, A, hA, by rw [smul_smul]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

def sat {A : Type} [AddCommGroup A] (B : AddSubgroup A) : AddSubgroup A where
  carrier := {x | ∃ m : ℕ, 0 < m ∧ m • x ∈ B}
  zero_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro x y ⟨m, hm, hx⟩ ⟨n, hn, hy⟩
    refine ⟨m * n, mul_pos hm hn, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx n
    · rw [mul_smul]; exact nsmul_mem hy m
  neg_mem' := by
    rintro x ⟨m, hm, hx⟩
    exact ⟨m, hm, by rw [smul_neg]; exact neg_mem hx⟩

theorem sat_of_nsmul {A : Type} [AddCommGroup A] {B : AddSubgroup A} {x : A} {m : ℕ} (hm : 0 < m)
    (h : m • x ∈ sat B) : x ∈ sat B := by
  obtain ⟨n, hn, h⟩ := h
  exact ⟨n * m, mul_pos hn hm, by rwa [mul_smul]⟩

theorem rationalLatticePoint_mul_imagQuadratic (a : D.host.K) {w : ℂ} (hw : InRationalLattice (lamOf D cc δ) w) :
    InRationalLattice (lamOf D cc δ) (w * D.host.φ₀ (a : D.host.E)) := by
  obtain ⟨m, hm, hw⟩ := hw
  have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ _).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hi⟩ := ha.exists_integral_multiple
  have hi' : IsIntegral ℤ ((y.natAbs : D.host.K) * a) := by
    rcases Int.natAbs_eq y with e | e
    · rw [e] at hi; simpa using hi
    · rw [e] at hi; simpa using hi.neg
  refine ⟨m * y.natAbs, mul_pos hm (Int.natAbs_pos.2 hy), ?_⟩
  have := lam_mul cc δ ⟨_, hi'⟩ hw
  convert this using 1
  change _ = D.host.φ₀ ((((y.natAbs : D.host.K) * a : D.host.K)) : D.host.E) * _
  push_cast [map_mul, map_natCast]
  ring

theorem delta_mem_rationalIdealLattice (hc : cc ≠ ⊥) : InRationalLattice (lamOf D cc δ) δ := by
  refine ⟨Ideal.absNorm cc, Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), ?_⟩
  refine AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, ?_⟩
  simp [mul_comm]

variable {r : ℕ} {b : Fin r → Matrix (Fin N') (Fin N) D.host.E}

theorem smul_embV_mem (hG : admG1 D) (hb : OnB D b) {w : ℂ} (hw : InRationalLattice (lamOf D cc δ) w)
    (A : Matrix (Fin N') (Fin N) D.host.E) :
    w • embV D (tor0 D cc δ) A ∈ sat (LaB D (tor0 D cc δ) b) := by
  have hA : A ∈ Submodule.span D.host.K (Set.range b) := by rw [hb.2]; trivial
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hA
  rw [embV_sum, Finset.smul_sum]
  refine sum_mem fun j _ => ?_
  rw [embV_smul cc δ hG, smul_smul]
  obtain ⟨m, hm, h⟩ := rationalLatticePoint_mul_imagQuadratic cc δ (a j) hw
  refine ⟨m, hm, AddSubgroup.subset_closure ⟨_, h, j, ?_⟩⟩
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]

theorem la_le (hG : admG1 D) (hb : OnB D b) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    La D (tor0 D cc δ) L L' ≤ sat (LaB D (tor0 D cc δ) b) := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨w, hw, A, -, rfl⟩
  exact smul_embV_mem cc δ hG hb ⟨1, one_pos, by rw [Nat.cast_one, one_mul]; exact hw⟩ A

theorem exists_coords {x : VC D N N'} (hx : x ∈ sat (LaB D (tor0 D cc δ) b)) :
    ∃ c : Fin r → ℂ, (∀ j, InRationalLattice (lamOf D cc δ) (c j)) ∧
      x = ∑ j, c j • embV D (tor0 D cc δ) (b j) := by
  obtain ⟨m, hm, hx⟩ := hx
  have key : ∀ y ∈ LaB D (tor0 D cc δ) b, ∃ c : Fin r → ℂ, (∀ j, c j ∈ lamOf D cc δ) ∧
      y = ∑ j, c j • embV D (tor0 D cc δ) (b j) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨w, hw, j, rfl⟩ := hw
      refine ⟨Pi.single j w, fun i => ?_, ?_⟩
      · by_cases h : i = j
        · subst h; rw [Pi.single_eq_same]; exact hw
        · simp [h]
      · rw [Finset.sum_eq_single j] <;> simp +contextual
    | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', fun j => add_mem (hc j) (hc' j), by simp [add_smul, Finset.sum_add_distrib]⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, fun j => neg_mem (hc j), by simp⟩
  obtain ⟨c, hc, e⟩ := key _ hx
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨fun j => (m : ℂ)⁻¹ * c j, fun j => ⟨m, hm, by simpa [hm'] using hc j⟩, ?_⟩
  simp only [mul_smul, ← Finset.smul_sum]
  rw [← e, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hm']

theorem coordB_eq (T : Tor D) (j : Fin r) (z : VC D N N') :
    coordB D T b j z = sq z (embV D T (b j)) := rfl

theorem U_pullB (hG : admG1 D) (hb : OnB D b) (c : Fin r → ℂ) (g : ℂ → ℂ) (z : VC D N N') :
    U D (tor0 D cc δ) (∑ j, c j • embV D (tor0 D cc δ) (b j)) (pullB D (tor0 D cc δ) b g) z =
      ∏ j, U1 (lamOf D cc δ) (c j) g (coordB D (tor0 D cc δ) b j z) := by
  have h1 : ∀ j, sq (∑ j, c j • embV D (tor0 D cc δ) (b j)) (embV D (tor0 D cc δ) (b j)) = c j := by
    intro j
    rw [sq_sum_left, Finset.sum_eq_single j]
    · rw [sq_smul_left, sq_embV cc δ hG, hb.1]; simp
    · intro i _ hi
      rw [sq_smul_left, sq_embV cc δ hG, hb.1]; simp [hi]
    · simp
  have h2 : ∀ y, sq y (∑ j, c j • embV D (tor0 D cc δ) (b j)) =
      ∑ j, sq y (embV D (tor0 D cc δ) (b j)) * (starRingEnd ℂ) (c j) := by
    intro y
    rw [sq_sum_right]
    exact Finset.sum_congr rfl fun j _ => sq_smul_right _ _ _
  simp only [U, U1, pullB, coordB_eq, Finset.prod_mul_distrib, ← Complex.exp_sum, sq_add_left, h1,
    Hf_eq, h2]
  congr 2
  simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ = _ / (area (tor0 D cc δ).abelian₂ : ℂ) - _ / (2 * (area (tor0 D cc δ).abelian₂ : ℂ))
  ring

theorem exists_pair (hG : admG1 D) (hC : Crv D cc δ) :
    ∃ P : PeriodPair, ∀ z, z ∈ lamOf D cc δ ↔ z ∈ P.lattice :=
  GlobalTheory.OddTheta.exists_periodPair _ (GlobalTheory.T.idealPeriodLattice_of_curveDatum D hG cc δ hC).1

theorem im_Hf (T : Tor D) (z w : VC D N N') : (Hf D T z w).im = (sq z w).im / area T.abelian₂ := by
  rw [Hf_eq, Complex.div_ofReal_im]

theorem integral_of_gen (hG : admG1 D) (hC : Crv D cc δ)
    (S : Set (Matrix (Fin N') (Fin N) D.host.E))
    (hS : ∀ x ∈ S, ∀ y ∈ S, hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range)
    (A : AddSubgroup (VC D N N'))
    (hA : A = AddSubgroup.closure
      {z | ∃ w ∈ lamOf D cc δ, ∃ x ∈ S, z = w • embV D (tor0 D cc δ) x}) :
    (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) ∧
      ∀ x ∈ A, ∃ m : ℤ, qH D (tor0 D cc δ) x = m := by
  obtain ⟨L, hL⟩ := exists_pair cc δ hG hC
  obtain ⟨-, hdual⟩ := GlobalTheory.T.latticeCovolume_pos_and_selfDual L _ hL
  have hLam : (tor0 D cc δ).abelian₂ = lamOf D cc δ := rfl
  have hsq : ∀ z ∈ A, ∀ x ∈ S, sq z (embV D (tor0 D cc δ) x) ∈ lamOf D cc δ := by
    intro z hz x hx
    rw [hA] at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨w, hw, x', hx', rfl⟩ := hz
      obtain ⟨a, ha⟩ := hS x' hx' x hx
      rw [sq_smul_left, sq_embV cc δ hG, ← ha, mul_comm]
      exact lam_mul cc δ a hw
    | zero => simp [sq]
    | add a b _ _ ha hb => rw [sq_add_left]; exact add_mem ha hb
    | neg a _ ha => rw [← sqL_apply, map_neg]; exact neg_mem ha
  have hint : ∀ z, (∀ x ∈ S, sq z (embV D (tor0 D cc δ) x) ∈ lamOf D cc δ) →
      ∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) z y).im = m := by
    intro z hz u hu
    rw [hA] at hu
    simp only [im_Hf, hLam]
    induction hu using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨w, hw, x, hx, rfl⟩ := hu
      rw [sq_smul_right]
      exact (hdual _).1 (hz x hx) w hw
    | zero => exact ⟨0, by simp [sq]⟩
    | add a b _ _ ha hb =>
      obtain ⟨m, hm⟩ := ha
      obtain ⟨n, hn⟩ := hb
      exact ⟨m + n, by rw [sq_add_right, Complex.add_im, add_div, hm, hn, Int.cast_add]⟩
    | neg a _ ha =>
      obtain ⟨m, hm⟩ := ha
      have e : sq z (-a) = -sq z a := by simp [sq]
      exact ⟨-m, by rw [e, Complex.neg_im, neg_div, hm, Int.cast_neg]⟩
  refine ⟨fun x hx => hint x (hsq x hx), fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_integer_map_eq_halfOneAddSqrt D
  obtain ⟨m, hm⟩ := hint (w0 D • x) (fun y hy => by
    rw [sq_smul_left, ← ha]
    exact lam_mul cc δ a (hsq x hx _ hy)) x hx
  have h0 : (sq x x).im = 0 := by simp [sq, Complex.im_sum, Complex.mul_conj]
  refine ⟨m, ?_⟩
  rw [← hm, im_Hf, sq_smul_left, qH, Hf_eq, Complex.div_ofReal_re, Complex.mul_im, h0]
  simp [w0]
  ring

theorem integral_laB (hG : admG1 D) (hC : Crv D cc δ) (hb : OnB D b) :
    (∀ x ∈ LaB D (tor0 D cc δ) b, ∀ y ∈ LaB D (tor0 D cc δ) b,
      ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) ∧
      ∀ x ∈ LaB D (tor0 D cc δ) b, ∃ m : ℤ, qH D (tor0 D cc δ) x = m := by
  refine integral_of_gen cc δ hG hC (Set.range b) ?_ _ ?_
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    rw [hb.1 i j]
    split_ifs
    exacts [one_mem _, zero_mem _]
  · unfold LaB
    congr 1
    ext z
    simp [tor0]

theorem integral_la (hG : admG1 D) (hC : Crv D cc δ)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : SD D L) (hL' : SD D L') :
    ∀ x ∈ La D (tor0 D cc δ) L L', ∃ m : ℤ, qH D (tor0 D cc δ) x = m :=
  (integral_of_gen cc δ hG hC {x | x ∈ YYl D L L'}
    (fun x hx y hy => GlobalTheory.T.hermitian_pairing_integral_values D N N' L L' hL hL' x hx y hy) _ rfl).2

def Good (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (G : VC D N N' → ℂ) : Prop :=
  ∀ x ∈ sat (LaB D (tor0 D cc δ) b), Gen (coordV D) (U D (tor0 D cc δ) x G)

variable {cc δ}

theorem Good.coefIn {G : VC D N N' → ℂ} (h : Good cc δ b G) : CoefIn D G Qbar := by
  have := h 0 (zero_mem _)
  rw [U_zero] at this
  exact this.coefIn

theorem Good.const_mul {G : VC D N N' → ℂ} (h : Good cc δ b G) {c : ℂ} (hc : c ∈ Qbar) :
    Good cc δ b (fun z => c * G z) := by
  intro x hx
  have e : U D (tor0 D cc δ) x (fun z => c * G z) = fun z => c * U D (tor0 D cc δ) x G z := by
    funext z; simp only [U, mul_assoc]
  rw [e]
  exact Gen.mul _ _ (Gen.const c hc) (h x hx)

theorem Good.sum {α : Type} (s : Finset α) (F : α → VC D N N' → ℂ)
    (h : ∀ a ∈ s, Good cc δ b (F a)) : Good cc δ b (fun z => ∑ a ∈ s, F a z) := by
  intro x hx
  have e : U D (tor0 D cc δ) x (fun z => ∑ a ∈ s, F a z) =
      fun z => ∑ a ∈ s, U D (tor0 D cc δ) x (F a) z := by
    funext z; simp only [U, Finset.sum_mul]
  rw [e]
  exact Gen.sum s _ fun a ha => h a ha x hx

theorem im_rat (hG : admG1 D) (hC : Crv D cc δ) (hb : OnB D b) {x y : VC D N N'}
    (hx : x ∈ sat (LaB D (tor0 D cc δ) b)) (hy : y ∈ sat (LaB D (tor0 D cc δ) b)) :
    ∃ q : ℚ, (Hf D (tor0 D cc δ) x y).im = q := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨n, hn, hy⟩ := hy
  obtain ⟨k, hk⟩ := (integral_laB cc δ hG hC hb).1 _ hx _ hy
  rw [Hf_nsmul, Complex.im_ofReal_mul] at hk
  refine ⟨k / (m * n), ?_⟩
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  rw [← hk]; field_simp

theorem qH_rat (hG : admG1 D) (hC : Crv D cc δ) (hb : OnB D b) {x : VC D N N'}
    (hx : x ∈ sat (LaB D (tor0 D cc δ) b)) : ∃ q : ℚ, qH D (tor0 D cc δ) x = q := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨k, hk⟩ :=
    (integral_laB cc δ hG hC hb).2 _ hx
  rw [qH_nsmul] at hk
  refine ⟨k / m ^ 2, ?_⟩
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  rw [← hk]; field_simp

theorem Good.transl (hG : admG1 D) (hC : Crv D cc δ) (hb : OnB D b) {G : VC D N N' → ℂ}
    (h : Good cc δ b G) {t : VC D N N'} (ht : t ∈ sat (LaB D (tor0 D cc δ) b)) :
    Good cc δ b (U D (tor0 D cc δ) t G) := by
  intro x hx
  obtain ⟨q, hq⟩ := im_rat hG hC hb hx ht
  have e := funext (U_U (tor0 D cc δ) x t G)
  rw [show U D (tor0 D cc δ) x (U D (tor0 D cc δ) t G) = _ from e, hq]
  refine Gen.mul _ _ (Gen.const _ ?_) (h _ (add_mem hx ht))
  simpa using exp_rat_mem (-q)

theorem Good.iop (hG : admG1 D) (hC : Crv D cc δ) (hb : OnB D b) {G : VC D N N' → ℂ}
    (h : Good cc δ b G) (A₁ A₂ : AddSubgroup (VC D N N'))
    (hA : A₂ ≤ sat (LaB D (tor0 D cc δ) b)) :
    Good cc δ b (Iop D (tor0 D cc δ) A₁ A₂ G) := by
  by_cases hi : (A₁.addSubgroupOf A₂).index = 0
  · have e : Iop D (tor0 D cc δ) A₁ A₂ G = fun z => 0 * G z := by
      funext z; simp [Iop, hi]
    rw [e]
    exact h.const_mul (zero_mem _)
  · haveI : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := Nat.finite_of_card_ne_zero hi
    haveI := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
    unfold Iop
    simp only [finsum_eq_sum_of_fintype]
    refine Good.const_mul (Good.sum _ _ fun q _ => ?_) (inv_mem (sqrt_nat_mem _))
    exact (h.transl hG hC hb (hA (Quotient.out q).2)).const_mul
      (zpow_mem (neg_mem (one_mem _)) _)

theorem differentiable_U1 (Λ : AddSubgroup ℂ) (c : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (U1 Λ c g) := by
  unfold U1
  fun_prop

theorem iteratedDeriv_mem {g : ℂ → ℂ} (h : ∀ n, coef1 g n ∈ Qbar) (n : ℕ) :
    iteratedDeriv n g 0 ∈ Qbar := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have := mul_mem (h n) (natCast_mem Qbar n.factorial)
  rwa [coef1, div_mul_cancel₀ _ hn] at this

theorem good_sigma (hG : admG1 D) (hU : use1 D) (hC : Crv D cc δ) (hb : OnB D b) :
    Good cc δ b (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := exists_coords cc δ hx
  obtain ⟨P, hP⟩ := exists_pair cc δ hG hC
  have hs : Differentiable ℂ (sgStar (lamOf D cc δ)) := by
    rw [GlobalTheory.OddTheta.sgStar_eq P _ hP]
    exact (GlobalTheory.OddTheta.canonicalSigma_spec P _ hP).1
  rw [show U D (tor0 D cc δ) _ _ = _ from funext (U_pullB cc δ hG hb c _)]
  refine Gen.prod _ _ fun j _ => ?_
  refine Gen.lin _ (differentiable_U1 _ _ hs) (iteratedDeriv_mem ((hU cc δ hC).1 _ (hc j)))
    (sqL (embV D (tor0 D cc δ) (b j))) fun k => ?_
  rw [sqL_apply, sq]
  refine sum_mem fun τ _ => sum_mem fun i _ => sum_mem fun i' _ => mul_mem ?_ ?_
  · unfold coordV
    split_ifs
    exacts [one_mem _, zero_mem _]
  · exact hom_mem ((starRingEnd ℂ).comp (embT D τ)) _

theorem good_theta (hG : admG1 D) (hU : use1 D) (hC : Crv D cc δ) (hb : OnB D b) {t0 : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) :
    Good cc δ b (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0)) := by
  have h2 : InRationalLattice (lamOf D cc δ) t0 := ⟨2, two_pos, by simpa using ht.1⟩
  have h0 : U1 (lamOf D cc δ) t0 (sgStar (lamOf D cc δ)) 0 ∈ Qbar := by
    simpa [coef1] using (hU cc δ hC).1 _ h2 0
  have e : pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0) = fun z =>
      ((U1 (lamOf D cc δ) t0 (sgStar (lamOf D cc δ)) 0)⁻¹) ^ r *
        U D (tor0 D cc δ) (∑ j, t0 • embV D (tor0 D cc δ) (b j))
          (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) z := by
    funext z
    rw [U_pullB cc δ hG hb (fun _ => t0)]
    simp [pullB, GL3Theta.th0, div_eq_mul_inv, Finset.prod_mul_distrib, mul_comm]
  rw [e]
  exact ((good_sigma hG hU hC hb).transl hG hC hb
    (sum_mem fun j _ => smul_embV_mem cc δ hG hb h2 _)).const_mul (pow_mem (inv_mem h0) _)

theorem pow_smul_liftY (hG : admG1 D) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {p : ℕ} (hp : p ≠ 0) (n : ℕ)
    (ε : 𝓞 D.host.K) (hb : ∀ i, δ • embV D (tor0 D cc δ) (b i) ∈ La D (tor0 D cc δ) L L')
    (y : Fin r → Fin (p ^ n)) :
    (p ^ n) • liftY D (tor0 D cc δ) δ p n ε b y ∈ La D (tor0 D cc δ) L L' := by
  have e : (p ^ n) • liftY D (tor0 D cc δ) δ p n ε b y = ∑ i, (y i : ℕ) •
      (D.host.φ₀ ((ε : D.host.K) : D.host.E) • δ • embV D (tor0 D cc δ) (b i)) := by
    simp only [← Nat.cast_smul_eq_nsmul ℂ]
    funext τ i j
    have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
    simp only [liftY, Pi.smul_apply, embV_apply, Finset.sum_apply, Matrix.smul_apply,
      Matrix.sum_apply, smul_eq_mul, map_mul, map_sum, map_div₀, map_pow,
      map_natCast, hG.1 τ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    field_simp
  rw [e]
  exact sum_mem fun i _ => nsmul_mem (la_mul cc δ L L' ε (hb i)) _

theorem taylor_algebraic : ∀ D : D7, useAlg D := by
  intro D cc δ hC t0 ht N N' L L' hL hL' _ G hE
  have hG : admG1 D := (GlobalTheory.InducedType.induced_type D).1
  have hU : use1 D := GlobalTheory.T.forall_use1 D
  obtain ⟨b, κ, hb, hκ, rfl⟩ := hE
  have hg := ((good_theta hG hU hC hb ht).iop hG hC hb (LaB D (tor0 D cc δ) b) _
    (la_le cc δ hG hb L L')).const_mul hκ.1
  have hQ : ∀ x, LaQ D (tor0 D cc δ) L L' x → x ∈ sat (LaB D (tor0 D cc δ) b) := by
    rintro x ⟨m, hm, hx⟩
    exact sat_of_nsmul hm (la_le cc δ hG hb L L' hx)
  refine ⟨hg.coefIn, fun x hx => (hg.transl hG hC hb (hQ x hx)).coefIn, fun k a t ha hta => ?_,
    fun L₁ L₁' _ _ => (hg.iop hG hC hb _ _ (la_le cc δ hG hb L₁ L₁')).coefIn, ?_⟩
  · exact (Good.sum _ _ fun j _ => (hg.transl hG hC hb (hQ _ (hta j))).const_mul (ha j)).coefIn
  · intro p hp lam _ _ r b' n ε Φ hb' _ _ hΦ
    have hd := delta_mem_rationalIdealLattice cc δ hC.1.1
    refine Good.coefIn (cc := cc) (δ := δ) (b := b)
      (Good.const_mul (Good.sum _ _ fun a _ => Good.const_mul (Good.sum _ _ fun y _ => ?_)
      (hΦ _)) (inv_mem (pow_mem (natCast_mem _ _) _)))
    have hy : liftY D (tor0 D cc δ) δ p n ε b' y ∈ sat (LaB D (tor0 D cc δ) b) :=
      smul_embV_mem cc δ hG hb hd _
    have ha : vecN D (tor0 D cc δ) δ p n b' a ∈ sat (LaB D (tor0 D cc δ) b) :=
      smul_embV_mem cc δ hG hb hd _
    refine Good.const_mul (Good.const_mul (hg.transl hG hC hb hy) ?_) (inv_mem ?_)
    · unfold wPh
      split_ifs
      · obtain ⟨q, hq⟩ := qH_rat hG hC hb hy
        rw [hq]
        simpa using exp_rat_mem q
      · obtain ⟨m, hm⟩ := integral_la cc δ hG hC hL hL' _
          (pow_smul_liftY hG hp.out.ne_zero n ε hb'.2 y)
        rw [qH_nsmul] at hm
        obtain ⟨k, m', -, e⟩ := Classical.epsilon_spec (p := fun s : ℂ => ∃ (k : ℕ) (m : ℤ),
          (p : ℝ) ^ k * qH D (tor0 D cc δ) (liftY D (tor0 D cc δ) δ p n ε b' y) = (m : ℝ) ∧
            s = (-1 : ℂ) ^ m) ⟨_, n * 2, m, by rw [← hm]; push_cast; ring, rfl⟩
        rw [e]
        exact zpow_mem (neg_mem (one_mem _)) _
    · obtain ⟨q, hq⟩ := im_rat hG hC hb ha hy
      rw [kap, hq]
      convert exp_rat_mem (-2 * q) using 2
      push_cast
      ring

end GlobalTheory.ThetaAlgebraic
