import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CompactDerivativesBounded

open Matrix Finset
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

namespace TorusPowerExponential

variable {n : ℕ}

def cf (ε : Fin n → Bool) (p : Fin n × Fin n) : ℝ := wt p * sg ε p

lemma gen_apply (ε : Fin n → Bool) (p : Fin n × Fin n) (x y : Fin n) :
    gen ε p x y =
      if p.1 = p.2 then (if p.1 = x ∧ p.1 = y then Complex.I else 0)
      else if p.1 < p.2 then
        (if p.1 = x ∧ p.2 = y then 1 else 0) - (sg ε p : ℂ) * (if p.2 = x ∧ p.1 = y then 1 else 0)
      else Complex.I * ((if p.2 = x ∧ p.1 = y then 1 else 0) + (sg ε p : ℂ) * (if p.1 = x ∧ p.2 = y then 1 else 0)) := by
  unfold gen
  by_cases h1 : p.1 = p.2
  · rw [if_pos h1, if_pos h1]
    simp [Matrix.single_apply, Matrix.smul_apply]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : p.1 < p.2
    · rw [if_pos h2, if_pos h2]
      simp [Matrix.single_apply, Matrix.sub_apply, mul_ite]
    · rw [if_neg h2, if_neg h2]
      simp [Matrix.single_apply, Matrix.add_apply, Matrix.smul_apply, mul_ite]

lemma gen_apply_eq_zero (ε : Fin n → Bool) (p : Fin n × Fin n) (x y : Fin n)
    (h : p ≠ (x, y) ∧ p ≠ (y, x)) : gen ε p x y = 0 := by
  obtain ⟨a, b⟩ := p
  have e1 : ¬(a = x ∧ b = y) := fun h' => h.1 (Prod.ext h'.1 h'.2)
  have e2 : ¬(b = x ∧ a = y) := fun h' => h.2 (Prod.ext h'.2 h'.1)
  rw [gen_apply]
  dsimp only
  by_cases h0 : a = b
  · subst h0
    simp [e1]
  · simp [h0, e1, e2]

lemma tens (ε : Fin n → Bool) (i j k l : Fin n) :
    ∑ p, ((cf ε p : ℝ) : ℂ) * gen ε p j i * gen ε p k l = -(if i = k ∧ j = l then 1 else 0) := by
  by_cases hij : i = j
  · subst hij
    rw [Fintype.sum_eq_single (i, i) (fun p hp => by rw [gen_apply_eq_zero ε p i i ⟨hp, hp⟩]; simp)]
    simp only [cf, wt, sg, gen_apply, if_true, and_self]
    by_cases hk : i = k <;> by_cases hl : i = l <;> simp [hk, hl] <;> split_ifs <;> simp
  · rw [Fintype.sum_eq_add (j, i) (i, j) (by simp [Ne.symm hij])
      (fun p hp => by rw [gen_apply_eq_zero ε p j i ⟨hp.1, hp.2⟩]; simp)]
    rcases lt_or_gt_of_ne hij with h | h
    · have h' : ¬ j < i := not_lt_of_gt h
      simp only [cf, wt, sg, gen_apply, hij, Ne.symm hij, h, h', if_false, if_true, true_and, and_true]
      by_cases hk : i = k <;> by_cases hl : j = l <;> by_cases hk' : j = k <;> by_cases hl' : i = l <;>
        simp_all <;> cases ε k <;> cases ε l <;> simp_all <;> ring_nf <;> simp [Complex.I_sq] <;> ring
    · have h' : ¬ i < j := not_lt_of_gt h
      simp only [cf, wt, sg, gen_apply, hij, Ne.symm hij, h, h', if_false, if_true, true_and, and_true]
      by_cases hk : i = k <;> by_cases hl : j = l <;> by_cases hk' : j = k <;> by_cases hl' : i = l <;>
        simp_all <;> cases ε k <;> cases ε l <;> simp_all <;> ring_nf <;> simp [Complex.I_sq] <;> ring

lemma gen_inG (ε : Fin n → Bool) (p : Fin n × Fin n) : inG ε (gen ε p) := by
  unfold inG
  ext i j
  simp only [Matrix.add_apply, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply,
    Matrix.zero_apply, gen_apply]
  obtain ⟨a, b⟩ := p
  dsimp only
  unfold sg
  dsimp only
  by_cases hab : a = b
  · subst hab
    by_cases hi : a = i <;> by_cases hj : a = j <;> simp [hi, hj] <;> by_cases hij : i = j <;> simp_all <;>
      cases ε j <;> simp
  · rcases lt_or_gt_of_ne hab with h | h
    · simp only [hab, h, if_false, if_true]
      by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : b = i <;> by_cases h4 : a = j <;>
        simp_all <;> cases ε i <;> cases ε j <;> simp_all
    · have h' : ¬ a < b := not_lt_of_gt h
      simp only [hab, h', if_false]
      by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : b = i <;> by_cases h4 : a = j <;>
        simp_all <;> cases ε i <;> cases ε j <;> simp_all

lemma lgen (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p, (((cf ε p : ℝ) : ℂ) * trace (X * gen ε p)) • gen ε p = -X := by
  ext k l
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply, Matrix.trace,
    Matrix.diag, Matrix.mul_apply]
  calc ∑ p, ((cf ε p : ℂ) * ∑ i, ∑ j, X i j * gen ε p j i) * gen ε p k l
      = ∑ i, ∑ j, X i j * ∑ p, (cf ε p : ℂ) * gen ε p j i * gen ε p k l := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        conv_lhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => by ring
    _ = ∑ i, ∑ j, X i j * -(if i = k ∧ j = l then 1 else 0) := by simp only [tens]
    _ = -X k l := by
        simp only [mul_neg, Finset.sum_neg_distrib, mul_ite, mul_one, mul_zero, ite_and]
        simp [Finset.sum_ite_eq']

lemma conjT_of_inG {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inG ε X) :
    Xᴴ = -(Jm ε * X * Jm ε) := by
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left h
  calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
    _ = -(Jm ε * X * Jm ε) := by rw [h1, Matrix.neg_mul]

lemma trace_star {ε : Fin n → Bool} {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) :
    star (trace (X * Y)) = trace (X * Y) := by
  rw [← trace_conjTranspose, conjTranspose_mul, conjT_of_inG hX, conjT_of_inG hY, neg_mul_neg]
  have e : Jm ε * Y * Jm ε * (Jm ε * X * Jm ε) = Jm ε * (Y * X * Jm ε) := by
    calc Jm ε * Y * Jm ε * (Jm ε * X * Jm ε) = Jm ε * Y * (Jm ε * Jm ε) * X * Jm ε := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε * (Y * X * Jm ε) := by rw [Jm_mul_self, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, trace_mul_comm]
  simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
  exact trace_mul_comm _ _

lemma trace_re {ε : Fin n → Bool} {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) :
    ((trace (X * Y)).re : ℂ) = trace (X * Y) :=
  Complex.conj_eq_iff_re.1 (by rw [starRingEnd_apply]; exact trace_star hX hY)

lemma umat_mul_inv {ε : Fin n → Bool} (g : UJ ε) : umat g * umat g⁻¹ = 1 := by
  simp [umat]

lemma umat_inv_mul {ε : Fin n → Bool} (g : UJ ε) : umat g⁻¹ * umat g = 1 := by
  simp [umat]

lemma umat_inUJ {ε : Fin n → Bool} (g : UJ ε) : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2

lemma conj_inG {ε : Fin n → Bool} (g : UJ ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    inG ε (umat g * X * umat g⁻¹) := by
  have hhJ : (umat g)ᴴ * Jm ε = Jm ε * umat g⁻¹ := by
    calc (umat g)ᴴ * Jm ε = (umat g)ᴴ * Jm ε * (umat g * umat g⁻¹) := by
          rw [umat_mul_inv, Matrix.mul_one]
      _ = ((umat g)ᴴ * Jm ε * umat g) * umat g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Jm ε * umat g⁻¹ := by rw [umat_inUJ]
  have hkJ : (umat g⁻¹)ᴴ * Jm ε = Jm ε * umat g := by
    calc (umat g⁻¹)ᴴ * Jm ε = (umat g⁻¹)ᴴ * Jm ε * (umat g⁻¹ * umat g) := by
          rw [umat_inv_mul, Matrix.mul_one]
      _ = ((umat g⁻¹)ᴴ * Jm ε * umat g⁻¹) * umat g := by simp only [Matrix.mul_assoc]
      _ = Jm ε * umat g := by rw [umat_inUJ]
  have hX' : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  unfold inG
  have e : (umat g * X * umat g⁻¹)ᴴ * Jm ε = -(Jm ε * (umat g * X * umat g⁻¹)) := by
    calc (umat g * X * umat g⁻¹)ᴴ * Jm ε = (umat g⁻¹)ᴴ * (Xᴴ * ((umat g)ᴴ * Jm ε)) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (umat g⁻¹)ᴴ * ((Xᴴ * Jm ε) * umat g⁻¹) := by rw [hhJ, Matrix.mul_assoc]
      _ = -(((umat g⁻¹)ᴴ * Jm ε) * X * umat g⁻¹) := by
          rw [hX', Matrix.neg_mul, Matrix.mul_neg]; simp only [Matrix.mul_assoc]
      _ = -(Jm ε * (umat g * X * umat g⁻¹)) := by rw [hkJ]; simp only [Matrix.mul_assoc]
  rw [e, neg_add_cancel]

lemma trace_swap (h k P Q : Matrix (Fin n) (Fin n) ℂ) :
    trace (h * P * k * Q) = trace (k * Q * h * P) := by
  calc trace (h * P * k * Q) = trace (h * (P * k * Q)) := by simp only [Matrix.mul_assoc]
    _ = trace (P * k * Q * h) := trace_mul_comm _ _
    _ = trace (P * (k * Q * h)) := by simp only [Matrix.mul_assoc]
    _ = trace (k * Q * h * P) := trace_mul_comm _ _

def am {ε : Fin n → Bool} (g : UJ ε) (p : Fin n × Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  umat g * gen ε p * umat g⁻¹

def zc {ε : Fin n → Bool} (g : UJ ε) (p q : Fin n × Fin n) : ℝ :=
  -(cf ε q * (trace (am g p * gen ε q)).re)

lemma am_eq {ε : Fin n → Bool} (g : UJ ε) (p : Fin n × Fin n) :
    am g p = ∑ q, ((zc g p q : ℝ) : ℂ) • gen ε q := by
  have hre : ∀ q, ((trace (am g p * gen ε q)).re : ℂ) = trace (am g p * gen ε q) := fun q =>
    trace_re (conj_inG g (gen_inG ε p)) (gen_inG ε q)
  rw [← neg_neg (am g p), ← lgen ε (am g p), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← neg_smul]
  congr 1
  unfold zc
  push_cast
  rw [hre]

lemma comb {ε : Fin n → Bool} (g : UJ ε) (r : Fin n × Fin n) :
    ∑ q, ((∑ p, cf ε p * zc g p q * zc g p r : ℝ) : ℂ) • gen ε q = ((cf ε r : ℝ) : ℂ) • gen ε r := by
  have hre : ∀ p, ((trace (am g p * gen ε r)).re : ℂ) = trace (umat g⁻¹ * gen ε r * umat g * gen ε p) :=
    fun p => by
      show ((trace (umat g * gen ε p * umat g⁻¹ * gen ε r)).re : ℂ) = _
      rw [trace_re (conj_inG g (gen_inG ε p)) (gen_inG ε r)]
      exact trace_swap _ _ _ _
  calc ∑ q, ((∑ p, cf ε p * zc g p q * zc g p r : ℝ) : ℂ) • gen ε q
      = ∑ p, ((cf ε p * zc g p r : ℝ) : ℂ) • ∑ q, ((zc g p q : ℝ) : ℂ) • gen ε q := by
        simp only [Finset.smul_sum, smul_smul, Complex.ofReal_sum, Finset.sum_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        congr 1
        push_cast
        ring
    _ = ∑ p, ((cf ε p * zc g p r : ℝ) : ℂ) • am g p :=
        Finset.sum_congr rfl fun p _ => by rw [← am_eq]
    _ = ∑ p, (-((cf ε r : ℝ) : ℂ)) • (umat g * ((((cf ε p : ℝ) : ℂ) *
          trace (umat g⁻¹ * gen ε r * umat g * gen ε p)) • gen ε p) * umat g⁻¹) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
        unfold am
        congr 1
        unfold zc
        push_cast
        rw [hre]
        ring
    _ = (-((cf ε r : ℝ) : ℂ)) • (umat g * (∑ p, (((cf ε p : ℝ) : ℂ) *
          trace (umat g⁻¹ * gen ε r * umat g * gen ε p)) • gen ε p) * umat g⁻¹) := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
    _ = ((cf ε r : ℝ) : ℂ) • gen ε r := by
        rw [lgen, Matrix.mul_neg, Matrix.neg_mul, neg_smul_neg]
        congr 1
        calc umat g * (umat g⁻¹ * gen ε r * umat g) * umat g⁻¹
            = (umat g * umat g⁻¹) * gen ε r * (umat g * umat g⁻¹) := by simp only [Matrix.mul_assoc]
          _ = gen ε r := by rw [umat_mul_inv, Matrix.one_mul, Matrix.mul_one]

section Ops

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}

lemma dS_add (hC : Calc ε σ D) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {u v : H} (hu : u ∈ D)
    (hv : v ∈ D) : dS σ X (u + v) = dS σ X u + dS σ X v := by
  have h := (hC.der X hX u hu).add (hC.der X hX v hv)
  have e : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (u + v)) =
      fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) u + σ (NormedSpace.exp ((t : ℂ) • X)) v := by
    funext t
    exact map_add _ _ _
  show deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (u + v)) 0 = _
  rw [e]
  exact h.deriv

lemma dS_smul (hC : Calc ε σ D) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (c : ℂ) {v : H}
    (hv : v ∈ D) : dS σ X (c • v) = c • dS σ X v := by
  have h := (hC.der X hX v hv).const_smul c
  have e : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (c • v)) =
      fun t : ℝ => c • σ (NormedSpace.exp ((t : ℂ) • X)) v := by
    funext t
    exact map_smul _ _ _
  show deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (c • v)) 0 = _
  rw [e]
  exact h.deriv

lemma dS_sum (hC : Calc ε σ D) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {ι : Type}
    (s : Finset ι) (a : ι → ℂ) (w : ι → H) (hw : ∀ i ∈ s, w i ∈ D) :
    dS σ X (∑ i ∈ s, a i • w i) = ∑ i ∈ s, a i • dS σ X (w i) := by
  have h := HasDerivAt.fun_sum (u := s) (x := (0 : ℝ))
    (fun i hi => (hC.der X hX (w i) (hw i hi)).const_smul (a i))
  have e : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (∑ i ∈ s, a i • w i)) =
      fun t : ℝ => ∑ i ∈ s, a i • σ (NormedSpace.exp ((t : ℂ) • X)) (w i) := by
    funext t
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  show deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (∑ i ∈ s, a i • w i)) 0 = _
  rw [e]
  exact h.deriv

lemma cas_add (hC : Calc ε σ D) {u v : H} (hu : u ∈ D) (hv : v ∈ D) :
    Cas ε σ (u + v) = Cas ε σ u + Cas ε σ v := by
  unfold Cas
  rw [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  have hg := gen_inG ε p
  rw [dS_add hC hg hu hv, dS_add hC hg (hC.mem _ hg u hu) (hC.mem _ hg v hv), smul_add]

lemma cas_smul (hC : Calc ε σ D) (c : ℂ) {v : H} (hv : v ∈ D) :
    Cas ε σ (c • v) = c • Cas ε σ v := by
  unfold Cas
  rw [smul_neg, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  have hg := gen_inG ε p
  rw [dS_smul hC hg c hv, dS_smul hC hg c (hC.mem _ hg v hv), smul_comm]

lemma cas_symm (hC : Calc ε σ D) {u v : H} (hu : u ∈ D) (hv : v ∈ D) :
    ⟪Cas ε σ u, v⟫_ℂ = ⟪u, Cas ε σ v⟫_ℂ := by
  unfold Cas
  rw [inner_neg_left, inner_neg_right, sum_inner, inner_sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  have hg := gen_inG ε p
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  congr 1
  rw [hC.skew _ hg _ (hC.mem _ hg u hu) v hv, hC.skew _ hg u hu _ (hC.mem _ hg v hv), neg_neg]

lemma lin_single (hC : Calc ε σ D) (r : Fin n × Fin n) (a : ℝ) {y : H} (hy : y ∈ D) :
    dS σ (((a : ℝ) : ℂ) • gen ε r) y = ((a : ℝ) : ℂ) • dS σ (gen ε r) y := by
  have h := hC.lin (fun q => if q = r then a else 0) y hy
  have e1 : ∑ q, (((if q = r then a else 0 : ℝ)) : ℂ) • gen ε q = ((a : ℝ) : ℂ) • gen ε r := by
    rw [Finset.sum_eq_single r (fun q _ hq => by simp [hq]) (by simp)]
    simp
  have e2 : ∑ q, (((if q = r then a else 0 : ℝ)) : ℂ) • dS σ (gen ε q) y = ((a : ℝ) : ℂ) • dS σ (gen ε r) y := by
    rw [Finset.sum_eq_single r (fun q _ hq => by simp [hq]) (by simp)]
    simp
  rw [← e1, ← e2]
  exact h

lemma dS_am (hC : Calc ε σ D) (g : UJ ε) (p : Fin n × Fin n) {y : H} (hy : y ∈ D) :
    dS σ (umat g * gen ε p * umat g⁻¹) y = ∑ r, ((zc g p r : ℝ) : ℂ) • dS σ (gen ε r) y := by
  rw [show umat g * gen ε p * umat g⁻¹ = am g p from rfl, am_eq]
  exact hC.lin _ y hy

omit [InnerProductSpace ℂ H] in
lemma sum_rot {ι : Type} [Fintype ι] (F : ι → ι → ι → H) :
    ∑ p, ∑ r, ∑ q, F p r q = ∑ r, ∑ q, ∑ p, F p r q := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_comm

lemma cas_inv (hC : Calc ε σ D) (hst : ∀ (g : UJ ε), ∀ v ∈ D, σ (umat g) v ∈ D) (g : UJ ε) {v : H}
    (hv : v ∈ D) : Cas ε σ (σ (umat g) v) = σ (umat g) (Cas ε σ v) := by
  have hw : σ (umat g) v ∈ D := hst g v hv
  have hD : ∀ q, dS σ (gen ε q) (σ (umat g) v) ∈ D := fun q => hC.mem _ (gen_inG ε q) _ hw

  have e1 : σ (umat g) (Cas ε σ v) = -∑ p, ∑ r, ∑ q, ((cf ε p * (zc g p r * zc g p q) : ℝ) : ℂ) •
      dS σ (gen ε r) (dS σ (gen ε q) (σ (umat g) v)) := by
    unfold Cas
    rw [map_neg, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    have hg := gen_inG ε p
    have hpv := hC.mem _ hg v hv
    rw [map_smul, hC.conj g _ hg _ hpv, dS_am hC g p (hst g _ hpv), hC.conj g _ hg _ hv,
      dS_am hC g p hw, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [dS_sum hC (gen_inG ε r) _ _ _ (fun q _ => hD q), Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    unfold cf
    push_cast
    ring
  have e2 : Cas ε σ (σ (umat g) v) = -∑ r, ∑ q, ∑ p, ((cf ε p * (zc g p r * zc g p q) : ℝ) : ℂ) •
      dS σ (gen ε r) (dS σ (gen ε q) (σ (umat g) v)) := by
    unfold Cas
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    have hg := gen_inG ε r
    have h1 : ∑ q, ((∑ p, cf ε p * zc g p q * zc g p r : ℝ) : ℂ) • dS σ (gen ε q) (σ (umat g) v) =
        ((cf ε r : ℝ) : ℂ) • dS σ (gen ε r) (σ (umat g) v) := by
      rw [← hC.lin _ _ hw, comb, lin_single hC r _ hw]
    rw [show ((wt r * sg ε r : ℝ) : ℂ) = ((cf ε r : ℝ) : ℂ) from rfl, ← dS_smul hC hg _ (hD r), ← h1,
      dS_sum hC hg _ _ _ (fun q _ => hD q)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Complex.ofReal_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    push_cast
    ring
  rw [e1, e2]
  congr 1
  exact (sum_rot (H := H) (ι := Fin n × Fin n) _).symm

end Ops
end TorusPowerExponential

theorem c2 : CasimirProperties := by
  intro n ε H _ _ _ σ D hC hst
  exact ⟨fun u hu v hv => TorusPowerExponential.cas_add hC hu hv, fun c v hv => TorusPowerExponential.cas_smul hC c hv,
    fun u hu v hv => TorusPowerExponential.cas_symm hC hu hv, fun g v hv => TorusPowerExponential.cas_inv hC hst g hv⟩

end Formalism.L2.SG.Pf.admitted
