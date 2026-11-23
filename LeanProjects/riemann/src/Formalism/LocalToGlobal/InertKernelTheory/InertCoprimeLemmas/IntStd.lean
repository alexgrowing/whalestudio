import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopIso
import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfGen
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime
import Formalism.LocalToGlobal.GlobalTheory.GL3.LinkThetaStatementFamily

noncomputable section

namespace Formalism.L2.KerInert.ISd

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

section Coef

variable {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

def Good (c : ℂ) : Prop := c ∈ Qbar ∧ IsIntP (lamC lam c)

theorem lamC_of_mem {c : ℂ} (h : c ∈ Qbar) : lamC lam c = lam ⟨c, h⟩ := by
  simp only [lamC, dif_pos h]

theorem good_mul {a b : ℂ} (ha : Good lam a) (hb : Good lam b) : Good lam (a * b) := by
  refine ⟨mul_mem ha.1 hb.1, ?_⟩
  have h : lamC lam (a * b) = lamC lam a * lamC lam b := by
    rw [lamC_of_mem lam ha.1, lamC_of_mem lam hb.1, lamC_of_mem lam (mul_mem ha.1 hb.1), ← map_mul]
    rfl
  have h1 := ha.2
  have h2 := hb.2
  unfold IsIntP at *
  rw [h, norm_mul]
  exact mul_le_one₀ h1 (norm_nonneg _) h2

theorem good_zero : Good lam 0 := by
  refine ⟨zero_mem _, ?_⟩
  unfold IsIntP
  rw [lamC_of_mem lam (zero_mem _)]
  have : (⟨0, zero_mem _⟩ : Qbar) = 0 := rfl
  rw [this, map_zero, norm_zero]
  exact zero_le_one

theorem good_of_pow (c : ℂ) (k n : ℕ) (hk : 0 < k) (hn : Nat.Coprime n p) (h : c ^ k * (n : ℂ) = 1) :
    Good lam c := by
  have hn0 : (n : ℂ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h; exact zero_ne_one h
  have hck : c ^ k = algebraMap ℚ ℂ ((n : ℚ)⁻¹) := by
    rw [map_inv₀, map_natCast]
    exact eq_inv_of_mul_eq_one_left h
  have hmem : c ∈ Qbar := by
    rw [mem_algebraicClosure_iff']
    refine IsIntegral.of_pow hk ?_
    rw [hck]
    exact isIntegral_algebraMap
  refine ⟨hmem, ?_⟩
  set y : Qbar := ⟨c, hmem⟩ with hy
  have hyk : y ^ k * (n : Qbar) = 1 := by
    apply Subtype.val_injective
    change Qbar.val (y ^ k * (n : Qbar)) = Qbar.val 1
    rw [map_mul, map_pow, map_natCast, map_one]
    exact h
  have hl := congrArg lam hyk
  rw [map_mul, map_pow, map_natCast, map_one] at hl
  have hnorm := congrArg norm hl
  rw [norm_mul, norm_pow, RestC.norm_nat_coprime p hn, mul_one, norm_one] at hnorm
  have h1 : ‖lam y‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp hnorm
  unfold IsIntP
  rw [lamC_of_mem lam hmem]
  exact le_of_eq h1

theorem good_one : Good lam 1 := good_of_pow lam 1 1 1 one_pos (Nat.coprime_one_left p) (by simp)

theorem good_iota (n : ℕ) (hn : n ≠ 0 → Nat.Coprime n p) : Good lam ((Real.sqrt (n : ℝ))⁻¹ : ℂ) := by
  by_cases h0 : n = 0
  · subst h0
    simp only [Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, inv_zero]
    exact good_zero lam
  · refine good_of_pow lam _ 2 n (by norm_num) (hn h0) ?_
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast h0
    have hs : ((Real.sqrt (n : ℝ) : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast; rfl
    rw [inv_pow, hs, inv_mul_cancel₀ hn']

variable {D : D7} {N N' : ℕ}

theorem good_al (T : Tor D) (x : VC D N N') : Good lam (al D T x) := by
  refine good_of_pow lam _ 2 1 (by norm_num) (Nat.coprime_one_left p) ?_
  simp only [al, Nat.cast_one, mul_one]
  rw [← zpow_natCast, ← zpow_mul]
  apply Even.neg_one_zpow
  exact Int.even_mul.2 (Or.inr ⟨1, by norm_num⟩)

theorem good_cf (T : Tor D) (x y : VC D N N') (q : ℚ) (hq : (Formalism.MainNotions.TaylorLogMetric.Hf D T x y).im = q) :
    Good lam (IO.cf T x y) := by
  refine good_of_pow lam _ (2 * q.den) 1 (by have := q.den_pos; omega) (Nat.coprime_one_left p) ?_
  rw [Nat.cast_one, mul_one, IO.cf, hq, ← Complex.exp_nat_mul]
  convert Complex.exp_int_mul_two_pi_mul_I (-q.num) using 2
  have hd : (q.den : ℂ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [Complex.ofReal_ratCast, Rat.cast_def]
  push_cast
  field_simp

end Coef

section Rep

variable {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {D : D7} {N N' : ℕ} (T : Tor D)

def Rep (Pt : VC D N N' → Prop) (F G : VC D N N' → ℂ) : Prop :=
  ∃ (m : ℕ) (c : Fin m → ℂ) (s : Fin m → VC D N N'), (∀ k, Good lam (c k)) ∧ (∀ k, Pt (s k)) ∧
    F = fun z => ∑ k, c k * U D T (s k) G z

variable {lam T}

theorem rep_of_fintype {Pt : VC D N N' → Prop} {G : VC D N N' → ℂ} {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (s : ι → VC D N N') (hc : ∀ i, Good lam (c i)) (hs : ∀ i, Pt (s i)) :
    Rep lam T Pt (fun z => ∑ i, c i * U D T (s i) G z) G := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun k => c (e.symm k), fun k => s (e.symm k), fun k => hc _, fun k => hs _, ?_⟩
  funext z
  exact (Fintype.sum_equiv e.symm _ _ (fun k => rfl)).symm

theorem rep_zero {Pt : VC D N N' → Prop} {G : VC D N N' → ℂ} : Rep lam T Pt (fun _ => 0) G :=
  ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, by funext z; simp⟩

theorem U_zero_pt (G : VC D N N' → ℂ) (z : VC D N N') : U D T 0 G z = G z := by
  simp [U, IO.Hf_zero_right]

theorem rep_self {Pt : VC D N N' → Prop} {G : VC D N N' → ℂ} (h0 : Pt 0) : Rep lam T Pt G G := by
  refine ⟨1, fun _ => 1, fun _ => 0, fun _ => good_one lam, fun _ => h0, ?_⟩
  funext z
  simp [U_zero_pt]

theorem rep_smul {Pt : VC D N N' → Prop} {F G : VC D N N' → ℂ} {a : ℂ} (ha : Good lam a)
    (h : Rep lam T Pt F G) : Rep lam T Pt (fun z => a * F z) G := by
  obtain ⟨m, c, s, hc, hs, rfl⟩ := h
  refine ⟨m, fun k => a * c k, s, fun k => good_mul lam ha (hc k), hs, ?_⟩
  funext z
  show a * ∑ k, c k * U D T (s k) G z = ∑ k, a * c k * U D T (s k) G z
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem rep_U {Pt Pt' : VC D N N' → Prop} {F G : VC D N N' → ℂ} (x : VC D N N') (h : Rep lam T Pt F G)
    (hx : ∀ y, Pt y → Good lam (IO.cf T x y) ∧ Pt' (x + y)) : Rep lam T Pt' (U D T x F) G := by
  obtain ⟨m, c, s, hc, hs, rfl⟩ := h
  refine ⟨m, fun k => c k * IO.cf T x (s k), fun k => x + s k,
    fun k => good_mul lam (hc k) (hx _ (hs k)).1, fun k => (hx _ (hs k)).2, ?_⟩
  funext z
  have e := IO.U_sum T x (fun k w => c k * U D T (s k) G w) z
  refine e.trans ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  beta_reduce
  rw [IO.U_smul, IO.U_U]
  ring

theorem rep_sum {Pt : VC D N N' → Prop} {G : VC D N N' → ℂ} {Q : Type*} [Fintype Q] (F : Q → VC D N N' → ℂ)
    (h : ∀ q, Rep lam T Pt (F q) G) : Rep lam T Pt (fun z => ∑ q, F q z) G := by
  classical
  choose m c s hc hs hF using h
  have e : (fun z => ∑ q, F q z) = fun z => ∑ i : (Σ q, Fin (m q)), c i.1 i.2 * U D T (s i.1 i.2) G z := by
    funext z
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hF q]
  rw [e]
  exact rep_of_fintype _ _ (fun i => hc _ _) (fun i => hs _ _)

theorem rep_Iop {Pt Pt' : VC D N N' → Prop} {F G : VC D N N' → ℂ} {La₁ La₂ : AddSubgroup (VC D N N')}
    (h : Rep lam T Pt F G)
    (hx : ∀ x ∈ La₂, ∀ y, Pt y → Good lam (IO.cf T x y) ∧ Pt' (x + y))
    (hidx : (La₁.addSubgroupOf La₂).index ≠ 0 → Nat.Coprime (La₁.addSubgroupOf La₂).index p) :
    Rep lam T Pt' (Iop D T La₁ La₂ F) G := by
  classical
  by_cases h0 : (La₁.addSubgroupOf La₂).index = 0
  · have e : Iop D T La₁ La₂ F = fun _ => 0 := by
      funext z
      simp [Iop, h0]
    rw [e]
    exact rep_zero
  · haveI : (La₁.addSubgroupOf La₂).FiniteIndex := ⟨h0⟩
    haveI : Fintype (La₂ ⧸ La₁.addSubgroupOf La₂) := Fintype.ofFinite _
    have e : Iop D T La₁ La₂ F = fun z => ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂,
        ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) * al D T ((Quotient.out q : La₂) : VC D N N') *
          U D T ((Quotient.out q : La₂) : VC D N N') F z := by
      funext z
      simp only [Iop]
      rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [e]
    apply rep_sum
    intro q
    exact rep_smul (good_mul lam (good_iota lam _ hidx) (good_al lam T _))
      (rep_U _ h (hx _ (Quotient.out q).2))

end Rep

section Lat

variable {p : ℕ} {D : D7} {N N' : ℕ}

theorem idx_coprime [Fact p.Prime] {V : Type*} [AddCommGroup V] (La₁ La₂ : AddSubgroup V) (s : ℕ)
    (hs : Nat.Coprime s p) (hk : ∀ z ∈ La₂, s • z ∈ La₁) (h0 : (La₁.addSubgroupOf La₂).index ≠ 0) :
    Nat.Coprime (La₁.addSubgroupOf La₂).index p := by
  haveI : (La₁.addSubgroupOf La₂).FiniteIndex := ⟨h0⟩
  have hp : p.Prime := Fact.out
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  rw [AddSubgroup.index] at hdvd
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' p hdvd
  induction g using QuotientAddGroup.induction_on with | H a => ?_
  have e : s • (a : La₂ ⧸ La₁.addSubgroupOf La₂) = 0 := by
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
      AddSubgroup.coe_nsmul]
    exact hk _ a.2
  have hd := addOrderOf_dvd_of_nsmul_eq_zero e
  rw [hg] at hd
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hs.symm hd

theorem homL_smul {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (a b : ℕ)
    (ha : ∀ x ∈ L₁, (a : D.host.E) • x ∈ L) (hb : ∀ y ∈ L', (b : D.host.E) • y ∈ L₁')
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ homL D L L') :
    ((a * b : ℕ) : D.host.E) • A ∈ homL D L₁ L₁' := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    apply Submodule.subset_span
    intro x hx
    have e : (((a * b : ℕ) : D.host.E) • A).mulVec x = (b : D.host.E) • A.mulVec ((a : D.host.E) • x) := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
      push_cast
      rw [mul_comm]
    rw [e]
    exact hb _ (hA _ (ha x hx))
  | zero => rw [smul_zero]; exact zero_mem _
  | add A B _ _ hA hB => rw [smul_add]; exact add_mem hA hB
  | smul o A _ hA =>
    rw [smul_comm]
    exact Submodule.smul_mem _ o hA

theorem YYl_smul {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (a b : ℕ)
    (ha : ∀ x ∈ L₁, (a : D.host.E) • x ∈ L) (hb : ∀ y ∈ L', (b : D.host.E) • y ∈ L₁')
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ YYl D L L') :
    ((a * b : ℕ) : D.host.E) • A ∈ YYl D L₁ L₁' := by
  induction hA using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a', ha', A', hA', rfl⟩ := hB
    apply Submodule.subset_span
    refine ⟨a', ha', _, homL_smul a b ha hb hA', ?_⟩
    rw [smul_comm]
  | zero => rw [smul_zero]; exact zero_mem _
  | add A B _ _ hA hB => rw [smul_add]; exact add_mem hA hB
  | smul o A _ hA =>
    rw [smul_comm]
    exact Submodule.smul_mem _ o hA

theorem embV_smul (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) ((n : D.host.E) • A) = n • embV D (tor0 D cc δ) A := by
  funext τ i j
  simp [embV, tor0, nsmul_eq_mul]

theorem La_smul (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (a b : ℕ)
    (ha : ∀ x ∈ L₁, (a : D.host.E) • x ∈ L) (hb : ∀ y ∈ L', (b : D.host.E) • y ∈ L₁')
    {z : VC D N N'} (hz : z ∈ La D (tor0 D cc δ) L L') : (a * b) • z ∈ La D (tor0 D cc δ) L₁ L₁' := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    refine ⟨w, hw, _, YYl_smul a b ha hb hA, ?_⟩
    rw [embV_smul, smul_comm]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem im_rat (T : Tor D) {La' : AddSubgroup (VC D N N')} (hI : IO.HfInt T La') {x y : VC D N N'} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hx : n • x ∈ La') (hy : m • y ∈ La') : ∃ q : ℚ, (Formalism.MainNotions.TaylorLogMetric.Hf D T x y).im = q := by
  obtain ⟨a, b, -, h⟩ := hI _ hx _ hy
  have hs : Formalism.MainNotions.TaylorLogMetric.Hf D T (n • x) (m • y) = ((n : ℂ) * (m : ℂ)) * Formalism.MainNotions.TaylorLogMetric.Hf D T x y := by
    rw [← Nat.cast_smul_eq_nsmul ℂ n x, ← Nat.cast_smul_eq_nsmul ℂ m y, IO.Hf_smul]
    simp
  rw [h] at hs
  have e2 := congrArg Complex.im hs
  simp at e2
  refine ⟨(b : ℚ) / ((n : ℚ) * (m : ℚ)), ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  push_cast
  rw [eq_div_iff (by positivity)]
  linarith

end Lat

end Formalism.L2.KerInert.ISd

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity ISd

theorem pairs_standard_at_p : StdStep := by
  intro D cc δ B hcc hδ χ hχ p _ hp5 hjac lam N N' M M' hAdm hM hM' t ht
  obtain ⟨s, hs, hsM, hMs⟩ := hM
  obtain ⟨s', hs', hsM', hMs'⟩ := hM'
  have hp : p.Prime := Fact.out
  have spos : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs))
  have spos' : 0 < s' := Nat.pos_of_ne_zero (by rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs'))
  set La0 := La D (tor0 D cc δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') with hLa0
  set La1 := La D (tor0 D cc δ) M (Formalism.MainNotions.StandardLatticesGL3.stdL D N') with hLa1
  set La2 := La D (tor0 D cc δ) M M' with hLa2
  have one_std : ∀ y ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N', ((1 : ℕ) : D.host.E) • y ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N' := by
    intro y hy; simpa using hy
  have one_M : ∀ y ∈ M, ((1 : ℕ) : D.host.E) • y ∈ M := by
    intro y hy; simpa using hy
  have k10 : ∀ z ∈ La1, (s * 1) • z ∈ La0 := fun z hz => La_smul cc δ s 1 hsM one_std hz
  have k21 : ∀ z ∈ La2, (1 * s') • z ∈ La1 := fun z hz => La_smul cc δ 1 s' one_M hMs' hz
  have k20 : ∀ z ∈ La2, (s * s') • z ∈ La0 := fun z hz => La_smul cc δ s s' hsM hMs' hz
  have k12 : ∀ z ∈ La1, (1 * s') • z ∈ La2 := fun z hz => La_smul cc δ 1 s' one_M hsM' hz
  have hδ0 : δ ≠ 0 := delta_nonzero_link D cc hcc δ hδ
  have hI : IO.HfInt (tor0 D cc δ) La2 := hermitian_form_integral_values D cc hcc δ hδ hδ0 N N' M M' hAdm

  let Q2 : VC D N N' → Prop := fun y => ∃ n : ℕ, 0 < n ∧ n • y ∈ La2
  have q2_add : ∀ x y, Q2 x → Q2 y → Q2 (x + y) := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have e : (n * m) • (x + y) = m • (n • x) + n • (m • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm m n]
    rw [e]
    exact add_mem (AddSubgroup.nsmul_mem _ hx m) (AddSubgroup.nsmul_mem _ hy n)
  have q2_2 : ∀ x ∈ La2, Q2 x := fun x hx => ⟨1, one_pos, by simpa using hx⟩
  have q2_1 : ∀ x ∈ La1, Q2 x := fun x hx => ⟨1 * s', by omega, k12 x hx⟩
  have cf_good : ∀ x y, Q2 x → Q2 y → Good lam (IO.cf (tor0 D cc δ) x y) := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    obtain ⟨q, hq⟩ := im_rat (tor0 D cc δ) hI hn hm hx hy
    exact good_cf lam _ x y q hq

  have R1 : Rep lam B.tor (fun y => y ∈ La1) (B.thHalf N N' M) (B.thZero N N') := by
    show Rep lam B.tor (fun y => y ∈ La1) (Iop D B.tor La0 La1 (B.thZero N N')) (B.thZero N N')
    refine rep_Iop (Pt := fun y => y = 0) (rep_self rfl) ?_ ?_
    · rintro x hx y rfl
      refine ⟨good_cf lam _ x 0 0 (by simp [IO.Hf_zero_right]), by simpa using hx⟩
    · exact idx_coprime La0 La1 (s * 1) (by simpa using hs) k10

  have R2 : Rep lam B.tor (fun y => ∃ a ∈ La2, ∃ b ∈ La1, y = a + b) (B.thMoved N N' M M') (B.thZero N N') := by
    show Rep lam B.tor _ (Iop D B.tor La1 La2 (B.thHalf N N' M)) (B.thZero N N')
    refine rep_Iop R1 ?_ ?_
    · intro x hx y hy
      exact ⟨cf_good x y (q2_2 x hx) (q2_1 y hy), x, hx, y, hy, rfl⟩
    · exact idx_coprime La1 La2 (1 * s') (by simpa using hs') k21

  obtain ⟨n, hn, hnp, hnt⟩ := ht
  have R3 : Rep lam B.tor (TorsPrime D p La0) (U D B.tor t (B.thMoved N N' M M')) (B.thZero N N') := by
    refine rep_U t R2 ?_
    rintro y ⟨a, ha, b, hb, rfl⟩
    refine ⟨cf_good t _ ⟨n, hn, hnt⟩ (q2_add a b (q2_2 a ha) (q2_1 b hb)), ?_⟩
    refine ⟨n * (s * s'), Nat.mul_pos hn (Nat.mul_pos spos spos'), Nat.Coprime.mul hnp (Nat.Coprime.mul hs hs'), ?_⟩
    have e : (n * (s * s')) • (t + (a + b)) = (s * s') • (n • t) + (n • ((s * s') • a) + (n * s') • ((s * 1) • b)) := by
      simp only [smul_add, smul_smul]
      congr 1
      · rw [mul_comm]
      · congr 1
        rw [mul_one, mul_assoc, mul_comm s' s]
    rw [e]
    exact add_mem (k20 _ hnt) (add_mem (AddSubgroup.nsmul_mem _ (k20 a ha) n)
      (AddSubgroup.nsmul_mem _ (k10 b hb) (n * s')))

  have hchi := RestC.chiFacUnit (D := D) χ hχ p lam N N' M M' hAdm ⟨s, hs, hsM, hMs⟩ ⟨s', hs', hsM', hMs'⟩
  have hgood : Good lam (Base.chiFac χ N N' M M') := ⟨hchi.1, le_of_eq hchi.2⟩
  have R4 := rep_smul hgood R3
  have e : U D B.tor t (B.eNat χ N N' M M') = fun z => Base.chiFac χ N N' M M' * U D B.tor t (B.thMoved N N' M M') z := by
    funext z
    exact IO.U_smul _ t _ _ z
  rw [e]
  obtain ⟨m, c, s₀, hc, hs₀, hF⟩ := R4
  exact ⟨m, c, s₀, hc, hs₀, hF⟩

end Formalism.L2.KerInert
