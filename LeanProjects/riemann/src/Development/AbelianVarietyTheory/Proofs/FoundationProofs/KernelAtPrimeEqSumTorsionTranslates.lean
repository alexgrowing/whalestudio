import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansionStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.NormSum.KernelAt

theorem coprime_index {V : Type*} [AddCommGroup V] (A₀ A₁ : AddSubgroup V) (hfg : A₁.FG) (s p : ℕ)
    (hp : p.Prime) (hs : Nat.Coprime s p) (h : ∀ x ∈ A₁, s • x ∈ A₀) :
    Nat.Coprime (A₀.addSubgroupOf A₁).index p := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hs
    exact hp.one_lt.ne' hs
  haveI : AddGroup.FG A₁ := (AddGroup.fg_iff_addSubgroup_fg A₁).2 hfg
  have hk : ∀ q : A₁ ⧸ A₀.addSubgroupOf A₁, s • q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact h x x.2
  haveI : Finite (A₁ ⧸ A₀.addSubgroupOf A₁) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro q
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨s, Nat.pos_of_ne_zero hs0, hk q⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card' (G := A₁ ⧸ A₀.addSubgroupOf A₁) p hd
  have : p ∣ s := hq ▸ addOrderOf_dvd_of_nsmul_eq_zero (hk q)
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hs.symm this

theorem smul_mem_homL {D : D7} {N N' : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {s s' : ℕ}
    (h : ∀ x ∈ L, (s : D.host.E) • x ∈ L₁) (h' : ∀ x ∈ L₁', (s' : D.host.E) • x ∈ L') :
    ∀ A ∈ homL D L₁ L₁', (s' * s) • A ∈ homL D L L' := by
  intro A hA
  induction hA using Submodule.span_induction with
  | mem A hA =>
    apply Submodule.subset_span
    intro x hx
    have := h' _ (hA _ (h x hx))
    rw [Matrix.mulVec_smul, smul_smul] at this
    rw [Matrix.smul_mulVec, ← Nat.cast_smul_eq_nsmul D.host.E, Nat.cast_mul]
    exact this
  | zero => simp
  | add A B _ _ hA hB => rw [smul_add]; exact Submodule.add_mem _ hA hB
  | smul a A _ hA => rw [smul_comm]; exact Submodule.smul_mem _ a hA

theorem smul_mem_YYl {D : D7} {N N' : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {s : ℕ}
    (h : ∀ A ∈ homL D L₁ L₁', s • A ∈ homL D L L') :
    ∀ A ∈ YYl D L₁ L₁', s • A ∈ YYl D L L' := by
  intro A hA
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨a, ha, B, hB, rfl⟩ := hA
    exact Submodule.subset_span ⟨a, ha, s • B, h B hB, smul_comm _ _ _⟩
  | zero => simp
  | add A B _ _ hA hB => rw [smul_add]; exact Submodule.add_mem _ hA hB
  | smul a A _ hA => rw [smul_comm]; exact Submodule.smul_mem _ a hA

theorem smul_mem_La {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}
    {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {s : ℕ}
    (h : ∀ A ∈ YYl D L₁ L₁', s • A ∈ YYl D L L') :
    ∀ x ∈ La D (tor0 D cc δ) L₁ L₁', s • x ∈ La D (tor0 D cc δ) L L' := by
  intro x hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨w, hw, s • A, h A hA, ?_⟩
    funext τ i j
    simp only [embV, tor0, Pi.smul_apply, Matrix.smul_apply, map_nsmul, smul_eq_mul, nsmul_eq_mul,
      map_mul, map_natCast]
    ring
  | zero => simp
  | add A B _ _ hA hB => rw [smul_add]; exact AddSubgroup.add_mem _ hA hB
  | neg A _ hA => rw [smul_neg]; exact AddSubgroup.neg_mem _ hA

def Bd {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (C : ℝ) (z : ℂ) : Prop :=
  ∃ h : z ∈ Qbar, ‖lam ⟨z, h⟩‖ ≤ C

theorem Bd.mul {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {C C' : ℝ} {z w : ℂ}
    (hz : Bd lam C z) (hw : Bd lam C' w) : Bd lam (C * C') (z * w) := by
  obtain ⟨h, hz⟩ := hz
  obtain ⟨h', hw⟩ := hw
  refine ⟨mul_mem h h', ?_⟩
  have : (⟨z * w, mul_mem h h'⟩ : Qbar) = ⟨z, h⟩ * ⟨w, h'⟩ := rfl
  rw [this, map_mul, norm_mul]
  exact mul_le_mul hz hw (norm_nonneg _) ((norm_nonneg _).trans hz)

theorem bd_of_pow_mul_eq_one {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {z : ℂ} {n m : ℕ}
    (hn : n ≠ 0) (hm : Nat.Coprime m p) (h : z ^ n * (m : ℂ) = 1) : Bd lam 1 z := by
  have hm0 : (m : ℂ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    exact zero_ne_one h
  have hz : z ∈ Qbar := by
    rw [mem_algebraicClosure_iff]
    apply IsAlgebraic.of_pow (Nat.pos_of_ne_zero hn)
    have : z ^ n = algebraMap ℚ ℂ ((m : ℚ)⁻¹) := by
      rw [map_inv₀, map_natCast]
      exact eq_inv_of_mul_eq_one_left h
    rw [this]
    exact isAlgebraic_algebraMap _
  refine ⟨hz, ?_⟩
  have h1 : (⟨z, hz⟩ : Qbar) ^ n * (m : Qbar) = 1 := by
    apply Subtype.ext
    simpa using h
  have h2 := congrArg (fun t => ‖lam t‖) h1
  have h3 : ‖(m : ℂ_[p])‖ = 1 := by
    have : (m : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (m : ℚ_[p]) := by simp
    rw [this, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact hm.symm
  simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow, map_one, norm_one, h3, mul_one] at h2
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2).le

theorem norm_le_one_of_isIntegral {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (h : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  obtain ⟨f, hf, hx⟩ := h
  by_contra hlt
  push Not at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, map_one, one_mul] at hx
  have h1 : ‖∑ i ∈ Finset.range f.natDegree, algebraMap ℤ ℂ_[p] (f.coeff i) * x ^ i‖ < ‖x‖ ^ f.natDegree := by
    have hpos : 0 < ‖x‖ ^ f.natDegree := pow_pos (by linarith) _
    by_cases hne : (Finset.range f.natDegree).Nonempty
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
        (fun i => algebraMap ℤ ℂ_[p] (f.coeff i) * x ^ i)
      refine hle.trans_lt ?_
      rw [norm_mul, norm_pow]
      have : ‖algebraMap ℤ ℂ_[p] (f.coeff i)‖ ≤ 1 := by
        simpa using IsUltrametricDist.norm_intCast_le_one ℂ_[p] (f.coeff i)
      calc _ ≤ 1 * ‖x‖ ^ i := by gcongr
        _ < _ := by rw [one_mul]; exact pow_lt_pow_right₀ hlt (Finset.mem_range.1 hi)
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simpa using hpos
  rw [eq_neg_of_add_eq_zero_left hx, norm_neg, norm_pow] at h1
  exact lt_irrefl _ h1

theorem Hf_nsmul (D : D7) (T : Tor D) {N N' : ℕ} (n : ℕ) (x y : VC D N N') :
    Hf D T (n • x) (n • y) = (n : ℂ) ^ 2 * Hf D T x y := by
  simp only [Hf, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum, mul_div_assoc']
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem Hf_add_left (D : D7) (T : Tor D) {N N' : ℕ} (x y z : VC D N N') :
    Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_add_right (D : D7) (T : Tor D) {N N' : ℕ} (x y z : VC D N N') :
    Hf D T x (y + z) = Hf D T x y + Hf D T x z := by
  simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div]

theorem Hf_conj (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') :
    Hf D T y x = (starRingEnd ℂ) (Hf D T x y) := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

theorem U_U (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (U D T y G) z =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) * U D T (x + y) G z := by
  simp only [U, Hf_add_left, Hf_add_right, add_assoc]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  have h := Complex.sub_conj (Hf D T x y)
  rw [← Hf_conj] at h
  push_cast at h
  linear_combination (-(Real.pi : ℂ) / 2) * h

def Cmb (D : D7) (T : Tor D) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (B : AddSubgroup (VC D N N'))
    (F₀ : VC D N N' → ℂ) (n : ℕ) (C : ℝ) (G : VC D N N' → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℂ) (s : ι → VC D N N'), (∀ i, n • s i ∈ B) ∧ (∀ i, Bd lam C (r i)) ∧
    G = fun z => ∑ i, r i * U D T (s i) F₀ z

section
variable {D : D7} {T : Tor D} {N N' : ℕ} {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {B : AddSubgroup (VC D N N')}
  {F₀ : VC D N N' → ℂ} {n : ℕ}

theorem Cmb.base : Cmb D T lam B F₀ n 1 F₀ := by
  refine ⟨Unit, inferInstance, fun _ => 1, fun _ => 0, fun _ => by simp, fun _ => ?_, ?_⟩
  · exact bd_of_pow_mul_eq_one lam (n := 1) (m := 1) one_ne_zero (Nat.coprime_one_left _) (by simp)
  · funext z
    simp [U, Hf]

theorem Cmb.smul {C C' : ℝ} {G : VC D N N' → ℂ} {c : ℂ} (hc : Bd lam C' c) (hG : Cmb D T lam B F₀ n C G) :
    Cmb D T lam B F₀ n (C' * C) (fun z => c * G z) := by
  obtain ⟨ι, _, r, s, hs, hr, rfl⟩ := hG
  refine ⟨ι, inferInstance, fun i => c * r i, s, hs, fun i => hc.mul (hr i), ?_⟩
  funext z
  simp only [Finset.mul_sum, mul_assoc]

theorem Cmb.sum {C : ℝ} {κ : Type} [Fintype κ] {G : κ → VC D N N' → ℂ} (hG : ∀ k, Cmb D T lam B F₀ n C (G k)) :
    Cmb D T lam B F₀ n C (fun z => ∑ k, G k z) := by
  choose ι inst r s hs hr hG using hG
  refine ⟨Σ k, ι k, inferInstance, fun i => r i.1 i.2, fun i => s i.1 i.2, fun i => hs _ _, fun i => hr _ _, ?_⟩
  funext z
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hG k]

theorem Cmb.transl (hn : n ≠ 0) (hB : ∀ x ∈ B, ∀ y ∈ B, ∃ m : ℤ, (Hf D T x y).im = m) {C : ℝ} {G : VC D N N' → ℂ}
    {x : VC D N N'} (hx : n • x ∈ B) (hG : Cmb D T lam B F₀ n C G) :
    Cmb D T lam B F₀ n C (U D T x G) := by
  obtain ⟨ι, _, r, s, hs, hr, rfl⟩ := hG
  refine ⟨ι, inferInstance,
    fun i => Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x (s i)).im : ℂ)) * r i, fun i => x + s i,
    fun i => by rw [smul_add]; exact B.add_mem hx (hs i), fun i => ?_, ?_⟩
  · rw [← one_mul C]
    refine Bd.mul ?_ (hr i)
    obtain ⟨m, hm⟩ := hB _ hx _ (hs i)
    rw [Hf_nsmul] at hm
    have hm' : (n : ℂ) ^ 2 * ((Hf D T x (s i)).im : ℂ) = m := by
      have : ((n : ℂ) ^ 2 * Hf D T x (s i)).im = (n : ℝ) ^ 2 * (Hf D T x (s i)).im := by
        rw [← Complex.im_ofReal_mul]; push_cast; rfl
      rw [this] at hm
      exact_mod_cast hm
    refine bd_of_pow_mul_eq_one lam (n := 2 * n ^ 2) (m := 1) (by positivity) (Nat.coprime_one_left _) ?_
    rw [Nat.cast_one, mul_one, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨-m, ?_⟩
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * Complex.I) * hm'
  · funext z
    have : U D T x (fun z => ∑ i, r i * U D T (s i) F₀ z) z = ∑ i, r i * U D T x (U D T (s i) F₀) z := by
      simp only [U, Finset.sum_mul, mul_assoc]
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [U_U]
    ring

theorem Cmb.iop (hn : n ≠ 0) (hB : ∀ x ∈ B, ∀ y ∈ B, ∃ m : ℤ, (Hf D T x y).im = m) {C : ℝ} {G : VC D N N' → ℂ}
    {A₁ A₂ : AddSubgroup (VC D N N')} (hi : Nat.Coprime (A₁.addSubgroupOf A₂).index p)
    (hx : ∀ x ∈ A₂, n • x ∈ B) (hG : Cmb D T lam B F₀ n C G) :
    Cmb D T lam B F₀ n C (Iop D T A₁ A₂ G) := by
  have hi0 : (A₁.addSubgroupOf A₂).index ≠ 0 := by
    intro h0
    rw [h0, Nat.coprime_zero_left] at hi
    exact (Fact.out : p.Prime).one_lt.ne' hi
  haveI : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := AddSubgroup.fintypeOfIndexNeZero hi0
  have h1 : Bd lam 1 ((Real.sqrt ((A₁.addSubgroupOf A₂).index : ℝ))⁻¹ : ℂ) := by
    refine bd_of_pow_mul_eq_one lam (n := 2) two_ne_zero hi ?_
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 hi0)
  have h2 : ∀ y, Bd lam 1 (al D T (y : VC D N N')) := by
    intro y
    refine bd_of_pow_mul_eq_one lam (n := 2) (m := 1) two_ne_zero (Nat.coprime_one_left _) ?_
    rw [Nat.cast_one, mul_one, al, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp
  have h3 := Cmb.smul h1 (Cmb.sum fun q : A₂ ⧸ A₁.addSubgroupOf A₂ =>
    Cmb.smul (h2 ((Quotient.out q : A₂) : VC D N N')) (Cmb.transl hn hB (hx _ (Quotient.out q : A₂).2) hG))
  rw [one_mul, one_mul] at h3
  convert h3 using 1
  funext z
  simp only [Iop, finsum_eq_sum_of_fintype]

theorem Cmb.out {C : ℝ} {G : VC D N N' → ℂ} (hG : Cmb D T lam B F₀ n C G) :
    ∃ (k : ℕ) (r : Fin k → Qbar) (s : Fin k → VC D N N'), (∀ i, n • s i ∈ B) ∧ (∀ i, ‖lam (r i)‖ ≤ C) ∧
      G = fun z => ∑ i, (r i : ℂ) * U D T (s i) F₀ z := by
  obtain ⟨ι, _, r, s, hs, hr, rfl⟩ := hG
  choose h hr using hr
  let e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun i => ⟨r (e i), h _⟩, fun i => s (e i), fun i => hs _, fun i => hr _, ?_⟩
  funext z
  exact (e.sum_comp fun i => r i * U D T (s i) F₀ z).symm

end

end GlobalTheory.NormSum.KernelAt

set_option maxHeartbeats 1000000 in
open GlobalTheory.NormSum.KernelAt in

theorem GlobalTheory.NormSum.kernel_eq_sum_translates : ∀ (D : D7), Inp D → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → 0 < Q → ∀ (P : Pair D ⊤ δ t0 Q) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (g : GA D P.a) (g' k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ∃ (b : Fin (fF D * P.a * P.d) → Matrix (Fin P.d) (Fin P.a) D.host.E) (k M : ℕ) (r : Fin k → Qbar) (s : Fin k → VC D P.a P.d), OnB D b ∧ LocBasis D p (YYl D (stdL D P.a) (stdL D P.d)) b ∧ 0 < M ∧ Nat.Coprime M p ∧ (∀ i, (M * Q) • s i ∈ LaB D (tor0 D ⊤ δ) b) ∧ (∀ i, ‖lam (r i)‖ ≤ (‖(Q : ℂ_[p])‖⁻¹) ^ (P.a * P.d)) ∧ P.W.Om g g' P.F = fun z => ∑ i, (r i : ℂ) * U D (tor0 D ⊤ δ) (s i) (pullB D (tor0 D ⊤ δ) b (GL3Theta.th0 (lamOf D ⊤ δ) t0)) z := by
  intro D hI δ t0 Q hC hT hQ P p _ lam g g' k' hk' hg hg'
  have hp : p.Prime := Fact.out
  obtain ⟨Lt, hM, h1, hLt, -, hE⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D P.a
  obtain ⟨Lt', hM', h1', hLt', -, hE'⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D P.d
  obtain ⟨s₁, hs₁, hs₁a, -⟩ := hE p g hp hg
  obtain ⟨s₂, hs₂, -, hs₂a⟩ := hE' p _ hp hg'
  have he : Lt' g' = Lt' (g' * k') := (hLt' _ _).2 (by simpa using hk')
  rw [← he] at hs₂a
  have hLa := smul_mem_La ⊤ δ (smul_mem_YYl (smul_mem_homL hs₁a hs₂a))
  have hsp : Nat.Coprime (s₂ * s₁) p := Nat.Coprime.mul_left hs₂ hs₁
  obtain ⟨-, -, -, -, hfg, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hI.g1 ⊤ δ hC P.a P.d _
    (Or.inr ⟨Lt g, Lt' g', (hM g).2, (hM' g').2, rfl⟩)
  have hi₁ := coprime_index (La0 D (tor0 D ⊤ δ) P.a P.d) _ hfg _ p hp hsp hLa
  obtain ⟨b, ε, hb, hloc, hε, hεn, hi₀, he0⟩ := P.vac.2.2.2.2 p lam (by simp)
  obtain ⟨-, -, hB, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hI.g1 ⊤ δ hC P.a P.d _ (Or.inl ⟨_, b, hb, rfl⟩)
  obtain ⟨c, k, r, y, hex⟩ := GlobalTheory.T.definiteThetaPair_testVector_expansion D hI ⊤ δ t0 Q hC hT P g g' _ _ (hM g).1 (hM' g').1
  obtain ⟨⟨hc, -⟩, hy, hr, -, hOm, hcn⟩ := hex hQ
  have hcn := hcn p lam k' hk' hg hg'
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = ((LaB D (tor0 D ⊤ δ) b).addSubgroupOf (La0 D (tor0 D ⊤ δ) P.a P.d)).index := ⟨_, rfl⟩
  have hMp : Nat.Coprime (n₀ * (s₂ * s₁)) p := Nat.Coprime.mul_left (hn₀ ▸ hi₀) hsp
  have hM0 : n₀ * (s₂ * s₁) ≠ 0 := by
    intro h0
    rw [h0, Nat.coprime_zero_left] at hMp
    exact hp.one_lt.ne' hMp
  have hn : n₀ * (s₂ * s₁) * Q ≠ 0 := mul_ne_zero hM0 hQ.ne'
  have a0 : ∀ x ∈ La0 D (tor0 D ⊤ δ) P.a P.d, n₀ • x ∈ LaB D (tor0 D ⊤ δ) b := fun x hx => by
    rw [hn₀]
    exact ((LaB D (tor0 D ⊤ δ) b).addSubgroupOf (La0 D (tor0 D ⊤ δ) P.a P.d)).nsmul_index_mem ⟨x, hx⟩
  have a1 : ∀ x ∈ La D (tor0 D ⊤ δ) (Lt g) (Lt' g'), (n₀ * (s₂ * s₁)) • x ∈ LaB D (tor0 D ⊤ δ) b := fun x hx => by
    rw [mul_smul]
    exact a0 _ (hLa x hx)
  have c0 : Cmb D (tor0 D ⊤ δ) lam (LaB D (tor0 D ⊤ δ) b) (pullB D (tor0 D ⊤ δ) b (GL3Theta.th0 (lamOf D ⊤ δ) t0))
      (n₀ * (s₂ * s₁) * Q) (1 * 1) P.e0 := by
    rw [he0]
    refine Cmb.smul ⟨hε, ?_⟩ (Cmb.iop hn hB hi₀ (fun x hx => ?_) Cmb.base)
    · rw [lamC, dif_pos hε] at hεn
      exact hεn.le
    · rw [mul_assoc n₀, mul_comm n₀, mul_smul]
      exact AddSubgroup.nsmul_mem _ (a0 x hx) _
  have c1 := Cmb.iop hn hB hi₁ (fun x hx => by
    rw [mul_comm _ Q, mul_smul]
    exact AddSubgroup.nsmul_mem _ (a1 x hx) _) c0
  have hr' : ∀ i, Bd lam ((‖(Q : ℂ_[p])‖⁻¹) ^ (P.a * P.d)) (r i : ℂ) := by
    intro i
    refine ⟨(r i).2, ?_⟩
    have h := norm_le_one_of_isIntegral ((hr i).map_of_comp_eq (RingHom.id ℤ) lam (RingHom.ext_int _ _))
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h
    have hQ0 : 0 < ‖(Q : ℂ_[p])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hQ.ne')
    rw [inv_pow, ← one_div, le_div_iff₀ (pow_pos hQ0 _), mul_comm]
    exact h
  have hc' : Bd lam 1 c := ⟨hc, by
    rw [lamC, dif_pos hc] at hcn
    exact hcn.le⟩
  have c2 : ∀ i, Cmb D (tor0 D ⊤ δ) lam (LaB D (tor0 D ⊤ δ) b) (pullB D (tor0 D ⊤ δ) b (GL3Theta.th0 (lamOf D ⊤ δ) t0))
      (n₀ * (s₂ * s₁) * Q) (1 * 1) (U D (tor0 D ⊤ δ) (y i) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d)
        (La D (tor0 D ⊤ δ) (Lt g) (Lt' g')) P.e0)) := fun i => by
    refine Cmb.transl hn hB ?_ c1
    rw [mul_smul]
    exact a1 _ (hy i)
  have c3 := Cmb.smul hc' (Cmb.sum fun i => Cmb.smul (hr' i) (c2 i))
  obtain ⟨k', r', s', h₁, h₂, h₃⟩ := c3.out
  refine ⟨b, k', n₀ * (s₂ * s₁), r', s', hb, hloc, Nat.pos_of_ne_zero hM0, hMp, h₁, fun i => ?_, hOm.trans h₃⟩
  have h₄ := h₂ i
  rwa [mul_one, mul_one, one_mul] at h₄
