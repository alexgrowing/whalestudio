import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProductStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelAtPrimeEqSumTorsionTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.NormSum.Term

def Bd {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (B : ℝ) (x : ℂ) : Prop :=
  x ∈ Qbar ∧ ‖lamC lam x‖ ≤ B

section
variable {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]}

theorem lamC_coe (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC, x.2]

theorem Bd.coe {B : ℝ} {x : Qbar} (h : ‖lam x‖ ≤ B) : Bd lam B (x : ℂ) :=
  ⟨x.2, by rwa [lamC_coe]⟩

theorem Bd.mono {B B' : ℝ} {x : ℂ} (h : Bd lam B x) (hB : B ≤ B') : Bd lam B' x :=
  ⟨h.1, h.2.trans hB⟩

theorem Bd.zero {B : ℝ} (hB : 0 ≤ B) : Bd lam B 0 := by
  have := Bd.coe (lam := lam) (B := B) (x := 0) (by simpa using hB)
  simpa using this

theorem Bd.add {B : ℝ} {x y : ℂ} (hx : Bd lam B x) (hy : Bd lam B y) : Bd lam B (x + y) := by
  obtain ⟨hx, h1⟩ := hx
  obtain ⟨hy, h2⟩ := hy
  lift x to Qbar using hx
  lift y to Qbar using hy
  rw [lamC_coe] at h1 h2
  have := Bd.coe (lam := lam) (B := B) (x := x + y) (by
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2))
  simpa using this

theorem Bd.mul {A B : ℝ} {x y : ℂ} (hx : Bd lam A x) (hy : Bd lam B y) : Bd lam (A * B) (x * y) := by
  obtain ⟨hx, h1⟩ := hx
  obtain ⟨hy, h2⟩ := hy
  lift x to Qbar using hx
  lift y to Qbar using hy
  rw [lamC_coe] at h1 h2
  have := Bd.coe (lam := lam) (B := A * B) (x := x * y) (by
    rw [map_mul, norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1))
  simpa using this

theorem Bd.sum {ι : Type*} {B : ℝ} (hB : 0 ≤ B) (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, Bd lam B (f i)) :
    Bd lam B (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Bd lam B) (fun _ _ => Bd.add) (Bd.zero hB) h

theorem Bd.intCast (z : ℤ) : Bd lam 1 (z : ℂ) := by
  have := Bd.coe (lam := lam) (B := 1) (x := (z : Qbar)) (by
    rw [map_intCast]
    exact IsUltrametricDist.norm_intCast_le_one _ z)
  simpa using this

theorem Bd.prod_coe {n : ℕ} {A : ℝ} (c : Fin n → Qbar) (h : ∀ i, ‖lam (c i)‖ ≤ A) :
    Bd lam (A ^ n) (∏ i, (c i : ℂ)) := by
  have := Bd.coe (lam := lam) (B := A ^ n) (x := ∏ i, c i) (by
    rw [map_prod, norm_prod]
    calc ∏ i, ‖lam (c i)‖ ≤ ∏ _i : Fin n, A :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => h i)
      _ = A ^ n := by simp)
  simpa using this

theorem bd_applyAt0 (D : D7) {a d n : ℕ} {B : ℝ} (hB : 0 ≤ B) (G : VC D a d → ℂ)
    (P : MvPolynomial (GL3Theta.Idx D a d) ℤ) (hP : P.IsHomogeneous n)
    (h : ∀ f : Fin n → GL3Theta.Idx D a d, Bd lam B (iteratedFDeriv ℂ n G 0 (fun i => coordV D (f i)))) :
    Bd lam B (GL3Theta.applyAt0 D (MvPolynomial.map (Int.castRingHom ℂ) P) G) := by
  have h' : ∀ m, m = n → ∀ f : Fin m → GL3Theta.Idx D a d,
      Bd lam B (iteratedFDeriv ℂ m G 0 (fun i => coordV D (f i))) := by
    rintro m rfl; exact h
  refine Bd.sum hB _ _ fun α hα => ?_
  have hα' : MvPolynomial.coeff α P ≠ 0 :=
    MvPolynomial.mem_support_iff.1 (MvPolynomial.support_map_subset _ _ hα)
  have hdeg : Multiset.card α.toMultiset = n := by
    have h1 := hP hα'
    rw [Finsupp.card_toMultiset]
    rw [← h1, Finsupp.weight_apply]
    simp only [Pi.one_apply, smul_eq_mul, mul_one]
    rfl
  have hne : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [taylor, mul_assoc, mul_div_cancel₀ _ hne, MvPolynomial.coeff_map]
  have := (Bd.intCast (lam := lam) (MvPolynomial.coeff α P)).mul (h' _ hdeg
    (fun i => α.toMultiset.toList.get ⟨i, by simpa using i.2⟩))
  rw [one_mul] at this
  exact this

theorem bd_coord (D : D7) {a d n : ℕ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (T : Tor D) (hT : ∀ τ x, T.emb τ x = embT D τ x)
    (Y : Set (Matrix (Fin d) (Fin a) D.host.E))
    (hL : ∀ k : GL3Theta.Idx D a d, ∃ (m : ℕ) (c : Fin m → Qbar) (y : Fin m → Matrix (Fin d) (Fin a) D.host.E),
        (∀ i, y i ∈ Y) ∧ (∀ i, ‖lam (c i)‖ ≤ A) ∧
        coordV D k = ∑ i, (c i : ℂ) • (fun τ s t => embT D τ (y i s t) : VC D a d))
    (φ : ContinuousMultilinearMap ℂ (fun _ : Fin n => VC D a d) ℂ)
    (h : ∀ y : Fin n → Matrix (Fin d) (Fin a) D.host.E, (∀ i, y i ∈ Y) → Bd lam B (φ fun i => embV D T (y i)))
    (f : Fin n → GL3Theta.Idx D a d) : Bd lam (A ^ n * B) (φ fun i => coordV D (f i)) := by
  choose m c y hy hc he using hL
  have h1 : (fun i => coordV D (f i)) = fun i => ∑ j, (c (f i) j : ℂ) • embV D T (y (f i) j) := by
    funext i
    rw [he]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    funext τ s t
    simp [embV, hT]
  rw [h1, φ.map_sum]
  refine Bd.sum (by positivity) _ _ fun r _ => ?_
  rw [φ.map_smul_univ, smul_eq_mul]
  exact (Bd.prod_coe (fun i => c (f i) (r i)) fun i => hc _ _).mul (h _ fun i => hy _ _)

end

def minorZ (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) : MvPolynomial (GL3Theta.Idx D a d) ℤ :=
  ∏ τ, ∏ j, (Matrix.of fun i i' : Fin a =>
    (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℤ)).det

theorem map_minorZ (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) :
    MvPolynomial.map (Int.castRingHom ℂ) (minorZ D T) = minorPol D T := by
  simp only [minorZ, minorPol, map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1
  ext i i' : 2
  simp

theorem minorZ_homogeneous (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) :
    (minorZ D T).IsHomogeneous (a * ∑ τ, n τ) := by
  have h : a * ∑ τ, n τ = ∑ τ, ∑ _j : Fin (n τ), a := by
    simp [Finset.mul_sum, mul_comm]
  rw [h]
  refine MvPolynomial.IsHomogeneous.prod _ _ _ fun τ _ => MvPolynomial.IsHomogeneous.prod _ _ _ fun j _ => ?_
  rw [Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h2 := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin a))
    (fun i => (MvPolynomial.X (τ, (T τ j).1 (σ i), i) : MvPolynomial (GL3Theta.Idx D a d) ℤ)) (fun _ => 1)
    (fun i _ => MvPolynomial.isHomogeneous_X _ _)
  have h3 := (MvPolynomial.isHomogeneous_C (GL3Theta.Idx D a d) ((Equiv.Perm.sign σ : ℤˣ) : ℤ)).mul h2
  simpa using h3

theorem differentiable_evenTheta (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (h : Crv D cc δ) :
    Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) := by
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ h
  have hs : Differentiable ℂ (sgStar (lamOf D cc δ)) := by
    refine (GlobalTheory.OddTheta.sgStar_laws _ ⟨L.ω₁, L.ω₂, L.indep, ?_⟩).1.1
    ext z
    rw [hL, PeriodPair.lattice, ← Submodule.span_int_eq_addSubgroupClosure]
    rfl
  unfold GL3Theta.th0 U1
  fun_prop

theorem contDiff_U_pullB (D : D7) (T : Tor D) {a d r : ℕ} (b : Fin r → Matrix (Fin d) (Fin a) D.host.E)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) (s : VC D a d) (n : ℕ) : ContDiff ℂ n (U D T s (pullB D T b g)) := by
  have hg' : ContDiff ℂ n g := hg.contDiff
  have h1 : ContDiff ℂ n (pullB D T b g) := by
    unfold pullB coordB
    refine contDiff_prod fun j _ => ?_
    fun_prop
  unfold U Hf
  fun_prop

theorem norm_natCast_inv (p : ℕ) [Fact p.Prime] {Q : ℕ} (hQ : Q ≠ 0) :
    ‖(Q : ℂ_[p])‖⁻¹ = (p : ℝ) ^ (padicValNat p Q : ℝ) := by
  have h1 : (Q : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (Q : ℚ_[p]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hQ), Padic.valuation_natCast]
  simp

theorem iteratedFDeriv_comb {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ} (n : ℕ)
    (r : Fin k → ℂ) (G : Fin k → V → ℂ) (hG : ∀ i, ContDiff ℂ n (G i)) (y : Fin n → V) :
    iteratedFDeriv ℂ n (fun z => ∑ i, r i * G i z) 0 y = ∑ i, r i * iteratedFDeriv ℂ n (G i) 0 y := by
  have h1 : (fun z => ∑ i, r i * G i z) = ∑ i, r i • G i := by
    funext z; simp
  rw [h1, iteratedFDeriv_sum_apply (f := fun i => r i • G i) (fun i _ => ((hG i).const_smul (r i)).contDiffAt),
    sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_const_smul_apply (hG i).contDiffAt, smul_apply, smul_eq_mul]

theorem rpow_collect {x : ℝ} (hx : 0 < x) (c : Prop) [Decidable c] (n m : ℕ) (u v : ℝ) :
    (x ^ u) ^ n * ((x ^ v) ^ m * ((x ^ v) ^ n * (if c then x ^ ((n : ℝ) / 4) else 1))) =
      x ^ ((n : ℝ) * (u + (if c then 1 / 4 else 0) + v) + (m : ℝ) * v) := by
  have he' : (if c then x ^ ((n : ℝ) / 4) else 1) = x ^ ((n : ℝ) * (if c then 1 / 4 else 0)) := by
    split_ifs
    · congr 1; ring
    · simp
  rw [he', ← Real.rpow_mul_natCast hx.le, ← Real.rpow_mul_natCast hx.le, ← Real.rpow_mul_natCast hx.le,
    ← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1
  ring

theorem term_bound : ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → GoodLevel D Q → ∀ (P : Pair D ⊤ δ t0 Q) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (g : GA D P.a) (g' k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ∀ T, P.term g g' T ∈ Qbar ∧ ‖lamC lam (P.term g g' T)‖ ≤ (p : ℝ) ^ (((P.a * ∑ τ, P.n τ : ℕ) : ℝ) * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) + ((P.a * P.d : ℕ) : ℝ) * (padicValNat p Q : ℝ)) := by
  intro D hI S dl hL δ t0 Q hC ht hQ P p _ lam g g' k' hk hg hg' T
  obtain ⟨b, k, M, r, s, hb, hloc, hM, hMp, hs, hr, hF⟩ :=
    GlobalTheory.T.kernelAtPrime_eq_sum_torsionTranslates D hI δ t0 Q hC ht hQ.1 P p lam g g' k' hk hg hg'
  have hp : p.Prime := Fact.out
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hQn := norm_natCast_inv p hQ.1.ne'
  have hN : ‖((M * Q : ℕ) : ℂ_[p])‖⁻¹ = (p : ℝ) ^ (padicValNat p Q : ℝ) := by
    rw [norm_natCast_inv p (Nat.mul_pos hM hQ.1).ne', padicValNat.mul hM.ne' hQ.1.ne',
      padicValNat.eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.1 hMp.symm), zero_add]
  have hsp : p ∣ M * Q → SplitIn D p := fun h =>
    hQ.2 p hp (hMp.symm.dvd_of_dvd_mul_left h)
  have he0 : 0 ≤ (if p = D.host.d then (p : ℝ) ^ (((P.a * ∑ τ, P.n τ : ℕ) : ℝ) / 4) else 1) := by
    split_ifs <;> positivity
  rw [← rpow_collect hp0, Pair.term, ← map_minorZ, hF]
  refine bd_applyAt0 (lam := lam) D (by positivity) _ _ (minorZ_homogeneous D T) fun f => ?_
  refine bd_coord D (by positivity) (by positivity) (tor0 D ⊤ δ) (fun _ _ => rfl)
    (YYl D (stdL D P.a) (stdL D P.d)) (hL.2.2.2.2 p lam P.a P.d) _ (fun y hy => ?_) f
  rw [iteratedFDeriv_comb _ (fun i => (r i : ℂ))
    (fun i => U D (tor0 D ⊤ δ) (s i) (pullB D (tor0 D ⊤ δ) b (GL3Theta.th0 (lamOf D ⊤ δ) t0))) fun i =>
    contDiff_U_pullB D _ b _ (differentiable_evenTheta D ⊤ δ t0 hC) (s i) _]
  refine Bd.sum (by positivity) _ _ fun i _ => ?_
  have h1 := hr i
  rw [hQn] at h1
  refine (Bd.coe h1).mul ?_
  have := GlobalTheory.T.jets_torsion_translates_cm_theta_product D hI p lam ⊤ δ hC (by simp) t0 ht P.a P.d _ b hb hloc (s i) (M * Q)
    (Nat.mul_pos hM hQ.1) (hs i) hsp _ y hy
  rw [hN] at this
  exact this

end GlobalTheory.NormSum.Term
