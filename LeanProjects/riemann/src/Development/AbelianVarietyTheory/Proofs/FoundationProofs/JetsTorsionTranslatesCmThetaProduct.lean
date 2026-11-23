import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionTranslateThetaJetsDenominatorBoundStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ProductJets

def AlgLe {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : ℂ) (t : ℝ) : Prop :=
  x ∈ Qbar ∧ ‖lamC lam x‖ ≤ t

section
variable {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]}

theorem lamC_coe (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC, x.2]

theorem AlgLe.nonneg {x : ℂ} {t : ℝ} (h : AlgLe lam x t) : 0 ≤ t := (norm_nonneg _).trans h.2

theorem AlgLe.mul {x y : ℂ} {t u : ℝ} (h : AlgLe lam x t) (h' : AlgLe lam y u) :
    AlgLe lam (x * y) (t * u) := by
  have h0 := h.nonneg
  obtain ⟨hx, h⟩ := h
  obtain ⟨hy, h'⟩ := h'
  lift x to Qbar using hx
  lift y to Qbar using hy
  refine ⟨mul_mem x.2 y.2, ?_⟩
  rw [← MulMemClass.coe_mul, lamC_coe, map_mul, norm_mul]
  rw [lamC_coe] at h h'
  exact mul_le_mul h h' (norm_nonneg _) h0

theorem AlgLe.add {x y : ℂ} {t : ℝ} (h : AlgLe lam x t) (h' : AlgLe lam y t) :
    AlgLe lam (x + y) t := by
  obtain ⟨hx, h⟩ := h
  obtain ⟨hy, h'⟩ := h'
  lift x to Qbar using hx
  lift y to Qbar using hy
  refine ⟨add_mem x.2 y.2, ?_⟩
  rw [← AddMemClass.coe_add, lamC_coe, map_add]
  rw [lamC_coe] at h h'
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

theorem AlgLe.zero {t : ℝ} (ht : 0 ≤ t) : AlgLe lam 0 t := by
  refine ⟨zero_mem _, ?_⟩
  rw [← ZeroMemClass.coe_zero Qbar, lamC_coe, map_zero, norm_zero]
  exact ht

theorem AlgLe.one : AlgLe lam 1 1 := by
  refine ⟨one_mem _, ?_⟩
  rw [← OneMemClass.coe_one Qbar, lamC_coe, map_one, norm_one]

theorem AlgLe.sum {ι : Type*} (s : Finset ι) {f : ι → ℂ} {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ i ∈ s, AlgLe lam (f i) t) : AlgLe lam (∑ i ∈ s, f i) t :=
  Finset.sum_induction f (fun x => AlgLe lam x t) (fun _ _ => AlgLe.add) (AlgLe.zero ht) h

theorem AlgLe.prod {ι : Type*} (s : Finset ι) {f : ι → ℂ} {t : ι → ℝ}
    (h : ∀ i ∈ s, AlgLe lam (f i) (t i)) : AlgLe lam (∏ i ∈ s, f i) (∏ i ∈ s, t i) := by
  induction s using Finset.induction_on with
  | empty => simpa using AlgLe.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (by simp)).mul (ih fun i hi => h i (by simp [hi]))

theorem norm_le_one_of_map {B C : Type*} [CommRing B] [NormedField C] [IsUltrametricDist C] (f : B →+* C)
    {x : B} (hx : IsIntegral ℤ x) : ‖f x‖ ≤ 1 := by
  have h2 : IsIntegral ℤ (f x) := hx.map f.toIntAlgHom
  have h : f x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral h2.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem AlgLe.of_isIntegral {x : ℂ} (hx : IsIntegral ℤ x) : AlgLe lam x 1 := by
  have hq : x ∈ Qbar := by
    rw [mem_algebraicClosure_iff]
    exact (hx.tower_top (A := ℚ)).isAlgebraic
  refine ⟨hq, ?_⟩
  lift x to Qbar using hq
  rw [lamC_coe]
  have h1 : IsIntegral ℤ x :=
    (isIntegral_algHom_iff (Qbar.val.toRingHom.toIntAlgHom) Subtype.val_injective).1 hx
  exact norm_le_one_of_map lam h1

theorem AlgLe.inv_natCast {s : ℕ} (hs : Nat.Coprime s p) : AlgLe lam ((s : ℂ)⁻¹) 1 := by
  have e : ((s : ℂ)⁻¹) = (((s : Qbar)⁻¹ : Qbar) : ℂ) := by simp
  rw [e]
  refine ⟨SetLike.coe_mem _, ?_⟩
  rw [lamC_coe, map_inv₀, map_natCast, norm_inv]
  have h1 := PadicComplex.norm_extends' p (s : ℚ_[p])
  have h2 : ‖(s : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]; exact hs.symm
  have h3 : ‖(s : ℂ_[p])‖ = 1 := by
    rw [← h2, ← h1]; simp
  rw [h3]; simp

theorem algLe_iteratedFDeriv_prod {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {r : ℕ}
    (l : Fin r → V →L[ℂ] ℂ) {A : ℝ} (n : ℕ) :
    ∀ (g : Fin r → ℂ → ℂ) (t : Fin r → ℝ), (∀ j, Differentiable ℂ (g j)) →
      (∀ j k, AlgLe lam (iteratedDeriv k (g j) 0) (t j * A ^ k)) → 0 ≤ A →
      ∀ v : Fin n → V, (∀ i j, AlgLe lam (l j (v i)) 1) →
      AlgLe lam (iteratedFDeriv ℂ n (fun z => ∏ j, g j (l j z)) 0 v) ((∏ j, t j) * A ^ n) := by
  have hcd : ∀ (g : Fin r → ℂ → ℂ), (∀ j, Differentiable ℂ (g j)) → ∀ m : WithTop ℕ∞,
      ContDiff ℂ m (fun z => ∏ j, g j (l j z)) := fun g hg m =>
    contDiff_prod fun j _ => ((hg j).contDiff).comp (l j).contDiff
  induction n with
  | zero =>
    intro g t hg ht hA v hv
    simp only [iteratedFDeriv_zero_apply, map_zero, pow_zero, mul_one]
    exact AlgLe.prod _ fun j _ => by simpa using ht j 0
  | succ n ih =>
    intro g t hg ht hA v hv
    have hg' : ∀ j i, Differentiable ℂ (Function.update g j (deriv (g j)) i) := by
      intro j i
      by_cases h : i = j
      · subst h; simpa using (hg i).deriv
      · simpa [h] using hg i
    have hfd : (fun y => fderiv ℂ (fun z => ∏ j, g j (l j z)) y (v (Fin.last n))) =
        fun y => ∑ j, l j (v (Fin.last n)) • ∏ i, Function.update g j (deriv (g j)) i (l i y) := by
      funext y
      have h1 : ∀ j ∈ Finset.univ, HasFDerivAt (fun z => g j (l j z)) (deriv (g j) (l j y) • l j) y :=
        fun j _ => ((hg j) (l j y)).hasDerivAt.comp_hasFDerivAt y (l j).hasFDerivAt
      rw [(HasFDerivAt.finsetProd h1).fderiv, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h0 : ∏ i ∈ Finset.univ.erase j, Function.update g j (deriv (g j)) i (l i y) =
          ∏ i ∈ Finset.univ.erase j, g i (l i y) :=
        Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self, h0]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [iteratedFDeriv_succ_apply_right,
      ← iteratedFDeriv_clm_apply_const_apply (n := n) ((hcd g hg (n + 1)).fderiv_right le_rfl) le_rfl,
      hfd, iteratedFDeriv_fun_sum_apply fun j _ => ((hcd _ (hg' j) n).const_smul _).contDiffAt,
      ContinuousMultilinearMap.sum_apply]
    have ht0 : ∀ j, 0 ≤ t j := fun j => by simpa using (ht j 0).nonneg
    refine AlgLe.sum _ (mul_nonneg (Finset.prod_nonneg fun j _ => ht0 j) (pow_nonneg hA _)) fun j _ => ?_
    rw [iteratedFDeriv_const_smul_apply' (hcd _ (hg' j) n).contDiffAt, ContinuousMultilinearMap.smul_apply,
      smul_eq_mul]
    have h2 := ih _ (Function.update t j (t j * A)) (hg' j) (by
      intro i k
      by_cases h : i = j
      · subst h
        simp only [Function.update_self]
        rw [← iteratedDeriv_succ', mul_assoc, ← pow_succ']
        exact ht i (k + 1)
      · simpa [h] using ht i k) hA (Fin.init v) fun i j => hv _ j
    have h3 := (hv (Fin.last n) j).mul h2
    convert h3 using 1
    rw [Finset.prod_update_of_mem (Finset.mem_univ j), ← Finset.mul_prod_erase _ t (Finset.mem_univ j),
      Finset.sdiff_singleton_eq_erase]
    ring

end

variable {D : D7}

def coordL (T : Tor D) {a d r : ℕ} (b : Fin r → Matrix (Fin d) (Fin a) D.host.E) (j : Fin r) :
    VC D a d →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := coordB D T b j
      map_add' := fun x y => by simp [coordB, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [coordB, Finset.mul_sum, mul_assoc] }

theorem coordL_apply (T : Tor D) {a d r : ℕ} (b : Fin r → Matrix (Fin d) (Fin a) D.host.E) (j : Fin r)
    (z : VC D a d) : coordL T b j z = coordB D T b j z := rfl

theorem coordL_embV (h : TraceMapNormalisation D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Orthonormal D b) (j k : Fin r) :
    coordL (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if k = j then 1 else 0 := by
  have h1 := h (∑ i, ∑ i', b k i i' * D.host.conj (b j i i'))
  have h2 := hb k j
  unfold hYY at h2
  rw [h2] at h1
  have h3 : coordL (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) =
      ∑ τ, embT D τ (∑ i, ∑ i', b k i i' * D.host.conj (b j i i')) := by
    simp only [coordL_apply, coordB, embV, tor0, map_sum, map_mul, WeightFamilies.emb_conj]
    rfl
  rw [h3, h1]
  split_ifs <;> simp

theorem coordL_sum (h : TraceMapNormalisation D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Orthonormal D b) (j : Fin r) (c : Fin r → ℂ) :
    coordL (tor0 D cc δ) b j (∑ k, c k • embV D (tor0 D cc δ) (b k)) = c j := by
  simp [map_sum, map_smul, coordL_embV h cc δ hb]

theorem exists_coord_of_mem_LaB (T : Tor D) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} {x : VC D a d} (hx : x ∈ LaB D T b) :
    ∃ w : Fin r → ℂ, (∀ j, w j ∈ T.abelian₂) ∧ x = ∑ j, w j • embV D T (b j) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, j, rfl⟩ := hx
    refine ⟨Pi.single j w, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simpa using hw
      · simp [h]
    · rw [Finset.sum_eq_single j] <;> simp +contextual
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hy
    exact ⟨w + w', fun j => add_mem (hw j) (hw' j), by simp [add_smul, Finset.sum_add_distrib]⟩
  | neg x _ hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨-w, fun j => neg_mem (hw j), by simp⟩

theorem Hf_sum (T : Tor D) {a d r : ℕ} (b : Fin r → Matrix (Fin d) (Fin a) D.host.E) (c : Fin r → ℂ)
    (z : VC D a d) :
    Hf D T z (∑ k, c k • embV D T (b k)) = (∑ k, coordB D T b k z * (starRingEnd ℂ) (c k)) / (area T.abelian₂ : ℂ) := by
  unfold Hf coordB
  congr 1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, embV]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem U_pullB (h : TraceMapNormalisation D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Orthonormal D b) (c : Fin r → ℂ) (g : ℂ → ℂ) :
    U D (tor0 D cc δ) (∑ k, c k • embV D (tor0 D cc δ) (b k)) (pullB D (tor0 D cc δ) b g) =
      fun z => ∏ j, U1 (lamOf D cc δ) (c j) g (coordL (tor0 D cc δ) b j z) := by
  funext z
  unfold U U1 pullB
  rw [Hf_sum, Hf_sum, Finset.prod_mul_distrib, ← Complex.exp_sum]
  simp only [← coordL_apply, map_add, coordL_sum h cc δ hb]
  congr 2
  simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib, tor0]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem differentiable_U1 (Λ : AddSubgroup ℂ) (ω : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (U1 Λ ω g) := by
  unfold U1
  fun_prop

theorem algLe_coord {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (h : admG1 D)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Orthonormal D b)
    {Y : Submodule (𝓞 D.host.E) (Matrix (Fin d) (Fin a) D.host.E)} (hY : LocBasis D p Y b)
    {y : Matrix (Fin d) (Fin a) D.host.E} (hy : y ∈ Y) (j : Fin r) :
    AlgLe lam (coordL (tor0 D cc δ) b j (embV D (tor0 D cc δ) y)) 1 := by
  obtain ⟨s, hs, c, hc⟩ := hY.2.2 y hy
  have hs0 : (s : ℂ) ≠ 0 := by
    rintro h0
    have : s = 0 := by exact_mod_cast h0
    subst this
    exact (Fact.out : p.Prime).one_lt.ne' (by simpa using hs)
  have h1 : embV D (tor0 D cc δ) y = ∑ k, ((s : ℂ)⁻¹ * D.host.φ₀ ((c k : D.host.K) : D.host.E)) •
      embV D (tor0 D cc δ) (b k) := by
    funext τ i i'
    have h2 := congrArg (fun M : Matrix (Fin d) (Fin a) D.host.E => embT D τ (M i i')) hc
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, map_mul, map_sum, map_natCast, h.1 τ] at h2
    simp only [embV, tor0, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, ← h2]
    field_simp
  rw [h1, coordL_sum h.2 cc δ hb]
  have h3 : IsIntegral ℤ (D.host.φ₀ ((c j : D.host.K) : D.host.E)) :=
    (c j).isIntegral_coe.map (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
  simpa using (AlgLe.inv_natCast (lam := lam) hs).mul (AlgLe.of_isIntegral h3)

theorem jets_translate_product : ∀ (D : D7), Inp D → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → Nat.Coprime (Ideal.absNorm cc) p → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d r : ℕ) (b : Fin r → Matrix (Fin d) (Fin a) D.host.E), OnB D b → LocBasis D p (YYl D (stdL D a) (stdL D d)) b → ∀ (s : VC D a d) (Nn : ℕ), 0 < Nn → Nn • s ∈ LaB D (tor0 D cc δ) b → (p ∣ Nn → SplitIn D p) → ∀ (n : ℕ) (y : Fin n → Matrix (Fin d) (Fin a) D.host.E), (∀ i, y i ∈ YYl D (stdL D a) (stdL D d)) → iteratedFDeriv ℂ n (U D (tor0 D cc δ) s (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0))) 0 (fun i => embV D (tor0 D cc δ) (y i)) ∈ Qbar ∧ ‖lamC lam (iteratedFDeriv ℂ n (U D (tor0 D cc δ) s (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0))) 0 (fun i => embV D (tor0 D cc δ) (y i)))‖ ≤ (‖(Nn : ℂ_[p])‖⁻¹) ^ n * (if p = D.host.d then (p : ℝ) ^ ((n : ℝ) / 4) else 1) := by
  intro D hI p _ lam cc δ hC hcop t0 ht0 a d r b hb hY s Nn hN hs hsp n y hy
  obtain ⟨w, hw, hsw⟩ := exists_coord_of_mem_LaB _ hs
  have hN0 : (Nn : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs' : s = ∑ k, ((Nn : ℂ)⁻¹ * w k) • embV D (tor0 D cc δ) (b k) := by
    simp only [mul_smul, ← Finset.smul_sum, ← hsw]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
  have hsg := (GlobalTheory.OddTheta.sgStar_laws _ (GlobalTheory.CurveLattice.lattice_of_curve D hI.g1 cc δ hC).1).1.1
  have hth : Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) :=
    (differentiable_U1 _ _ hsg).div_const _
  set A : ℝ := ‖(Nn : ℂ_[p])‖⁻¹ * (if p = D.host.d then (p : ℝ) ^ ((1 : ℝ) / 4) else 1) with hA
  have hAk : ∀ k : ℕ, (‖(Nn : ℂ_[p])‖⁻¹) ^ k * (if p = D.host.d then (p : ℝ) ^ ((k : ℝ) / 4) else 1) =
      A ^ k := by
    intro k
    rw [hA, mul_pow]
    congr 1
    split_ifs
    · rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
      congr 1
      ring
    · simp
  have hA0 : 0 ≤ A := by
    rw [hA]
    split_ifs <;> positivity
  rw [hs', U_pullB hI.g1.2 cc δ hb.1, hAk]
  have key := algLe_iteratedFDeriv_prod (lam := lam) (coordL (tor0 D cc δ) b) (A := A) n
    (fun j => U1 (lamOf D cc δ) ((Nn : ℂ)⁻¹ * w j) (GL3Theta.th0 (lamOf D cc δ) t0)) (fun _ => 1)
    (fun j => differentiable_U1 _ _ hth) (fun j k => by
      rw [one_mul, ← hAk]
      refine GlobalTheory.T.torsionTranslate_theta_jets_denominator_bound D hI p lam cc δ hC hcop t0 ht0 _ Nn hN ?_ hsp k
      rw [mul_inv_cancel_left₀ hN0]
      exact hw j) hA0 (fun i => embV D (tor0 D cc δ) (y i))
    fun i j => algLe_coord lam hI.g1 cc δ hb.1 hY (hy i) j
  simpa [AlgLe] using key

end GlobalTheory.ProductJets
