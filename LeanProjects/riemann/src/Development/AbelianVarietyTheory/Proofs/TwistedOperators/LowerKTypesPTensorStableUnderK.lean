import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKStableOnOfLieStableFiniteDim

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet

section VmStab

variable {n : ℕ}

theorem vmstab_entry_zero {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (h : k * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * k) {a b : Fin n} (hab : ε a ≠ ε b) : k a b = 0 := by
  have h1 := congrFun (congrFun h a) b
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb, ne_eq, not_true_eq_false] at hab
  · simp only [ha, hb, Bool.false_eq_true, if_false, if_true] at h1
    linear_combination h1 / 2
  · simp only [ha, hb, Bool.false_eq_true, if_false, if_true] at h1
    linear_combination -h1 / 2

theorem vmstab_inK_ct {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inK ε Y) : Yᴴ = -Y := by
  obtain ⟨hG, hc⟩ := h
  have hJ := Jm_mul_self ε
  unfold Formalism.REAL.inG at hG
  calc Yᴴ = Yᴴ * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) := by rw [hJ, Matrix.mul_one]
    _ = (Yᴴ * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by rw [Matrix.mul_assoc]
    _ = -(Formalism.REAL.Jm ε * Y) * Formalism.REAL.Jm ε := by rw [eq_neg_of_add_eq_zero_left hG]
    _ = -(Y * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by rw [← hc]
    _ = -Y := by rw [Matrix.neg_mul, Matrix.mul_assoc, hJ, Matrix.mul_one]

theorem vmstab_inK_smul {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inK ε Y) (t : ℝ) :
    Formalism.REAL.inK ε ((t : ℂ) • Y) := by
  obtain ⟨hG, hc⟩ := h
  refine ⟨?_, ?_⟩
  · unfold Formalism.REAL.inG at hG ⊢
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, Complex.conj_ofReal,
      ← smul_add, hG, smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hc]

theorem vmstab_mem_KC {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (h : k ∈ Formalism.REAL.Kset ε) :
    k ∈ KC ε ∧ kᴴ ∈ KC ε := by
  obtain ⟨hu, hc⟩ := h
  have hr : k * kᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff).1 hu
    simpa [Matrix.star_eq_conjTranspose] using this
  have hl : kᴴ * k = 1 := mul_eq_one_comm.1 hr
  have hc' : kᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * kᴴ := by
    have := congrArg Matrix.conjTranspose hc
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose] at this
    exact this.symm
  exact ⟨⟨⟨⟨k, kᴴ, hr, hl⟩, rfl⟩, hc⟩, ⟨⟨kᴴ, k, hl, hr⟩, rfl⟩, hc'⟩

theorem vmstab_conj_thE {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (h : k ∈ Formalism.REAL.Kset ε)
    (p : Fin n × Fin n) :
    k⁻¹ * thE ε p * k = ∑ q : Fin n × Fin n, (k p.1 q.1 * star (k p.2 q.2)) • thE ε q := by
  obtain ⟨hu, hc⟩ := h
  have hl : kᴴ * k = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').1 hu
    simpa [Matrix.star_eq_conjTranspose] using this
  rw [Matrix.inv_eq_left_inv hl]
  obtain ⟨a, b⟩ := p
  ext i j
  simp [thE, Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum, ite_and]
  by_cases h1 : ε a = ε j
  · by_cases h2 : ε b = ε i
    · simp only [Formalism.REAL.sgn, h1, h2]
      ring
    · rw [vmstab_entry_zero hc h2]
      simp
  · rw [vmstab_entry_zero hc h1]
    simp

theorem vmstab_hasDerivAt_entry (Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Y) a b) (Y a b) 0 := by
  have h1 : HasDerivAt (fun z : ℂ => NormedSpace.exp (z • Y)) (NormedSpace.exp ((0 : ℂ) • Y) * Y) 0 :=
    hasDerivAt_exp_smul_const Y 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h1
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a b)
  have h2 : HasDerivAt (fun z : ℂ => L (NormedSpace.exp (z • Y))) (L Y) ((0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_zero]
    exact L.hasFDerivAt.comp_hasDerivAt 0 h1
  exact h2.comp_ofReal

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def vmAct (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (k : Matrix (Fin n) (Fin n) ℂ) :
    PiLp 2 (fun _ : Fin n × Fin n => W) →ₗ[ℂ] PiLp 2 (fun _ : Fin n × Fin n => W) where
  toFun G := WithLp.toLp 2 fun q => ∑ p : Fin n × Fin n, (k p.1 q.1 * star (k p.2 q.2)) • τ kᴴ (G p)
  map_add' F G := by
    ext q
    simp [Finset.sum_add_distrib]
  map_smul' c G := by
    ext q
    simp [Finset.smul_sum, smul_smul, mul_comm]

theorem vmAct_apply (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (k : Matrix (Fin n) (Fin n) ℂ)
    (G : PiLp 2 (fun _ : Fin n × Fin n => W)) (q : Fin n × Fin n) :
    vmAct τ k G q = ∑ p : Fin n × Fin n, (k p.1 q.1 * star (k p.2 q.2)) • τ kᴴ (G p) := rfl

theorem vmAct_one (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (h : τ 1 = 1)
    (G : PiLp 2 (fun _ : Fin n × Fin n => W)) : vmAct τ 1 G = G := by
  ext q
  rw [vmAct_apply, Matrix.conjTranspose_one, h, Finset.sum_eq_single q]
  · simp
  · intro p _ hp
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    by_cases h1 : p1 = q1
    · by_cases h2 : p2 = q2
      · exact absurd (by rw [h1, h2]) hp
      · simp [Matrix.one_apply, h2]
    · simp [Matrix.one_apply, h1]
  · intro hq
    exact absurd (Finset.mem_univ q) hq

theorem vmAct_mul (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (k l : Matrix (Fin n) (Fin n) ℂ)
    (h : τ (lᴴ * kᴴ) = τ lᴴ * τ kᴴ) (G : PiLp 2 (fun _ : Fin n × Fin n => W)) :
    vmAct τ (k * l) G = vmAct τ l (vmAct τ k G) := by
  ext q
  simp only [vmAct_apply, Matrix.conjTranspose_mul, h, ContinuousLinearMap.mul_apply, map_sum, map_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mul_apply, star_sum, star_mul', Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

def vmGen (a₀ : W →ₗ[ℂ] W) (Y : Matrix (Fin n) (Fin n) ℂ) :
    PiLp 2 (fun _ : Fin n × Fin n => W) →ₗ[ℂ] PiLp 2 (fun _ : Fin n × Fin n => W) where
  toFun G := WithLp.toLp 2 fun q =>
    (∑ d, Y d q.1 • G (d, q.2)) + (∑ c, star (Y c q.2) • G (q.1, c)) + a₀ (G q)
  map_add' F G := by
    ext q
    simp only [PiLp.add_apply, smul_add, Finset.sum_add_distrib, map_add]
    abel
  map_smul' c G := by
    ext q
    simp [Finset.smul_sum, smul_smul, mul_comm]

theorem vmGen_apply (a₀ : W →ₗ[ℂ] W) (Y : Matrix (Fin n) (Fin n) ℂ)
    (G : PiLp 2 (fun _ : Fin n × Fin n => W)) (q : Fin n × Fin n) :
    vmGen a₀ Y G q = (∑ d, Y d q.1 • G (d, q.2)) + (∑ c, star (Y c q.2) • G (q.1, c)) + a₀ (G q) := rfl

theorem vmAct_hasDerivAt (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (h1 : τ 1 = 1)
    (a₀ : W →ₗ[ℂ] W) (Y : Matrix (Fin n) (Fin n) ℂ)
    (hd : ∀ v, HasDerivAt (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • Y))ᴴ v) (a₀ v) 0)
    (G : PiLp 2 (fun _ : Fin n × Fin n => W)) :
    HasDerivAt (fun t : ℝ => vmAct τ (NormedSpace.exp ((t : ℂ) • Y)) G) (vmGen a₀ Y G) 0 := by
  have hc := fun p q : Fin n × Fin n =>
    (vmstab_hasDerivAt_entry Y p.1 q.1).mul (vmstab_hasDerivAt_entry Y p.2 q.2).star
  have hφ : HasDerivAt (fun t : ℝ => fun q : Fin n × Fin n => ∑ p : Fin n × Fin n,
      (NormedSpace.exp ((t : ℂ) • Y) p.1 q.1 * star (NormedSpace.exp ((t : ℂ) • Y) p.2 q.2)) •
        τ (NormedSpace.exp ((t : ℂ) • Y))ᴴ (G p))
      (fun q => ∑ p : Fin n × Fin n,
        ((NormedSpace.exp (((0 : ℝ) : ℂ) • Y) p.1 q.1 * star (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) p.2 q.2)) • a₀ (G p) +
        (Y p.1 q.1 * star (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) p.2 q.2) +
          NormedSpace.exp (((0 : ℝ) : ℂ) • Y) p.1 q.1 * star (Y p.2 q.2)) •
          τ (NormedSpace.exp (((0 : ℝ) : ℂ) • Y))ᴴ (G p))) 0 :=
    hasDerivAt_pi.2 fun q => HasDerivAt.fun_sum fun p _ => (hc p q).smul (hd (G p))
  have h3 := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n × Fin n => W)).symm :
    (∀ _ : Fin n × Fin n, W) →L[ℝ] PiLp 2 (fun _ : Fin n × Fin n => W)).hasFDerivAt.comp_hasDerivAt 0 hφ
  have hfun : (fun t : ℝ => vmAct τ (NormedSpace.exp ((t : ℂ) • Y)) G) =
      ⇑((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n × Fin n => W)).symm :
        (∀ _ : Fin n × Fin n, W) →L[ℝ] PiLp 2 (fun _ : Fin n × Fin n => W)) ∘
      (fun t : ℝ => fun q : Fin n × Fin n => ∑ p : Fin n × Fin n,
        (NormedSpace.exp ((t : ℂ) • Y) p.1 q.1 * star (NormedSpace.exp ((t : ℂ) • Y) p.2 q.2)) •
          τ (NormedSpace.exp ((t : ℂ) • Y))ᴴ (G p)) := by
    funext t
    ext q
    simp [vmAct_apply]
  rw [hfun]
  refine h3.congr_deriv ?_
  ext q
  simp [vmGen_apply, h1, Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_add_distrib, add_smul, ite_smul,
    Finset.sum_ite_eq', mul_ite, ite_mul]
  abel

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def isometryArrayLinearMap (n : ℕ) (j : W →ₗᵢ[ℂ] V) : PiLp 2 (fun _ : Fin n × Fin n => W) →ₗ[ℂ] Arr V n 1 where
  toFun G := arr1 j fun p => G p
  map_add' F G := by
    ext α
    simp [arr1, arrTo]
  map_smul' c G := by
    ext α
    simp [arr1, arrTo]

theorem familyArrayLinearMap_matrixUnitFamilyActionGenerator (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V) (a₀ : W →ₗ[ℂ] W)
    (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Yᴴ = -Y) (ha : ∀ v, j (a₀ v) = actM E ((-Y).map star) (j v))
    (G : PiLp 2 (fun _ : Fin n × Fin n => W)) :
    isometryArrayLinearMap n j (vmGen a₀ Y G) = ∑ c, ∑ d, (-star (Y c d)) • arrE E 1 c d (isometryArrayLinearMap n j G) := by
  have hYe : ∀ a d, star (Y a d) = -Y d a := fun a d => by
    have := congrFun (congrFun hY d) a
    simpa using this
  have hYe' : ∀ a d, (starRingEnd ℂ) (Y a d) = -Y d a := hYe
  have hite : ∀ (c : Prop) [Decidable c] (f : ((Fin 1 → Fin n × Fin n) → V) →ₗ[ℂ] V) (v),
      (if c then f else 0) v = if c then f v else 0 := by
    intro c _ f v
    split_ifs <;> rfl
  have hs1 : ∀ (a : Fin n) (g : Fin n → Fin n → V), (∑ x, ∑ x₁, if a = x then g x x₁ else 0) = ∑ x₁, g a x₁ := by
    intro a g
    rw [Fintype.sum_eq_single a (fun x hx => by simp [Ne.symm hx])]
    simp
  have hs2 : ∀ (b : Fin n) (g : Fin n → Fin n → V), (∑ x, ∑ x₁, if b = x₁ then g x x₁ else 0) = ∑ x, g x b := by
    intro b g
    exact Finset.sum_congr rfl fun x _ => by simp
  ext α
  obtain ⟨⟨a, b⟩, rfl⟩ : ∃ p, α = fun _ => p := ⟨α 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  simp [isometryArrayLinearMap, arr1, arrE, factorAction, ptE, arrTo, arrOf, actM, vmGen_apply, ha, Finset.sum_add_distrib,
    smul_add, smul_sub, Finset.sum_sub_distrib, hYe', hite, smul_ite, hs1, hs2,
    LinearMap.sum_apply, map_sum, map_smul, neg_smul, Finset.sum_neg_distrib]
  abel

private theorem kStable_isoPart' {X : Type*} [AddCommGroup X] [Module ℂ X] (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ X) (T : Set (Fin n → ℝ)) (S : Submodule ℂ X) :
    Formalism.REAL.KStable ε F (Formalism.REAL.isoPart ε F T S) := by
  intro a b hab x hx
  have key : Formalism.REAL.isoPart ε F T S ≤ (Formalism.REAL.isoPart ε F T S).comap (F a b) := by
    unfold Formalism.REAL.isoPart
    refine iSup₂_le fun y hy => ?_
    intro z hz
    rw [Submodule.mem_comap]
    have hz' : F a b z ∈ Formalism.REAL.kSpan ε F y := by
      unfold Formalism.REAL.kSpan at hz ⊢
      exact Submodule.mem_sInf.2 fun S' hS' => hS'.2 a b hab z (Submodule.mem_sInf.1 hz S' hS')
    exact (le_iSup₂ (f := fun (y : X) (_ : y ∈ S ∧ ∃ μ ∈ T, Formalism.REAL.KHighest ε F μ y) =>
      Formalism.REAL.kSpan ε F y) y hy) hz'
  exact key hx

theorem vmstab_Vminus_stable (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) :
    Formalism.REAL.KStable ε (arrE E 1) (Vminus ε E Λ u) := by
  unfold Vminus
  exact kStable_isoPart' _ _ _ _

private theorem mem_submodule_of_hasDerivAt_linear_of_invariant {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    (S : Submodule ℂ P) (A : P →ₗ[ℂ] P) (hA : ∀ x ∈ S, A x ∈ S) (x : ℝ → P)
    (hx : ∀ t, HasDerivAt x (A (x t)) t) (h0 : x 0 ∈ S) (t : ℝ) : x t ∈ S := by
  haveI : IsClosed (S : Set P) := S.closed_of_finiteDimensional
  have hA' : S ≤ S.comap A := fun y hy => hA y hy
  let B : (P ⧸ S) →L[ℂ] (P ⧸ S) := LinearMap.toContinuousLinearMap (S.mapQ S A hA')
  have hf : ∀ s, HasDerivAt (fun s => S.mkQL (x s)) (B (S.mkQL (x s))) s := by
    intro s
    have := ((S.mkQL).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hx s)
    have e1 : B (S.mkQL (x s)) = (S.mkQL.restrictScalars ℝ) (A (x s)) := by simp [B]
    rw [e1]
    exact this
  have hu := ODE_solution_unique_univ (v := fun _ => (B : P ⧸ S → P ⧸ S)) (s := fun _ => Set.univ)
    (K := ‖B‖₊) (t₀ := 0) (f := fun s => S.mkQL (x s)) (g := fun _ => 0)
    (fun _ => B.lipschitz.lipschitzOnWith) (fun s => ⟨hf s, trivial⟩)
    (fun s => ⟨by simpa using hasDerivAt_const s (0 : P ⧸ S), trivial⟩)
    (by simpa using h0)
  have ht := congrFun hu t
  simpa using ht

end VmStab

theorem vminus_stable_under_K : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), LowData ε E Λ u j → IsTau ε Λ τ w → TauTie ε E j τ → ∀ G : Fin n × Fin n → W, arr1 j G ∈ Vminus ε E Λ u → ∀ k ∈ Kset ε, ∃ G' : Fin n × Fin n → W, arr1 j G' ∈ Vminus ε E Λ u ∧ ∑ p, ⟪τ k w, G p⟫_ℂ • (k⁻¹ * thE ε p * k) = ∑ p, ⟪w, G' p⟫_ℂ • thE ε p := by
  intro V W _ _ _ _ n ε E Λ u j τ w hL hT hTie G hG k hk
  obtain ⟨hfd, ⟨h1, hmul⟩, -, hadj, -⟩ := hT
  obtain ⟨-, -, -, -, hrange⟩ := hL
  obtain ⟨Y, hY, hYk, -⟩ := compact_exists_log_bounded ε k hk
  have hYc : Yᴴ = -Y := vmstab_inK_ct hY
  have hYz : ∀ a b, ε a ≠ ε b → Y a b = 0 := fun a b h => vmstab_entry_zero hY.2 h
  have hspan : ∀ x ∈ Formalism.REAL.kSpan ε E u, ∀ a b, ε a = ε b → E a b x ∈ Formalism.REAL.kSpan ε E u := by
    intro x hx a b hab
    unfold Formalism.REAL.kSpan at hx ⊢
    exact Submodule.mem_sInf.2 fun S' hS' => hS'.2 a b hab x (Submodule.mem_sInf.1 hx S' hS')
  have hex : ∀ v : W, ∃ v' : W, j v' = actM E ((-Y).map star) (j v) := by
    intro v
    have hjv : j v ∈ Formalism.REAL.kSpan ε E u := by
      rw [← hrange]
      exact LinearMap.mem_range_self _ v
    have hmem : actM E ((-Y).map star) (j v) ∈ Formalism.REAL.kSpan ε E u := by
      unfold actM
      rw [LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun a _ => ?_
      rw [LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [LinearMap.smul_apply]
      by_cases hab : ε a = ε b
      · exact Submodule.smul_mem _ _ (hspan _ hjv a b hab)
      · rw [Matrix.map_apply, Matrix.neg_apply, hYz a b hab, neg_zero, star_zero, zero_smul]
        exact Submodule.zero_mem _
    rw [← hrange] at hmem
    obtain ⟨v', hv'⟩ := LinearMap.mem_range.1 hmem
    exact ⟨v', hv'⟩
  choose f hf using hex
  let a₀ : W →ₗ[ℂ] W :=
    { toFun := f
      map_add' := fun v v' => j.injective (by simp only [map_add, hf])
      map_smul' := fun c v => j.injective (by simp only [map_smul, hf, RingHom.id_apply]) }
  have ha : ∀ v, j (a₀ v) = actM E ((-Y).map star) (j v) := hf
  have hJJ := Jm_mul_self ε
  have hJu : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨_, _, hJJ, hJJ⟩, rfl⟩
  have hcomm : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Z * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Z →
      NormedSpace.exp Z * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * NormedSpace.exp Z := by
    intro Z hZ
    have h := Matrix.exp_conj (Formalism.REAL.Jm ε) Z hJu
    rw [Matrix.inv_eq_left_inv hJJ] at h
    have h' : Formalism.REAL.Jm ε * Z * Formalism.REAL.Jm ε = Z := by
      rw [Matrix.mul_assoc, hZ, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
    rw [h'] at h
    calc NormedSpace.exp Z * Formalism.REAL.Jm ε
        = Formalism.REAL.Jm ε * NormedSpace.exp Z * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [← h]
      _ = Formalism.REAL.Jm ε * NormedSpace.exp Z := by
        rw [Matrix.mul_assoc (Formalism.REAL.Jm ε * NormedSpace.exp Z), hJJ, Matrix.mul_one]
  have hsm : ∀ t : ℝ, ((t : ℂ) • Y) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * ((t : ℂ) • Y) :=
    fun t => (vmstab_inK_smul hY t).2
  have hct : ∀ t : ℝ, (NormedSpace.exp ((t : ℂ) • Y))ᴴ = NormedSpace.exp (((-t : ℝ) : ℂ) • Y) := by
    intro t
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hYc, Complex.star_def, Complex.conj_ofReal,
      smul_neg, ← neg_smul, Complex.ofReal_neg]
  have hKC : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • Y) ∈ KC ε := fun t => ⟨Matrix.isUnit_exp _, hcomm _ (hsm t)⟩
  have hKC' : ∀ t : ℝ, (NormedSpace.exp ((t : ℂ) • Y))ᴴ ∈ KC ε := fun t => by
    rw [hct]
    exact hKC (-t)
  let G₀ : PiLp 2 (fun _ : Fin n × Fin n => W) := WithLp.toLp 2 G
  have hadd : ∀ t s : ℝ, vmAct τ (NormedSpace.exp (((t + s : ℝ) : ℂ) • Y)) G₀ =
      vmAct τ (NormedSpace.exp ((s : ℂ) • Y)) (vmAct τ (NormedSpace.exp ((t : ℂ) • Y)) G₀) := by
    intro t s
    rw [Complex.ofReal_add, add_smul,
      Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)]
    exact vmAct_mul τ _ _ (hmul _ (hKC' s) _ (hKC' t)) G₀
  have hd : ∀ v, HasDerivAt (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • Y))ᴴ v) (a₀ v) 0 := by
    intro v
    have hY' : Formalism.REAL.inK ε (-Y) := by simpa using vmstab_inK_smul hY (-1)
    have := hTie (-Y) hY' v (a₀ v) (ha v)
    convert this using 1
    funext t
    rw [hct, Complex.ofReal_neg, neg_smul, smul_neg]
  let A := vmGen a₀ Y
  have hxd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => vmAct τ (NormedSpace.exp ((s : ℂ) • Y)) G₀)
      (A (vmAct τ (NormedSpace.exp ((t : ℂ) • Y)) G₀)) t := by
    intro t
    have h0 := vmAct_hasDerivAt τ h1 a₀ Y hd (vmAct τ (NormedSpace.exp ((t : ℂ) • Y)) G₀)
    have h0' : HasDerivAt (fun s : ℝ => vmAct τ (NormedSpace.exp (((t + s : ℝ) : ℂ) • Y)) G₀)
        (A (vmAct τ (NormedSpace.exp ((t : ℂ) • Y)) G₀)) ((fun s : ℝ => s - t) t) := by
      simp only [hadd, sub_self]
      exact h0
    have hh : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
    have h3 := HasDerivAt.scomp (h := fun s : ℝ => s - t) t h0' hh
    have hfun : (fun s : ℝ => vmAct τ (NormedSpace.exp ((s : ℂ) • Y)) G₀) =
        (fun s : ℝ => vmAct τ (NormedSpace.exp (((t + s : ℝ) : ℂ) • Y)) G₀) ∘ (fun s : ℝ => s - t) := by
      funext s
      simp
    rw [hfun]
    refine h3.congr_deriv ?_
    simp
  haveI := hfd
  let S : Submodule ℂ (PiLp 2 (fun _ : Fin n × Fin n => W)) := (Vminus ε E Λ u).comap (isometryArrayLinearMap n j)
  have hA : ∀ x ∈ S, A x ∈ S := by
    intro x hx
    show isometryArrayLinearMap n j (vmGen a₀ Y x) ∈ Vminus ε E Λ u
    rw [familyArrayLinearMap_matrixUnitFamilyActionGenerator E j a₀ Y hYc ha x]
    refine Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun d _ => ?_
    by_cases hcd : ε c = ε d
    · exact Submodule.smul_mem _ _ (vmstab_Vminus_stable ε E Λ u c d hcd _ hx)
    · simp [hYz c d hcd]
  have hG0 : G₀ ∈ S := hG
  have hx0 : (fun s : ℝ => vmAct τ (NormedSpace.exp ((s : ℂ) • Y)) G₀) 0 ∈ S := by
    simpa [vmAct_one τ h1] using hG0
  have hx1 := mem_submodule_of_hasDerivAt_linear_of_invariant S A hA _ hxd hx0 1
  simp only [Complex.ofReal_one, one_smul, hYk] at hx1
  refine ⟨fun q => vmAct τ k G₀ q, hx1, ?_⟩
  simp only [vmstab_conj_thE hk, vmAct_apply, inner_sum, inner_smul_right, Finset.smul_sum, smul_smul,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  rw [hadj k (vmstab_mem_KC hk).1 w (G p)]
  congr 1
  simp only [G₀, PiLp.toLp_apply]
  ring

end GlobalTheory.SphJet
