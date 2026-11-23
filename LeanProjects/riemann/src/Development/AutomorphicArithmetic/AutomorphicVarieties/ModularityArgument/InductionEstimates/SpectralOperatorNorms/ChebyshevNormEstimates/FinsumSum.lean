import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.Exponents3
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FamExp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.GoodConst
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.TruncSB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.Regroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.SideEstX
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.SideEst
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TotalDegreeAevalLe
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Degree

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem chi_ex (η : ℝ) (hη : 0 < η) : ∃ χ : ℝ → ℝ, Continuous χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x ≥ η, χ x = 1) ∧
    (∀ x ≤ η / 2, χ x = 0) ∧ ∀ x, |χ x| ≤ 1 := by
  have h01 : ∀ x : ℝ, 0 ≤ max 0 (min 1 (2 * x / η - 1)) ∧ max 0 (min 1 (2 * x / η - 1)) ≤ 1 :=
    fun x => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  refine ⟨fun x => max 0 (min 1 (2 * x / η - 1)), by fun_prop, h01, ?_, ?_, ?_⟩
  · intro x hx
    have : 2 ≤ 2 * x / η := by rw [le_div_iff₀ hη]; linarith
    show max 0 (min 1 (2 * x / η - 1)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  · intro x hx
    have : 2 * x / η ≤ 1 := by rw [div_le_iff₀ hη]; linarith
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  · intro x
    rw [abs_of_nonneg (h01 x).1]; exact (h01 x).2

private theorem trOn_bot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) :
    trOn (⊥ : Submodule ℂ H) T = 0 := by
  have : prj (⊥ : Submodule ℂ H) = 0 := by
    ext v
    have h := Submodule.starProjection_apply_mem (⊥ : Submodule ℂ H).topologicalClosure v
    have h0 : (⊥ : Submodule ℂ H).topologicalClosure = ⊥ := IsClosed.submodule_topologicalClosure_eq (by simp)
    exact (Submodule.mem_bot ℂ).mp (h0.le h)
  simp [trOn, this, trace]

private theorem eig_bot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (V : Submodule ℂ H)
    (A : H →L[ℂ] H) (hA : ‖A‖ ≤ 1) (x : ℝ) (hx : 1 < x) : eigIn V A x = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have h1 : A v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.mp hv.2
  have h2 : ‖A v‖ ≤ 1 * ‖v‖ := (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  rw [h1, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h2
  have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  simpa using this

private theorem deg_ev (d : ℕ → ℕ) (hd : Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0)) (p : ℕ) (hp : 0 < p) (A : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ m' : ℕ, j / (2 * p) + (d j + A) ≤ (j + m') / p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  filter_upwards [hd.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * p) by positivity)), eventually_ge_atTop (4 * p * A),
    eventually_gt_atTop 0] with j h1 h2 h3 m'
  have hj : (0 : ℝ) < j := by exact_mod_cast h3
  rw [div_lt_div_iff₀ hj (by positivity)] at h1
  have h4 : d j * (4 * p) < j := by
    have : ((d j * (4 * p) : ℕ) : ℝ) < (j : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have h5 := Nat.div_mul_le_self j (2 * p)
  rw [Nat.le_div_iff_mul_le hp]
  nlinarith

private theorem comb_bd (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) (c₁ c₂ j X Y u v : ℝ) (hj : 0 ≤ j) (hX : 0 ≤ X)
    (hY : 0 ≤ Y) (hu : u ≤ a ^ (n + 1) * (Real.exp (c₁ * j) * X + Y)) (hv : v ≤ b ^ (n + 1) * (Real.exp (c₂ * j) * X + Y)) :
    u + c * v ≤ (a + (c + 1) * b) ^ (n + 1) * (Real.exp (max c₁ c₂ * j) * X + Y) := by
  have e1 : Real.exp (c₁ * j) * X + Y ≤ Real.exp (max c₁ c₂ * j) * X + Y := by
    gcongr; exact le_max_left _ _
  have e2 : Real.exp (c₂ * j) * X + Y ≤ Real.exp (max c₁ c₂ * j) * X + Y := by
    gcongr; exact le_max_right _ _
  set Z := Real.exp (max c₁ c₂ * j) * X + Y
  have hZ : 0 ≤ Z := by positivity
  have hu' : u ≤ a ^ (n + 1) * Z := hu.trans (by gcongr)
  have hv' : v ≤ b ^ (n + 1) * Z := hv.trans (by gcongr)
  have h3 : c ≤ (c + 1) ^ (n + 1) := (by linarith : c ≤ c + 1).trans (le_self_pow₀ (by linarith) (Nat.succ_ne_zero n))
  have h4 : a ^ (n + 1) + ((c + 1) * b) ^ (n + 1) ≤ (a + (c + 1) * b) ^ (n + 1) :=
    pow_add_pow_le ha (by positivity) (Nat.succ_ne_zero n)
  have h5 : c * b ^ (n + 1) ≤ ((c + 1) * b) ^ (n + 1) := by rw [mul_pow]; gcongr
  calc u + c * v ≤ a ^ (n + 1) * Z + c * (b ^ (n + 1) * Z) := by gcongr
    _ = (a ^ (n + 1) + c * b ^ (n + 1)) * Z := by ring
    _ ≤ _ := by gcongr; linarith

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem val_congr (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ) (t t' : Pl K → Multiset ℂ) (S : Set (Pl K)) (h : ∀ w ∉ S, t w = t' w)
    (P : PR K n) (hP : ∀ y ∈ P.vars, y.1 ∉ S) : val x Λ t P = val x Λ t' P := by
  unfold val
  refine hom_congr_vars (by ext <;> simp) ?_ rfl
  intro i hi _
  simp [hval, h _ (hP i hi)]

private theorem val_gam (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ) (t : Pl K → Multiset ℂ) (γ : MvPolynomial (Pl K × Fin n) ℂ) :
    val x Λ t (map C γ : PR K n) = eval (hval t) γ := by
  unfold val
  induction γ using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp]; simp

private theorem evK_congr (hT : TruncSpec) (S : Set (Pl K)) (Φ : KF (Ix K n) (Pl K × Fin n)) (hΦ : admitted S Φ) (L L' : Ix K n → ℂ)
    (t t' : Pl K → Multiset ℂ) (hL : msOf L = msOf L') (h : ∀ w ∉ S, t w = t' w) : evK L (hval t) Φ = evK L' (hval t') Φ := by
  obtain ⟨⟨G, hG⟩, h2⟩ := hT K n S Φ hΦ
  obtain ⟨⟨κ, D, hκ, hB⟩, h3, -⟩ := h2 G hG
  obtain ⟨u, hu, hu'⟩ := h3 L t
  obtain ⟨v, hv, hv'⟩ := h3 L' t'
  have : u = v := by
    funext d
    have a1 := hu' 1 d
    have a2 := hv' 1 d
    rw [hL, val_congr 1 _ t t' S h _ (fun y hy => hκ _ ((hB d).1 y hy)), a2] at a1
    simpa using a1.symm
  subst this
  exact tendsto_nhds_unique hu hv

private theorem pt_card (b : Datum K n) (S : Set (Pl K)) (Λ : (K →+* ℂ) → Multiset ℂ) (t : Pl K → Multiset ℂ) (h : b.Pt S Λ t) :
    ∀ w ∉ S, (t w).card = n := by
  obtain ⟨lam, m, B, h1, -, h3⟩ := h
  intro w hw
  rw [h3 w hw, Multiset.card_sum]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) b.sum
  rw [Multiset.card_map]
  exact ((h1 i).2 w hw).1

private theorem tr_eq {l : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure] {θ : Twist μ} (𝔰 : Side θ l)
    (p : Submodule ℂ (LL μ) → Prop) (x : ℝ) (j : ℕ) :
    𝔰.tr p x j = ∑ᶠ y ∈ {y : ℝ × Submodule ℂ (LL μ) | (IsSummand μ y.2 ∧ y.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = y.2 ∧
      eigIn y.2 𝔰.toAmp.A y.1 ≠ ⊥) ∧ p y.2 ∧ y.1 = x}, trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U) := by
  unfold Side.tr
  symm
  rw [finsum_mem_eq_of_bijOn (t := {V : Submodule ℂ (LL μ) | (IsSummand μ V ∧ V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V ∧ p V) ∧ eigIn V 𝔰.toAmp.A x ≠ ⊥})
    (g := fun V => trOn (eigIn V 𝔰.toAmp.A x) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U)) Prod.snd]
  · apply finsum_mem_inter_support_eq'
    intro V hV
    refine ⟨fun h => h.1, fun h => ⟨h, fun h0 => hV ?_⟩⟩
    simp only [h0, trOn_bot]
  · refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, V⟩ ⟨⟨h1, h2, h3⟩, h4, rfl⟩
      exact ⟨⟨h1, h2, h4⟩, h3⟩
    · rintro ⟨a, V⟩ ⟨-, -, h⟩ ⟨a', V'⟩ ⟨-, -, h'⟩ h''
      exact Prod.ext (h.trans h'.symm) h''
    · rintro V ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨(x, V), ⟨⟨h1, h2, h4⟩, h3, rfl⟩, rfl⟩
  · rintro ⟨a, V⟩ ⟨-, -, rfl⟩
    rfl

end

private theorem finsum_sum {α β : Type} (S : Set (α ⊕ β)) (hS : S.Finite) (f : α ⊕ β → ℂ) :
    ∑ᶠ i ∈ S, f i = ∑ᶠ i ∈ Sum.inl ⁻¹' S, f (Sum.inl i) + ∑ᶠ i ∈ Sum.inr ⁻¹' S, f (Sum.inr i) := by
  conv_lhs => rw [← Set.image_preimage_inl_union_image_preimage_inr S]
  rw [finsum_mem_union Set.disjoint_image_inl_image_inr ((hS.preimage Sum.inl_injective.injOn).image _)
    ((hS.preimage Sum.inr_injective.injOn).image _), finsum_mem_image Sum.inl_injective.injOn,
    finsum_mem_image Sum.inr_injective.injOn]

private def ExpF (τ : ℕ → ℂ) : Prop := ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop, τ j = ∑ ζ ∈ s, c ζ * ζ ^ j

private def Lim (u : ℕ → ℂ) (g e : Prop) (k : ℂ) : Prop := ∃ z, Tendsto u atTop (𝓝 z) ∧ (g → e → z = k) ∧ (¬ g → z = 0)

private theorem ExpF.mul {τ : ℕ → ℂ} (h : ExpF τ) (c : ℂ) : ExpF fun j => c * τ j := by
  obtain ⟨s, c', h0, h1⟩ := h
  refine ⟨s, fun ζ => c * c' ζ, h0, ?_⟩
  filter_upwards [h1] with j hj
  rw [hj, Finset.mul_sum]
  simp only [mul_assoc]

private theorem abs3 (T₁ T₂ T₃ : Type) (a₁ : T₁ → ℝ) (a₂ : T₂ → ℝ) (a₃ : T₃ → ℝ) (τ₁ : T₁ → ℕ → ℂ) (τ₂ : T₂ → ℕ → ℂ) (τ₃ : T₃ → ℕ → ℂ)
    (act₁ good₁ : T₁ → Prop) (act₂ good₂ : T₂ → Prop) (act₃ good₃ : T₃ → Prop) (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (p : ℕ) (hp : 0 < p)
    (d : ℕ → ℕ) (hd : Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0))
    (hd' : ∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial)
    (e₁ : ∀ i, act₁ i → 0 < a₁ i → ExpF (τ₁ i)) (e₂ : ∀ i, act₂ i → 0 < a₂ i → ExpF (τ₂ i)) (e₃ : ∀ i, act₃ i → 0 < a₃ i → ExpF (τ₃ i))
    (f₁ : {i | act₁ i ∧ a₁ i = x}.Finite) (f₂ : {i | act₂ i ∧ a₂ i = x}.Finite) (f₃ : {i | act₃ i ∧ a₃ i = x}.Finite)
    (h : ∀ N : ℝ, ∃ c₁ : ℝ, ∀ η : ℝ, 0 < η → η < x → ∃ (s₁ : Finset T₁) (s₂ : Finset T₂) (s₃ : Finset T₃)
      (u₁ : T₁ → ℕ → ℂ) (u₂ : T₂ → ℕ → ℂ) (u₃ : T₃ → ℕ → ℂ) (k : ℂ), k ≠ 0 ∧
      (∀ i, i ∈ s₁ ↔ η < a₁ i ∧ act₁ i) ∧ (∀ i, i ∈ s₂ ↔ η < a₂ i ∧ act₂ i) ∧ (∀ i, i ∈ s₃ ↔ η < a₃ i ∧ act₃ i) ∧
      (∀ i ∈ s₁, Lim (u₁ i) (good₁ i) (a₁ i = x) k) ∧ (∀ i ∈ s₂, Lim (u₂ i) (good₂ i) (a₂ i = x) k) ∧
      (∀ i ∈ s₃, Lim (u₃ i) (good₃ i) (a₃ i = x) k) ∧
      ∀ s₀ : ℕ, ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ m ≤ s₀, ∀ m' ≤ s₀,
        ‖∑ i ∈ s₁, u₁ i (d j) * (a₁ i : ℂ) ^ d j * (cheb η (j / p + m) (a₁ i) : ℂ) * τ₁ i (j + m') +
          (∑ i ∈ s₂, u₂ i (d j) * (a₂ i : ℂ) ^ d j * (cheb η (j / p + m) (a₂ i) : ℂ) * τ₂ i (j + m') +
          ∑ i ∈ s₃, u₃ i (d j) * (a₃ i : ℂ) ^ d j * (cheb η (j / p + m) (a₃ i) : ℂ) * τ₃ i (j + m'))‖ ≤
            K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) :
    ∀ᶠ j : ℕ in atTop, ∑ᶠ i ∈ {i | act₁ i ∧ good₁ i ∧ a₁ i = x}, τ₁ i j + (∑ᶠ i ∈ {i | act₂ i ∧ good₂ i ∧ a₂ i = x}, τ₂ i j +
      ∑ᶠ i ∈ {i | act₃ i ∧ good₃ i ∧ a₃ i = x}, τ₃ i j) = 0 := by
  have hfin : {i : T₁ ⊕ T₂ ⊕ T₃ | Sum.elim act₁ (Sum.elim act₂ act₃) i ∧ Sum.elim a₁ (Sum.elim a₂ a₃) i = x}.Finite := by
    refine Set.finite_preimage_inl_and_inr.mp ⟨f₁, Set.finite_preimage_inl_and_inr.mp ⟨f₂, f₃⟩⟩
  have key := absX (T₁ ⊕ T₂ ⊕ T₃) (Sum.elim a₁ (Sum.elim a₂ a₃)) (Sum.elim τ₁ (Sum.elim τ₂ τ₃)) (Sum.elim act₁ (Sum.elim act₂ act₃))
    (Sum.elim good₁ (Sum.elim good₂ good₃)) x hx hx1 p hp d hd hd' ?_ hfin ?_
  · refine key.mono fun j hj => ?_
    have hf2 : {i : T₁ ⊕ T₂ ⊕ T₃ | Sum.elim act₁ (Sum.elim act₂ act₃) i ∧ Sum.elim good₁ (Sum.elim good₂ good₃) i ∧
        Sum.elim a₁ (Sum.elim a₂ a₃) i = x}.Finite := hfin.subset fun i hi => ⟨hi.1, hi.2.2⟩
    rw [finsum_sum _ hf2, finsum_sum _ (hf2.preimage Sum.inr_injective.injOn)] at hj
    exact hj
  · rintro (i | i | i)
    exacts [e₁ i, e₂ i, e₃ i]
  · intro N
    obtain ⟨c₁, h⟩ := h N
    refine ⟨c₁, fun η hη hη' => ?_⟩
    obtain ⟨s₁, s₂, s₃, u₁, u₂, u₃, k, hk, m₁, m₂, m₃, l₁, l₂, l₃, hb⟩ := h η hη hη'
    have hl : ∀ i ∈ s₁.disjSum (s₂.disjSum s₃), Lim (Sum.elim u₁ (Sum.elim u₂ u₃) i) (Sum.elim good₁ (Sum.elim good₂ good₃) i)
        (Sum.elim a₁ (Sum.elim a₂ a₃) i = x) k := by
      rintro (i | i | i) hi
      · exact l₁ i (by simpa using hi)
      · exact l₂ i (by simpa using hi)
      · exact l₃ i (by simpa using hi)
    choose! z hz1 hz2 hz3 using hl
    refine ⟨s₁.disjSum (s₂.disjSum s₃), Sum.elim u₁ (Sum.elim u₂ u₃), z, k, hk, ?_, hz1, hz2, hz3, fun s₀ => ?_⟩
    · rintro (i | i | i)
      · simpa using m₁ i
      · simpa using m₂ i
      · simpa using m₃ i
    · obtain ⟨K, hK⟩ := hb s₀
      refine ⟨K, ?_⟩
      filter_upwards [hK] with j hj m hm m' hm'
      rw [Finset.sum_disjSum, Finset.sum_disjSum]
      exact hj m hm m' hm'

private theorem side_fin (hTr : TrExp) (hEV : EvVal) (hTS : TruncSpec) (hOS : OneSide) (hEv : EvEx) {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] {μ : Measure (normOneGL K (2 + 2))} [μ.IsHaarMeasure] {θ : Twist μ} (𝔰 : Side θ 2) :
    (∀ y : ℝ × Submodule ℂ (LL μ), (IsSummand μ y.2 ∧ y.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = y.2 ∧ eigIn y.2 𝔰.toAmp.A y.1 ≠ ⊥) → 0 < y.1 →
      ExpF fun j => trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U)) ∧
    ∀ x : ℝ, 0 < x → {y : ℝ × Submodule ℂ (LL μ) |
      (IsSummand μ y.2 ∧ y.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = y.2 ∧ eigIn y.2 𝔰.toAmp.A y.1 ≠ ⊥) ∧ y.1 = x}.Finite := by
  obtain ⟨hA0, -, -, ev, hev, hin⟩ := hEv K (2 + 2) (by norm_num) μ 𝔰.toAmp
  obtain ⟨c₁, h⟩ := sideEst hOS hEV hTS K (2 + 2) 2 (by norm_num) μ θ 𝔰 ev hev hin 0
  have key : ∀ x : ℝ, 0 < x → ∃ (η : ℝ) (s : Finset (ℝ × Submodule ℂ (LL μ))), η < x ∧
      (∀ y, y ∈ s ↔ η < y.1 ∧ IsSummand μ y.2 ∧ y.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = y.2 ∧ eigIn y.2 𝔰.toAmp.A y.1 ≠ ⊥) ∧
        (∀ y ∈ s, FiniteDimensional ℂ (eigIn y.2 𝔰.toAmp.A y.1)) := by
    intro x hx
    have hη : 0 < min (x / 2) 1 := lt_min (by linarith) one_pos
    obtain ⟨χ, h1, h2, h3, -⟩ := chi_ex _ hη
    obtain ⟨s, hs, hs', -⟩ := h _ hη (min_le_right _ _) χ h1 h2 h3
    exact ⟨_, s, (min_le_left _ _).trans_lt (by linarith), hs, hs'⟩
  refine ⟨fun y hy hy0 => ?_, fun x hx => ?_⟩
  · obtain ⟨η, s, h1, h2, h3⟩ := key _ hy0
    exact hTr K (2 + 2) 2 (by norm_num) μ θ 𝔰 y.2 y.1 hA0 hy.1 (h3 y ((h2 y).mpr ⟨h1, hy⟩))
  · obtain ⟨η, s, h1, h2, h3⟩ := key _ hx
    exact s.finite_toSet.subset fun y hy => (h2 y).mpr ⟨hy.2 ▸ h1, hy.1⟩

private theorem fam_card (hPar : ParEx) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]
    {μ : Measure (normOneGL E (2 + 2))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam 𝔢) :
    (∀ τ, (𝔵.Λ τ).card = 2 + 2) ∧ ∀ w ∉ 𝔢.S, (𝔵.t w).card = 2 + 2 ∧ 0 ∉ 𝔵.t w := by
  have h1 : IsSummand (BW.mu1 E 2) 𝔵.τ₁ :=
    ⟨𝔵.pair.irr₁.le, 𝔵.pair.irr₁.closed, 𝔵.pair.irr₁.inv, 𝔵.pair.irr₁.ne, fun V a b c => 𝔵.pair.irr₁.irr V a b c⟩
  have h2 : IsSummand (BW.mu1 E 2) 𝔵.τ₂ :=
    ⟨𝔵.pair.irr₂.le, 𝔵.pair.irr₂.closed, 𝔵.pair.irr₂.inv, 𝔵.pair.irr₂.ne, fun V a b c => 𝔵.pair.irr₂.irr V a b c⟩
  refine ⟨fun τ => ?_, fun w hw => ⟨?_, ?_⟩⟩
  · rw [UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam.Λ, Multiset.card_add, (𝔵.at₁.1 τ).1, (𝔵.at₂.1 τ).1]
  · rw [UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam.t, Multiset.card_add, (𝔵.at₁.2 w hw).1, (𝔵.at₂.2 w hw).1]
  · rw [UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam.t, Multiset.mem_add, not_or]
    exact ⟨(hPar E 2 (by norm_num) _ _ h1).2.2 w _ (𝔵.at₁.2 w hw), (hPar E 2 (by norm_num) _ _ h2).2.2 w _ (𝔵.at₂.2 w hw)⟩

private theorem sep (hEV : EvVal) (hVB : ValBc) (hSep : SepPoly) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E] {n : ℕ} (hn : 0 < n)
    {μE : Measure (normOneGL E n)} [μE.IsHaarMeasure] {μF : Measure (normOneGL F n)} [μF.IsHaarMeasure] (𝔞 : Amp μE) (𝔟 : Amp μF)
    (hS : ∀ w : Pl E, w ∈ 𝔞.S ↔ w.under (𝓞 F) ∈ 𝔟.S) (Λ : (E →+* ℂ) → Multiset ℂ) (t : Pl E → Multiset ℂ)
    (hΛ : ∀ τ, (Λ τ).card = n) (ht : ∀ w ∉ 𝔞.S, (t w).card = n)
    (sE : Finset (ℝ × Submodule ℂ (LL μE))) (sF : Finset (ℝ × Submodule ℂ (LL μF)))
    (hE : ∀ y ∈ sE, 0 < y.1 ∧ IsSummand μE y.2 ∧ eigIn y.2 𝔞.A y.1 ≠ ⊥) (hF : ∀ y ∈ sF, 0 < y.1 ∧ IsSummand μF y.2 ∧ eigIn y.2 𝔟.A y.1 ≠ ⊥) :
    ∃ (P : PR E n) (κ : Finset (Pl E)) (D : ℕ), (∀ w ∈ κ, w ∉ 𝔞.S) ∧ Bd κ D D P ∧ (∀ x : ℝ, x ≠ 0 → val x Λ t P ≠ 0) ∧
      (∀ y ∈ sE, ¬ At μE 𝔞.S y.2 Λ t → ∃ (L : Ix E n → ℂ) (t' : Pl E → Multiset ℂ), At μE 𝔞.S y.2 (msOf L) t' ∧ val y.1 (msOf L) t' P = 0) ∧
      (∀ y ∈ sF, ¬ (∃ Λ' t', At μF 𝔟.S y.2 Λ' t' ∧ Λ = bcInf Λ' ∧ ∀ w ∉ 𝔞.S, t w = bcSat t' w) →
        ∃ (L : Ix F n → ℂ) (t' : Pl F → Multiset ℂ), At μF 𝔟.S y.2 (msOf L) t' ∧ val y.1 (msOf L) t' (bcPR F P) = 0) := by
  classical
  have pE : ∀ y ∈ sE, ∃ (L : Ix E n → ℂ) (t' : Pl E → Multiset ℂ), At μE 𝔞.S y.2 (msOf L) t' := by
    intro y hy
    obtain ⟨Λ', t', h⟩ := (hEV E n hn μE 𝔞 y.2 y.1 (hE y hy).1 (hE y hy).2.1).1 (hE y hy).2.2
    obtain ⟨L, rfl⟩ := (bdLem E n ∅ ∅ 0 0 0 0 0 0).2.2.2 Λ' fun τ => (h.1 τ).1
    exact ⟨L, t', h⟩
  have pF : ∀ y ∈ sF, ∃ (L : Ix F n → ℂ) (t' : Pl F → Multiset ℂ), At μF 𝔟.S y.2 (msOf L) t' := by
    intro y hy
    obtain ⟨Λ', t', h⟩ := (hEV F n hn μF 𝔟 y.2 y.1 (hF y hy).1 (hF y hy).2.1).1 (hF y hy).2.2
    obtain ⟨L, rfl⟩ := (bdLem F n ∅ ∅ 0 0 0 0 0 0).2.2.2 Λ' fun τ => (h.1 τ).1
    exact ⟨L, t', h⟩
  choose! LE tE hLE using pE
  choose! LF tF hLF using pF
  let I₁ := {y // y ∈ sE.filter fun y => ¬ At μE 𝔞.S y.2 Λ t}
  let I₂ := {y // y ∈ sF.filter fun y => ¬ (∃ Λ' t', At μF 𝔟.S y.2 Λ' t' ∧ Λ = bcInf Λ' ∧ ∀ w ∉ 𝔞.S, t w = bcSat t' w)}
  letI : Fintype I₁ := Finset.Subtype.fintype _
  letI : Fintype I₂ := Finset.Subtype.fintype _
  obtain ⟨P, κ, D, h1, h2, h3, h4⟩ := hSep E n 𝔞.S Λ t (I₁ ⊕ I₂)
    (Sum.elim (fun y => msOf (LE y.1)) fun y => bcInf (msOf (LF y.1))) (Sum.elim (fun y => tE y.1) fun y => bcSat (tF y.1)) hΛ ht
    (by
      rintro (y | y) τ
      · exact ((hLE y.1 (Finset.mem_filter.mp y.2).1).1 τ).1
      · exact ((hLF y.1 (Finset.mem_filter.mp y.2).1).1 _).1)
    (by
      rintro (y | y) w hw
      · exact ((hLE y.1 (Finset.mem_filter.mp y.2).1).2 w hw).1
      · exact (Multiset.card_map _ _).trans ((hLF y.1 (Finset.mem_filter.mp y.2).1).2 _ fun h => hw ((hS w).mpr h)).1)
    (by
      rintro (y | y) ⟨ha, hb⟩
      · have h := hLE y.1 (Finset.mem_filter.mp y.2).1
        refine (Finset.mem_filter.mp y.2).2 ⟨fun τ => ?_, fun w hw => ?_⟩
        · rw [congrFun ha τ]; exact h.1 τ
        · rw [hb w hw]; exact h.2 w hw
      · exact (Finset.mem_filter.mp y.2).2 ⟨_, _, hLF y.1 (Finset.mem_filter.mp y.2).1, ha, hb⟩)
  refine ⟨P, κ, D, h1, h2, h3, fun y hy hy' => ⟨LE y, tE y, hLE y hy, ?_⟩, fun y hy hy' => ⟨LF y, tF y, hLF y hy, ?_⟩⟩
  · exact h4 (Sum.inl ⟨y, Finset.mem_filter.mpr ⟨hy, hy'⟩⟩) y.1
  · rw [(hVB F E n y.1 _ (tF y) P fun z hz => ((hLF y hy).2 _ fun h => h1 _ (h2.1 z hz) ((hS _).mpr h)).1).1]
    exact h4 (Sum.inr ⟨y, Finset.mem_filter.mpr ⟨hy, hy'⟩⟩) y.1

set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.cixOf :
    ParEx → TrExp → EvVal → ValBc → KillEx2 → KfBc → TruncSpec → SepPoly → OneSide → OneSideX → EvEx → Kill → KillExempt → FamEx → CIx := by
  intro hPar hTr hEV hVB hK2 hKf hTS hSep hOS hOSX hEv hKill hKX hFam F E _ _ _ _ _ _ _ μE _ μF _ θ 𝔢 𝔣 c hG 𝔵 hoff
  classical
  obtain ⟨hAE0, hAE1, -, evE, hevE, hinE⟩ := hEv E (2 + 2) (by norm_num) μE 𝔢.toAmp
  obtain ⟨hAF0, hAF1, -, evF, hevF, hinF⟩ := hEv F (2 + 2) (by norm_num) μF 𝔣.toAmp
  obtain ⟨Nn, Cf, hN⟩ := hFam E μE _ 𝔵.τ₁ 𝔵.τ₂ 𝔵.pair 𝔵.D 𝔵.d 𝔵.d' 𝔵.A 𝔵.A' 𝔵.P 𝔵.isP
  obtain ⟨evz, hevz⟩ := evzEx 𝔵 evE hevE
  obtain ⟨⟨sp, hsp, hsp1, hsp0⟩, hexp⟩ := famExp 𝔵 Nn Cf hN hAE0 hAE1
  refine ⟨Nn, hN.2, fun x hx => ?_⟩
  by_cases hx1 : 1 < x
  · refine Eventually.of_forall fun j => ?_
    rw [hsp0 x hx (fun h => absurd (hsp1 x h) (not_le.mpr hx1)) j]
    simp only [Side.tr, eig_bot _ _ hAE1 x hx1, eig_bot _ _ hAF1 x hx1, trOn_bot, finsum_zero, mul_zero, add_zero]
  obtain ⟨d, hd, hd'⟩ := UpperTheory.ConvolutionTheory.FX.degree
  obtain ⟨hS, p, C₀, hp, hGeo⟩ := hG
  obtain ⟨eE, fE⟩ := side_fin hTr hEV hTS hOS hEv 𝔢
  obtain ⟨eF, fF⟩ := side_fin hTr hEV hTS hOS hEv 𝔣
  obtain ⟨hΛ, ht⟩ := fam_card hPar 𝔵
  have key := abs3 _ _ _ Prod.fst id Prod.fst
    (fun y j => trOn (eigIn y.2 𝔢.toAmp.A y.1) ((𝔢.Uq 0 ^ j) ∘L Rop μE 𝔢.g ∘L θ.U))
    (fun a j => (1 / 2 : ℂ) * 𝔵.tr Nn a j)
    (fun y j => -c * trOn (eigIn y.2 𝔣.toAmp.A y.1) ((𝔣.Uq 0 ^ j) ∘L Rop μF 𝔣.g ∘L (Twist.id μF).U))
    _ (fun y => At μE 𝔢.S y.2 𝔵.Λ 𝔵.t) (fun a => a ∈ sp) (fun _ => True)
    _ (fun y => ∃ Λ' t', At μF 𝔣.S y.2 Λ' t' ∧ 𝔵.Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢.S, 𝔵.t w = bcSat t' w)
    x hx (not_lt.mp hx1) (2 * p) (by omega) d hd hd' eE (fun a _ _ => ExpF.mul (hexp a) _)
    (fun y h1 h2 => (eF y h1 h2).mul _) (fE x hx) (sp.finite_toSet.subset fun a ha => ha.1) (fF x hx) ?_
  · refine key.mono fun j hj => ?_
    rw [tr_eq, tr_eq]
    have h2 : ∑ᶠ i ∈ {i : ℝ | i ∈ sp ∧ True ∧ id i = x}, (1 / 2 : ℂ) * 𝔵.tr Nn i j = (1 / 2 : ℂ) * 𝔵.tr Nn x j := by
      by_cases hxs : x ∈ sp
      · have : {i : ℝ | i ∈ sp ∧ True ∧ id i = x} = {x} := by
          ext i
          exact ⟨fun h => h.2.2, fun h => ⟨h ▸ hxs, trivial, h⟩⟩
        rw [this, finsum_mem_singleton]
      · have : {i : ℝ | i ∈ sp ∧ True ∧ id i = x} = ∅ := by
          ext i
          exact ⟨fun h => hxs (h.2.2 ▸ h.1), fun h => h.elim⟩
        rw [this, finsum_mem_empty, hsp0 x hx hxs, mul_zero]
    rw [h2, ← mul_finsum_mem] at hj
    linear_combination hj
  intro N
  obtain ⟨cE, hE⟩ := sideEstX hOSX hEV hTS E μE θ 𝔢 𝔵 evE evz Nn Cf hevE hinE hevz hN.1 sp hsp C₀ N
  obtain ⟨cF, hF⟩ := sideEst hOS hEV hTS F (2 + 2) 2 (by norm_num) μF _ 𝔣 evF hevF hinF C₀
  refine ⟨max cE cF, fun η hη hηx => ?_⟩
  have hη1 : η ≤ 1 := hηx.le.trans (not_lt.mp hx1)
  obtain ⟨χ, hχ1, hχ2, hχ3, hχ4, hχ5⟩ := chi_ex η hη
  obtain ⟨sE, hsE, -, hE⟩ := hE η hη hη1 χ hχ1 hχ2 hχ3
  obtain ⟨sF, hsF, -, hF⟩ := hF η hη hη1 χ hχ1 hχ2 hχ3
  obtain ⟨B, _, b, hb1, hb2, hb3⟩ := hKX E μE θ 𝔢 𝔵 η hη
  obtain ⟨B', _, b', hb1', hb3'⟩ := hKill F (2 + 2) (by norm_num) μF 𝔣.toAmp η hη
  obtain ⟨L, hL⟩ := (bdLem E (2 + 2) ∅ ∅ 0 0 0 0 0 0).2.2.2 𝔵.Λ hΛ
  obtain ⟨Φ, hΦ, hΦ0, hΦ1, hΦ2⟩ := hK2 F E (2 + 2) 𝔢.S 𝔣.S hS B B' b b' hb1 hb1' L 𝔵.t (fun w hw => (ht w hw).1)
    (by rw [hL]; exact hb2) (by rw [hL]; exact fun i => hoff (b' i))
  obtain ⟨⟨G, hΦG⟩, hT⟩ := hTS E (2 + 2) 𝔢.S Φ hΦ
  obtain ⟨⟨κ₁, D₁, hκ₁, hB₁⟩, -⟩ := hT G hΦG
  obtain ⟨Φ', G', hΦ', hΦG', hGG, hΦΦ⟩ := hKf F E (2 + 2) 𝔢.S 𝔣.S hS Φ G hΦ hΦG
  have hkill' : ∀ i, Kills 𝔣.S Φ' (b' i) := fun i L' t' h => by
    rw [hΦΦ L' t' (pt_card _ _ _ _ h)]
    exact hΦ2 i L' t' h
  obtain ⟨P₀, κ₂, D₂, hκ₂, hB₂, hP0, hPE, hPF⟩ := sep hEV hVB hSep (by norm_num) 𝔢.toAmp 𝔣.toAmp hS 𝔵.Λ 𝔵.t hΛ
    (fun w hw => (ht w hw).1) sE sF
    (fun y hy => ⟨hη.trans ((hsE y).mp hy).1, ((hsE y).mp hy).2.1, ((hsE y).mp hy).2.2.2⟩)
    (fun y hy => ⟨hη.trans ((hsF y).mp hy).1, ((hsF y).mp hy).2.1, ((hsF y).mp hy).2.2.2⟩)
  have hκ : ∀ w ∈ κ₁ ∪ κ₂, w ∉ 𝔢.S := fun w hw => (Finset.mem_union.mp hw).elim (hκ₁ w) (hκ₂ w)
  obtain ⟨γ, hγ1, hγ0, hγ⟩ := hGeo (κ₁ ∪ κ₂) hκ 𝔵.t (fun w hw => ht w (hκ w hw)) (D₁ + D₂)
  have hP : ∀ y ∈ (map C γ * P₀ : PR E (2 + 2)).vars, y.1 ∉ 𝔢.S := fun y hy =>
    (Finset.mem_union.mp (vars_mul _ _ hy)).elim (fun h => hκ _ (hγ1 y (vars_map _ _ h))) fun h => hκ₂ _ (hB₂.1 y h)
  have hVB0 := hVB F E (2 + 2) 0 (fun _ => 0) (fun _ => Multiset.replicate (2 + 2) 0) (map C γ * P₀) fun _ _ => by simp
  have hP' : ∀ y ∈ (bcPR F (map C γ * P₀ : PR E (2 + 2))).vars, y.1 ∉ 𝔣.S := fun y hy h => by
    obtain ⟨y', h1, h2⟩ := hVB0.2.1 y hy
    exact hP y' h1 ((hS _).mpr (h2 ▸ h))
  obtain ⟨uE, w, huE, hw, hE⟩ := hE Φ G hΦ hΦG (hb3 evE hevE hevz.comm χ hχ1 hχ4 hχ5 Φ G hΦ hΦ1 hΦG) _ hP
  obtain ⟨uF, huF, hF⟩ := hF Φ' G' hΦ' hΦG' (hb3' evF hevF χ hχ1 hχ4 hχ5 Φ' G' hΦ' hkill' hΦG') _ hP'
  refine ⟨sE, sp.filter (η < ·), sF, uE, w, uF, x * val x 𝔵.Λ 𝔵.t (map C γ * P₀ : PR E (2 + 2)) * evK L (hval 𝔵.t) Φ, ?_, hsE,
    fun a => by rw [Finset.mem_filter, and_comm]; rfl, hsF, fun y hy => ?_, fun a _ => ?_, fun y hy => ?_, fun s₀ => ?_⟩
  · rw [map_mul, val_gam]
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hx.ne') (mul_ne_zero hγ0 (hP0 x hx.ne'))) hΦ0
  · by_cases hg : At μE 𝔢.S y.2 𝔵.Λ 𝔵.t
    · refine ⟨_, huE y hy L 𝔵.t (hL ▸ hg), fun _ h => ?_, fun h => absurd hg h⟩
      rw [hL, h]
    · obtain ⟨L', t', h1, h2⟩ := hPE y hy hg
      refine ⟨_, huE y hy L' t' h1, fun h => absurd h hg, fun _ => ?_⟩
      rw [map_mul, h2, mul_zero, mul_zero, zero_mul]
  · refine ⟨_, hw a L hL, fun _ h => ?_, fun h => absurd trivial h⟩
    rw [show a = x from h]
  · by_cases hg : ∃ Λ' t', At μF 𝔣.S y.2 Λ' t' ∧ 𝔵.Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢.S, 𝔵.t w = bcSat t' w
    · obtain ⟨Λ', t', h1, h2, h3⟩ := id hg
      obtain ⟨L', rfl⟩ := (bdLem F (2 + 2) ∅ ∅ 0 0 0 0 0 0).2.2.2 Λ' fun τ => (h1.1 τ).1
      refine ⟨_, huF y hy L' t' h1, fun _ h => ?_, fun h => absurd hg h⟩
      rw [h, hΦΦ L' t' fun v hv => (h1.2 v hv).1,
        (hVB F E (2 + 2) x _ t' _ fun z hz => (h1.2 _ fun h => hP z hz ((hS _).mpr h)).1).1, ← h2,
        val_congr x _ _ _ _ h3 _ hP, evK_congr hTS _ Φ hΦ L (fun y => L' (y.1.comp (algebraMap F E), y.2)) _ _ (hL.trans h2) h3]
    · obtain ⟨L', t', h1, h2⟩ := hPF y hy hg
      refine ⟨_, huF y hy L' t' h1, fun h => absurd h hg, fun _ => ?_⟩
      rw [map_mul, map_mul, h2, mul_zero, mul_zero, zero_mul]
  obtain ⟨ME, hME, hE⟩ := hE (2 * p) (by omega) s₀
  obtain ⟨MF, hMF, hF⟩ := hF (2 * p) N s₀
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hγ evE evF hevE hevF)
  refine ⟨ME + (‖c‖ + 1) * MF, ?_⟩
  filter_upwards [hE, eventually_ge_atTop J, deg_ev d hd p hp (s₀ + D₂)] with j hE hj hdeg m hm m' hm'
  have hBd : Bd (κ₁ ∪ κ₂) (D₁ + D₂) ((j + m') / p) (chebP η (j / (2 * p) + m) * (trunc (d j) G * P₀) : PR E (2 + 2)) := by
    have h1 := (bdLem E (2 + 2) _ _ _ _ _ _ _ _).1 (hB₁ (d j)) hB₂
    have h2 := (bdLem E (2 + 2) _ _ _ _ _ _ _ _).1 ((bdLem E (2 + 2) (κ₁ ∪ κ₂) ∅ 0 0 0 0 0 0).2.1 η (j / (2 * p) + m)) h1
    refine (bdLem E (2 + 2) _ _ _ _ _ _ _ 0).2.2.1 ?_ (by omega) ?_ h2
    · intro z hz
      simpa using hz
    · have := hdeg m'
      omega
  obtain ⟨gE, gF, r1, r2, r3⟩ := hJ (j + m') (by omega) _ hBd.1 hBd.2.1 hBd.2.2
  have q1 : (map C γ * (chebP η (j / (2 * p) + m) * (trunc (d j) G * P₀)) : PR E (2 + 2)) =
      chebP η (j / (2 * p) + m) * (trunc (d j) G * (map C γ * P₀)) := by ring
  rw [q1] at r1 r2
  rw [map_mul (bcPR F), map_mul (bcPR F), hVB0.2.2, ← hGG] at r2
  have b1 := hE (d j) m hm m' hm' gE r1
  have b2 := hF j (d j) m hm m' hm' gF r2
  refine le_trans ?_ (comb_bd ME MF ‖c‖ hME hMF (norm_nonneg _) (d j) cE cF j _ _ _ _ (Nat.cast_nonneg _) (by positivity)
    (by positivity) b1 b2)
  rw [← norm_mul, ← norm_neg (_ - _ - _)]
  refine le_trans (le_of_eq ?_) (norm_add_le _ _)
  congr 1
  rw [r3, mul_sub, Finset.mul_sum, ← sub_eq_zero]
  have : ∀ (u v : ℂ), u * (-c * v) = -(c * (u * v)) := fun u v => by ring
  simp only [this, Finset.sum_neg_distrib, id]
  ring
