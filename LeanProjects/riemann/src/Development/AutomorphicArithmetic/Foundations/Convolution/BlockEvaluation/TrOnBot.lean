import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PowLeExpEventually
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Degree
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.AbsDAtTop
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.SideEst
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TotalDegreeAevalLe

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

private theorem UpperTheory.ConvolutionTheory.Ci.finSplit {A B : Type} (x : ℝ) (PE : A → Prop) (PF : B → Prop)
    (Q : (ℝ × A) ⊕ (ℝ × B) → Prop) (hE : ∀ y, Q (Sum.inl y) ↔ y.1 = x ∧ PE y.2)
    (hF : ∀ y, Q (Sum.inr y) ↔ y.1 = x ∧ PF y.2) (hfin : {i | Q i}.Finite) (τ : (ℝ × A) ⊕ (ℝ × B) → ℂ) :
    {V | PF V}.Finite ∧ ∑ᶠ i ∈ {i | Q i}, τ i =
      (∑ᶠ V ∈ {V | PE V}, τ (Sum.inl (x, V))) + ∑ᶠ V ∈ {V | PF V}, τ (Sum.inr (x, V)) := by
  have iE : Function.Injective fun V : A => (Sum.inl (x, V) : (ℝ × A) ⊕ (ℝ × B)) := fun V W h => by simpa using h
  have iF : Function.Injective fun V : B => (Sum.inr (x, V) : (ℝ × A) ⊕ (ℝ × B)) := fun V W h => by simpa using h
  have hS : {i | Q i} = (fun V : A => (Sum.inl (x, V) : (ℝ × A) ⊕ (ℝ × B))) '' {V | PE V} ∪
      (fun V : B => (Sum.inr (x, V) : (ℝ × A) ⊕ (ℝ × B))) '' {V | PF V} := by
    ext i
    rcases i with ⟨a, V⟩ | ⟨a, V⟩
    · simp only [Set.mem_setOf_eq, hE, Set.mem_union, Set.mem_image]
      constructor
      · rintro ⟨rfl, h⟩; exact Or.inl ⟨V, h, rfl⟩
      · rintro (⟨W, h, e⟩ | ⟨W, h, e⟩)
        · cases e; exact ⟨rfl, h⟩
        · cases e
    · simp only [Set.mem_setOf_eq, hF, Set.mem_union, Set.mem_image]
      constructor
      · rintro ⟨rfl, h⟩; exact Or.inr ⟨V, h, rfl⟩
      · rintro (⟨W, h, e⟩ | ⟨W, h, e⟩)
        · cases e
        · cases e; exact ⟨rfl, h⟩
  rw [hS] at hfin ⊢
  rw [Set.finite_union] at hfin
  refine ⟨Set.Finite.of_finite_image hfin.2 iF.injOn, ?_⟩
  rw [finsum_mem_union _ hfin.1 hfin.2, finsum_mem_image iE.injOn, finsum_mem_image iF.injOn]
  rw [Set.disjoint_left]
  rintro _ ⟨V, -, rfl⟩ ⟨W, -, e⟩
  cases e

private theorem UpperTheory.ConvolutionTheory.Ci.abs2 {A B : Type} (τE : ℝ × A → ℕ → ℂ) (τF : ℝ × B → ℕ → ℂ) (actE : ℝ × A → Prop)
    (actF : ℝ × B → Prop) (gE : A → Prop) (gF : B → Prop) (c : ℂ) (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (p : ℕ) (hp : 0 < p)
    (cE cF : ℝ) (d : ℕ → ℕ) (hd : Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0))
    (hd' : ∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial)
    (eE : ∀ i, actE i → 0 < i.1 → ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop, τE i j = ∑ ζ ∈ s, c ζ * ζ ^ j)
    (eF : ∀ i, actF i → 0 < i.1 → ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop, τF i j = ∑ ζ ∈ s, c ζ * ζ ^ j)
    (main : ∀ η : ℝ, 0 < η → η < x → ∃ (sE : Finset (ℝ × A)) (sF : Finset (ℝ × B)) (uE : ℝ × A → ℕ → ℂ)
      (uF : ℝ × B → ℕ → ℂ) (w : ℝ → ℂ), w x ≠ 0 ∧ (∀ y, y ∈ sE ↔ η < y.1 ∧ actE y) ∧ (∀ y, y ∈ sF ↔ η < y.1 ∧ actF y) ∧
      (∀ y ∈ sE, (gE y.2 → Tendsto (uE y) atTop (𝓝 (w y.1))) ∧ (¬ gE y.2 → Tendsto (uE y) atTop (𝓝 0))) ∧
      (∀ y ∈ sF, (gF y.2 → Tendsto (uF y) atTop (𝓝 (w y.1))) ∧ (¬ gF y.2 → Tendsto (uF y) atTop (𝓝 0))) ∧
      ∀ (N : ℝ) (s₀ : ℕ), ∃ ME MF : ℝ, 0 ≤ ME ∧ 0 ≤ MF ∧ ∀ᶠ j : ℕ in atTop, ∀ m ≤ s₀, ∀ m' ≤ s₀, ∃ z : ℂ,
        ‖c * z - ∑ y ∈ sE, uE y (d j) * (y.1 : ℂ) ^ d j * (cheb η (j / p + m) y.1 : ℂ) * τE y (j + m')‖ ≤
          ME ^ (d j + 1) * (Real.exp (cE * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j)) ∧
        ‖z - ∑ y ∈ sF, uF y (d j) * (y.1 : ℂ) ^ d j * (cheb η (j / p + m) y.1 : ℂ) * τF y (j + m')‖ ≤
          MF ^ (d j + 1) * (Real.exp (cF * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) :
    ∀ᶠ j : ℕ in atTop, ∑ᶠ V ∈ {V | actE (x, V) ∧ gE V}, τE (x, V) j = c * ∑ᶠ V ∈ {V | actF (x, V) ∧ gF V}, τF (x, V) j := by
  classical
  have key := UpperTheory.ConvolutionTheory.Ci.abs ((ℝ × A) ⊕ (ℝ × B)) (Sum.elim Prod.fst Prod.fst) (Sum.elim τE fun y j => -c * τF y j)
    (Sum.elim actE actF) (Sum.elim (fun y => gE y.2) fun y => gF y.2) x hx hx1 p hp (max cE cF) d hd hd' ?_ ?_
  · obtain ⟨hfin, hev⟩ := key
    filter_upwards [hev] with j hj
    obtain ⟨hF, hs⟩ := UpperTheory.ConvolutionTheory.Ci.finSplit x (fun V => actE (x, V) ∧ gE V) (fun V => actF (x, V) ∧ gF V) _
      (by rintro ⟨a, V⟩; simp only [Sum.elim_inl]; constructor
          · rintro ⟨h1, h2, rfl⟩; exact ⟨rfl, h1, h2⟩
          · rintro ⟨rfl, h1, h2⟩; exact ⟨h1, h2, rfl⟩)
      (by rintro ⟨a, V⟩; simp only [Sum.elim_inr]; constructor
          · rintro ⟨h1, h2, rfl⟩; exact ⟨rfl, h1, h2⟩
          · rintro ⟨rfl, h1, h2⟩; exact ⟨h1, h2, rfl⟩) hfin (fun i => Sum.elim τE (fun y j => -c * τF y j) i j)
    replace hj := hs.symm.trans hj
    simp only [Sum.elim_inl, Sum.elim_inr] at hj
    change ∑ᶠ V ∈ {V | actE (x, V) ∧ gE V}, τE (x, V) j = c * ∑ᶠ V ∈ {V | actF (x, V) ∧ gF V}, τF (x, V) j
    rw [finsum_mem_eq_finite_toFinset_sum _ hF] at hj ⊢
    rw [← Finset.mul_sum] at hj
    linear_combination hj
  · rintro (y | y) h1 h2
    · exact eE y h1 h2
    · obtain ⟨s, e, h0, h⟩ := eF y h1 h2
      refine ⟨s, fun ζ => -c * e ζ, h0, ?_⟩
      filter_upwards [h] with j hj
      simp only [Sum.elim_inr, hj, Finset.mul_sum, mul_assoc]
  · intro η h0 h1
    obtain ⟨sE, sF, uE, uF, w, hw, hsE, hsF, huE, huF, hb⟩ := main η h0 h1
    refine ⟨sE.disjSum sF, Sum.elim uE uF,
      Sum.elim (fun y => if gE y.2 then w y.1 else 0) fun y => if gF y.2 then w y.1 else 0, w x, hw, ?_, ?_, ?_, ?_, ?_⟩
    · rintro (y | y)
      · simpa using hsE y
      · simpa using hsF y
    · rintro (y | y) hy
      · have := huE y (by simpa using hy)
        by_cases hg : gE y.2
        · simpa [hg] using this.1 hg
        · simpa [hg] using this.2 hg
      · have := huF y (by simpa using hy)
        by_cases hg : gF y.2
        · simpa [hg] using this.1 hg
        · simpa [hg] using this.2 hg
    · rintro (y | y) - hg ha
      · simp only [Sum.elim_inl] at hg ha ⊢
        rw [if_pos hg, ha]
      · simp only [Sum.elim_inr] at hg ha ⊢
        rw [if_pos hg, ha]
    · rintro (y | y) - hg
      · simp only [Sum.elim_inl] at hg ⊢
        rw [if_neg hg]
      · simp only [Sum.elim_inr] at hg ⊢
        rw [if_neg hg]
    · intro N s₀
      obtain ⟨ME, MF, hME, hMF, hev⟩ := hb N s₀
      refine ⟨ME + (1 + ‖c‖) * MF, ?_⟩
      filter_upwards [hev] with j hj m hm m' hm'
      obtain ⟨z, h2, h3⟩ := hj m hm m' hm'
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr]
      set SE := ∑ y ∈ sE, uE y (d j) * (y.1 : ℂ) ^ d j * (cheb η (j / p + m) y.1 : ℂ) * τE y (j + m') with hSE
      set SF := ∑ y ∈ sF, uF y (d j) * (y.1 : ℂ) ^ d j * (cheb η (j / p + m) y.1 : ℂ) * τF y (j + m') with hSF
      have e1 : ∑ y ∈ sF, uF y (d j) * (y.1 : ℂ) ^ d j * (cheb η (j / p + m) y.1 : ℂ) * (-c * τF y (j + m')) = -c * SF := by
        rw [hSF, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [e1]
      set Er := Real.exp (max cE cF * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j)
        with hEr
      have mono : ∀ e : ℝ, e ≤ max cE cF →
          Real.exp (e * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j) ≤ Er := by
        intro e he
        rw [hEr]
        gcongr
      have hEr0 : 0 ≤ Er := by rw [hEr]; positivity
      have h4 : ‖c * z - SE‖ ≤ ME ^ (d j + 1) * Er :=
        h2.trans (mul_le_mul_of_nonneg_left (mono _ (le_max_left _ _)) (by positivity))
      have h5 : ‖z - SF‖ ≤ MF ^ (d j + 1) * Er :=
        h3.trans (mul_le_mul_of_nonneg_left (mono _ (le_max_right _ _)) (by positivity))
      have h6 : ‖c‖ ≤ (1 + ‖c‖) ^ (d j + 1) :=
        (le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ (le_add_of_nonneg_right (norm_nonneg _)) (by omega))
      have e2 : SE + -c * SF = c * (z - SF) - (c * z - SE) := by ring
      rw [e2]
      calc _ ≤ ‖c * (z - SF)‖ + ‖c * z - SE‖ := norm_sub_le _ _
        _ ≤ (1 + ‖c‖) ^ (d j + 1) * (MF ^ (d j + 1) * Er) + ME ^ (d j + 1) * Er := by
          rw [norm_mul]; gcongr
        _ = (ME ^ (d j + 1) + ((1 + ‖c‖) * MF) ^ (d j + 1)) * Er := by rw [mul_pow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_add_pow_le hME (by positivity) (by omega)) hEr0

private theorem UpperTheory.ConvolutionTheory.Ci.chiEx (η : ℝ) (hη : 0 < η) : ∃ χ : ℝ → ℝ, Continuous χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
    (∀ x ≥ η, χ x = 1) ∧ ∀ x ≤ η / 2, χ x = 0 := by
  refine ⟨fun x => max 0 (min 1 (2 * x / η - 1)), by fun_prop, fun x => ⟨le_max_left _ _, ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · exact max_le zero_le_one (min_le_left _ _)
  · have : 2 ≤ 2 * x / η := by rw [le_div_iff₀ hη]; linarith
    show max 0 (min 1 (2 * x / η - 1)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  · have : 2 * x / η ≤ 1 := by rw [div_le_iff₀ hη]; linarith
    exact max_eq_left ((min_le_right _ _).trans (by linarith))

private theorem UpperTheory.ConvolutionTheory.Ci.degEv (d : ℕ → ℕ) (hd : Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0)) (p : ℕ) (hp : 0 < p)
    (e : ℕ) : ∀ᶠ j : ℕ in atTop, j / (2 * p) + d j + e ≤ j / p := by
  have h1 := hd.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * p) by positivity))
  filter_upwards [h1, eventually_ge_atTop (4 * p * e + 1)] with j hj hj'
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  rw [div_lt_div_iff₀ hj0 (by positivity), one_mul] at hj
  have h2 : d j * (4 * p) < j := by exact_mod_cast hj
  have h3 := Nat.div_mul_le_self j (2 * p)
  rw [Nat.le_div_iff_mul_le hp]
  nlinarith

private theorem UpperTheory.ConvolutionTheory.Ci.trOn_bot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) : trOn ⊥ T = 0 := by
  have : prj (⊥ : Submodule ℂ H) = 0 := by
    ext v
    have h := Submodule.starProjection_apply_mem (⊥ : Submodule ℂ H).topologicalClosure v
    have hb : (⊥ : Submodule ℂ H).topologicalClosure = ⊥ := IsClosed.submodule_topologicalClosure_eq (by simp)
    have h2 : ∀ z : H, z ∈ (⊥ : Submodule ℂ H).topologicalClosure → z = 0 := fun z hz => by rwa [hb, Submodule.mem_bot] at hz
    exact h2 _ h
  rw [trOn, this]
  simp [trace]

private theorem UpperTheory.ConvolutionTheory.Ci.eig_bot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) (A : H →L[ℂ] H) (hA : ‖A‖ ≤ 1) (x : ℝ) (hx : 1 < x) : eigIn V A x = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨-, hv⟩
  have h : A v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 hv
  have h1 := A.le_opNorm v
  rw [h, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h1
  have h2 : ‖v‖ ≤ 0 := by nlinarith [norm_nonneg v, norm_nonneg A]
  exact norm_le_zero_iff.1 h2

private theorem UpperTheory.ConvolutionTheory.Ci.ptCard {K : Type} [Field K] [NumberField K] {n : ℕ} (b : Datum K n) (S : Set (Pl K)) (Λ) (t)
    (h : b.Pt S Λ t) : ∀ w ∉ S, (t w).card = n := by
  obtain ⟨lam, m, B, h1, -, h3⟩ := h
  intro w hw
  rw [h3 w hw, Multiset.card_sum]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) b.sum
  rw [Multiset.card_map]
  exact ((h1 i).2 w hw).1

private theorem UpperTheory.ConvolutionTheory.Ci.valCongr {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ) (t t' : Pl K → Multiset ℂ)
    (S : Set (Pl K)) (h : ∀ w ∉ S, t w = t' w) (P : PR K n) (hP : ∀ y ∈ P.vars, y.1 ∉ S) : val x Λ t P = val x Λ t' P :=
  eval₂Hom_congr' rfl (fun y hy _ => by rw [hval, hval, h _ (hP y hy)]) rfl

private theorem UpperTheory.ConvolutionTheory.Ci.valC {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ) (t : Pl K → Multiset ℂ)
    (γ : MvPolynomial (Pl K × Fin n) ℂ) : val x Λ t (map C γ : PR K n) = eval (hval t) γ := by
  rw [val, coe_eval₂Hom, eval₂_map]
  change _ = eval₂ (RingHom.id ℂ) _ _
  congr 1
  ext c
  simp

set_option maxHeartbeats 1600000 in
theorem UpperTheory.ConvolutionTheory.Ci.ciOf :
    TrExp → EvVal → ValBc → KillEx → KfBc → TruncSpec → SepPoly → OneSide → EvEx → Kill → CI := by
  classical
  intro hT hV hB hKE hKB hTS hSP hOS hEv hKl F E _ _ _ _ _ _ _ n l hn hl μE _ μF _ θ 𝔢 𝔣 c hG Λ t hΛ ht hoff x hx
  obtain ⟨hS, p, C₀, hp, hG⟩ := hG
  obtain ⟨e0, e1, -, evE, hevE, hinE⟩ := hEv E n hn μE 𝔢.toAmp
  obtain ⟨f0, f1, -, evF, hevF, hinF⟩ := hEv F n hn μF 𝔣.toAmp
  rcases lt_or_ge 1 x with hx1 | hx1
  · refine Eventually.of_forall fun j => ?_
    simp only [Side.tr, eig_bot _ _ e1 x hx1, eig_bot _ _ f1 x hx1, trOn_bot, finsum_zero, mul_zero]
  have bE := bdLem E n
  have msE := (bE ∅ ∅ 0 0 0 0 0 0).2.2.2
  have msF := (bdLem F n ∅ ∅ 0 0 0 0 0 0).2.2.2
  obtain ⟨L, rfl⟩ := msE Λ hΛ
  obtain ⟨cE, hsE⟩ := sideEst hOS hV hTS E n l hn μE θ 𝔢 evE hevE hinE C₀
  obtain ⟨cF, hsF⟩ := sideEst hOS hV hTS F n l hn μF (Twist.id μF) 𝔣 evF hevF hinF C₀
  obtain ⟨d, hd, hd'⟩ := FX.degree
  have key := abs2
    (fun (y : ℝ × Submodule ℂ (LL μE)) j => trOn (eigIn y.2 𝔢.toAmp.A y.1) ((𝔢.Uq 0 ^ j) ∘L Rop μE 𝔢.g ∘L θ.U))
    (fun (y : ℝ × Submodule ℂ (LL μF)) j => trOn (eigIn y.2 𝔣.toAmp.A y.1) ((𝔣.Uq 0 ^ j) ∘L Rop μF 𝔣.g ∘L (Twist.id μF).U))
    (fun y => IsSummand μE y.2 ∧ y.2.map (θ.U : LL μE →ₗ[ℂ] LL μE) = y.2 ∧ eigIn y.2 𝔢.toAmp.A y.1 ≠ ⊥)
    (fun y => IsSummand μF y.2 ∧ y.2.map ((Twist.id μF).U : LL μF →ₗ[ℂ] LL μF) = y.2 ∧ eigIn y.2 𝔣.toAmp.A y.1 ≠ ⊥)
    (fun V => At μE 𝔢.S V (msOf L) t)
    (fun V => ∃ Λ' t', At μF 𝔣.S V Λ' t' ∧ msOf L = bcInf Λ' ∧ ∀ w ∉ 𝔢.S, t w = bcSat t' w)
    c x hx hx1 (2 * p) (by omega) cE cF d hd hd' ?_ ?_ ?_
  · filter_upwards [key] with j hj
    unfold Side.tr
    convert hj using 1
    · refine finsum_mem_inter_support_eq' _ _ _ fun V hV0 => ?_
      have : eigIn V 𝔢.toAmp.A x ≠ ⊥ := fun h => hV0 (by simp only [h, trOn_bot])
      exact ⟨fun h => ⟨⟨h.1, h.2.1, this⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2.1, h.2⟩⟩
    · congr 1
      refine finsum_mem_inter_support_eq' _ _ _ fun V hV0 => ?_
      have : eigIn V 𝔣.toAmp.A x ≠ ⊥ := fun h => hV0 (by simp only [h, trOn_bot])
      exact ⟨fun h => ⟨⟨h.1, h.2.1, this⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2.1, h.2⟩⟩
  · intro y hy h0
    have hη : 0 < min (y.1 / 2) 1 := lt_min (by linarith) one_pos
    obtain ⟨χ, c1, c2, c3, -⟩ := chiEx _ hη
    obtain ⟨s, s1, s2, -⟩ := hsE _ hη (min_le_right _ _) χ c1 c2 c3
    exact hT E n l hl μE θ 𝔢 y.2 y.1 e0 hy.1 (s2 y ((s1 y).2 ⟨(min_le_left _ _).trans_lt (by linarith), hy⟩))
  · intro y hy h0
    have hη : 0 < min (y.1 / 2) 1 := lt_min (by linarith) one_pos
    obtain ⟨χ, c1, c2, c3, -⟩ := chiEx _ hη
    obtain ⟨s, s1, s2, -⟩ := hsF _ hη (min_le_right _ _) χ c1 c2 c3
    exact hT F n l hl μF _ 𝔣 y.2 y.1 f0 hy.1 (s2 y ((s1 y).2 ⟨(min_le_left _ _).trans_lt (by linarith), hy⟩))
  intro η h0 h1
  obtain ⟨χ, c1, c2, c3, c4⟩ := chiEx η h0
  have c5 : ∀ x, |χ x| ≤ 1 := fun x => by rw [abs_of_nonneg (c2 x).1]; exact (c2 x).2
  obtain ⟨sE, conjLinearRankOne, -, sE3⟩ := hsE η h0 (h1.le.trans hx1) χ c1 c2 c3
  obtain ⟨sF, sF1, -, sF3⟩ := hsF η h0 (h1.le.trans hx1) χ c1 c2 c3
  obtain ⟨B, _, b, hb, hk⟩ := hKl E n hn μE 𝔢.toAmp η h0
  obtain ⟨B', _, b', hb', hk'⟩ := hKl F n hn μF 𝔣.toAmp η h0
  obtain ⟨Φ, hΦ, hΦ0, hΦ1, hΦ2⟩ := hKE F E n 𝔢.S 𝔣.S hS B B' b b' hb hb' L t (fun w hw => (ht w hw).1) hoff
  obtain ⟨⟨G, hGen⟩, hTG⟩ := hTS E n 𝔢.S Φ hΦ
  obtain ⟨⟨κ₁, D₁, hκ₁, hBd⟩, hlim, -⟩ := hTG G hGen
  obtain ⟨Φ', G', hΦ', hGen', htr, hev'⟩ := hKB F E n 𝔢.S 𝔣.S hS Φ G hΦ hGen
  have hkill' : ∀ i, Kills 𝔣.S Φ' (b' i) := fun i L' t' hpt => by
    rw [hev' L' t' (ptCard _ _ _ _ hpt)]
    exact hΦ2 i L' t' hpt
  have pE : ∀ y : sE, ∃ Λ t, At μE 𝔢.S y.1.2 Λ t := fun y =>
    have h := (conjLinearRankOne y).1 y.2
    (hV E n hn μE 𝔢.toAmp y.1.2 y.1.1 (h0.trans h.1) h.2.1).1 h.2.2.2
  have pF : ∀ y : sF, ∃ Λ t, At μF 𝔣.S y.1.2 Λ t := fun y =>
    have h := (sF1 y).1 y.2
    (hV F n hn μF 𝔣.toAmp y.1.2 y.1.1 (h0.trans h.1) h.2.1).1 h.2.2.2
  choose ΛE tE hE using pE
  choose ΛF tF hF using pF
  obtain ⟨P₀, κ₂, D₂, hκ₂, hP₀, hP1, hP2⟩ := hSP E n 𝔢.S (msOf L) t
    ({y : sE // ¬ At μE 𝔢.S y.1.2 (msOf L) t} ⊕
      {y : sF // ¬ ∃ Λ' t', At μF 𝔣.S y.1.2 Λ' t' ∧ msOf L = bcInf Λ' ∧ ∀ w ∉ 𝔢.S, t w = bcSat t' w})
    (Sum.elim (fun y => ΛE y.1) fun y => bcInf (ΛF y.1)) (Sum.elim (fun y => tE y.1) fun y => bcSat (tF y.1))
    hΛ (fun w hw => (ht w hw).1)
    (by rintro (y | y) τ
        · exact ((hE y.1).1 τ).1
        · exact ((hF y.1).1 _).1)
    (by rintro (y | y) w hw
        · exact ((hE y.1).2 w hw).1
        · exact (Multiset.card_map _ _).trans ((hF y.1).2 _ (mt (hS w).2 hw)).1)
    (by rintro (y | y) ⟨a1, a2⟩
        · refine y.2 ⟨fun τ => ?_, fun w hw => ?_⟩
          · exact (congrArg (SInf μE y.1.1.2 τ) (congrFun a1 τ)).mpr ((hE y.1).1 τ)
          · exact (congrArg (SSat μE y.1.1.2 w) (a2 w hw)).mpr ((hE y.1).2 w hw)
        · exact y.2 ⟨_, _, hF y.1, a1, a2⟩)
  have hκ : ∀ w ∈ κ₁ ∪ κ₂, w ∉ 𝔢.S := fun w hw => (Finset.mem_union.1 hw).elim (hκ₁ w) (hκ₂ w)
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := hG (κ₁ ∪ κ₂) hκ t (fun w hw => ht w (hκ w hw)) (D₁ + D₂)
  have hPv : ∀ y ∈ (map C γ * P₀ : PR E n).vars, y.1 ∉ 𝔢.S := fun y hy => by
    rcases Finset.mem_union.1 (vars_mul _ _ hy) with h | h
    · exact hκ _ (hγ1 y (vars_map _ _ h))
    · exact hκ₂ _ (hP₀.1 y h)
  have hB0 := hB F E n 0 (fun _ => 0) (fun _ => Multiset.replicate n 0) (map C γ * P₀) (fun _ _ => Multiset.card_replicate _ _)
  have hPv' : ∀ y ∈ (bcPR F (map C γ * P₀ : PR E n)).vars, y.1 ∉ 𝔣.S := fun y hy => by
    obtain ⟨y', h1, h2⟩ := hB0.2.1 y hy
    rw [h2]
    exact mt (hS _).2 (hPv y' h1)
  obtain ⟨uE, uE1, uE2⟩ := sE3 Φ G hΦ hGen (hk evE hevE χ c1 c4 c5 Φ G hΦ hΦ1 hGen) _ hPv
  obtain ⟨uF, uF1, uF2⟩ := sF3 Φ' G' hΦ' hGen' (hk' evF hevF χ c1 c4 c5 Φ' G' hΦ' hkill' hGen') _ hPv'
  have vF : ∀ (V : Submodule ℂ (LL μF)) (a : ℝ) Λ' t', At μF 𝔣.S V Λ' t' →
      val a Λ' t' (bcPR F (map C γ * P₀ : PR E n)) = val a (bcInf Λ') (bcSat t') (map C γ * P₀ : PR E n) :=
    fun V a Λ' t' h => (hB F E n a Λ' t' _ fun y hy => (h.2 _ (mt (hS _).2 (hPv y hy))).1).1
  refine ⟨sE, sF, uE, uF, fun a => a * val a (msOf L) t (map C γ * P₀ : PR E n) * evK L (hval t) Φ, ?_, conjLinearRankOne, sF1, ?_, ?_, ?_⟩
  · refine mul_ne_zero (mul_ne_zero (by exact_mod_cast hx.ne') ?_) hΦ0
    rw [map_mul, valC]
    exact mul_ne_zero hγ2 (hP1 x hx.ne')
  · refine fun y hy => ⟨fun hg => uE1 y hy L t hg, fun hg => ?_⟩
    obtain ⟨L', hL'⟩ := msE (ΛE ⟨y, hy⟩) fun τ => ((hE _).1 τ).1
    have := uE1 y hy L' (tE ⟨y, hy⟩) (hL' ▸ hE ⟨y, hy⟩)
    have z : val y.1 (ΛE ⟨y, hy⟩) (tE ⟨y, hy⟩) P₀ = 0 := hP2 (Sum.inl ⟨⟨y, hy⟩, hg⟩) y.1
    rwa [hL', map_mul, z, mul_zero, mul_zero, zero_mul] at this
  · refine fun y hy => ⟨fun hg => ?_, fun hg => ?_⟩
    · obtain ⟨Λ', t', a1, a2, a3⟩ := hg
      obtain ⟨L', rfl⟩ := msF Λ' fun τ => (a1.1 τ).1
      have := uF1 y hy L' t' a1
      rw [vF _ _ _ _ a1, hev' L' t' (fun v hv => (a1.2 v hv).1), ← a2, ← valCongr y.1 _ t _ 𝔢.S a3 _ hPv] at this
      have e : evK (fun y : Ix E n => L' (y.1.comp (algebraMap F E), y.2)) (hval (bcSat t')) Φ = evK L (hval t) Φ := by
        obtain ⟨u, u1, u2⟩ := hlim L t
        obtain ⟨u', u1', u2'⟩ := hlim (fun y : Ix E n => L' (y.1.comp (algebraMap F E), y.2)) (bcSat t')
        have : u' = u := funext fun k => by
          have b1 := u2 1 k
          have b2 := u2' 1 k
          have b3 : msOf (fun y : Ix E n => L' (y.1.comp (algebraMap F E), y.2)) = msOf L := a2.symm
          rw [b3, ← valCongr 1 _ t _ 𝔢.S a3 _ (fun y hy => hκ₁ _ ((hBd k).1 y hy)), b1] at b2
          simpa using b2.symm
        rw [this] at u1'
        exact tendsto_nhds_unique u1' u1
      rwa [e] at this
    · obtain ⟨L', hL'⟩ := msF (ΛF ⟨y, hy⟩) fun τ => ((hF _).1 τ).1
      have := uF1 y hy L' (tF ⟨y, hy⟩) (hL' ▸ hF ⟨y, hy⟩)
      have z : val y.1 (bcInf (ΛF ⟨y, hy⟩)) (bcSat (tF ⟨y, hy⟩)) P₀ = 0 := hP2 (Sum.inr ⟨⟨y, hy⟩, hg⟩) y.1
      rwa [hL', vF _ _ _ _ (hF ⟨y, hy⟩), map_mul, z, mul_zero, mul_zero, zero_mul] at this
  · intro N s₀
    obtain ⟨ME, hME, bdE⟩ := uE2 (2 * p) N s₀
    obtain ⟨MF, hMF, bdF⟩ := uF2 (2 * p) N s₀
    refine ⟨ME, MF, hME, hMF, ?_⟩
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hγ3 evE evF hevE hevF)
    filter_upwards [degEv d hd p hp (s₀ + D₂), eventually_ge_atTop j₀] with j hj hj' m hm m' hm'
    have r1 := (bE κ₁ κ₂ D₁ D₂ (d j) D₂ _ _).1 (hBd (d j)) hP₀
    have r2 := (bE (κ₁ ∪ κ₂) (κ₁ ∪ κ₂) 0 (D₁ + D₂) (j / (2 * p) + m) (d j + D₂) _ _).1
      ((bE (κ₁ ∪ κ₂) ∅ 0 0 0 0 0 0).2.1 η _) r1
    rw [Finset.union_idempotent, zero_add] at r2
    have hdiv : j / p ≤ (j + m') / p := Nat.div_le_div_right (Nat.le_add_right _ _)
    obtain ⟨fE, fF, g1, g2, g3⟩ := hj₀ (j + m') (by omega) _ r2.1 r2.2.1 (fun β => (r2.2.2 β).trans (by omega))
    have q1 : (map C γ * (chebP η (j / (2 * p) + m) * (trunc (d j) G * P₀)) : PR E n) =
        chebP η (j / (2 * p) + m) * (trunc (d j) G * (map C γ * P₀)) := by ring
    rw [q1] at g1 g2
    rw [map_mul (bcPR F), hB0.2.2, map_mul (bcPR F), ← htr] at g2
    refine ⟨twInt (Twist.id μF) fF, ?_, bdF j (d j) m hm m' hm' fF g2⟩
    rw [← g3]
    exact bdE j (d j) m hm m' hm' fE g1
