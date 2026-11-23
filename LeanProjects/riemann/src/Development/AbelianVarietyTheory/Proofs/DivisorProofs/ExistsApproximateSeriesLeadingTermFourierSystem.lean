import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruentTupleUnimodularImageOrLarge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLatticeQuadraticSumGeDiagonal

noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.Poinc.leadingTermLemmas

theorem leastVal {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hpos : ∀ x, x ≠ 0 → 0 < β x x) {x₀ : X}
    (hx₀ : x₀ ≠ 0) : ∃ x, x ≠ 0 ∧ ∀ x', x' ≠ 0 → β x x ≤ β x' x' := by
  classical
  have hex : ∃ n : ℕ, ∃ x, x ≠ 0 ∧ β x x = n :=
    ⟨(β x₀ x₀).toNat, x₀, hx₀, (Int.toNat_of_nonneg (hpos x₀ hx₀).le).symm⟩
  obtain ⟨x, hx, hxn⟩ := Nat.find_spec hex
  refine ⟨x, hx, fun x' hx' => ?_⟩
  rw [hxn, ← Int.toNat_of_nonneg (hpos x' hx').le]
  exact_mod_cast Nat.find_min' hex ⟨x', hx', (Int.toNat_of_nonneg (hpos x' hx').le).symm⟩

theorem congMod_of_span {X ι : Type} [AddCommGroup X] (N : ℕ) (g : X →+ X) (a : ι → X)
    (hspan : Submodule.span ℤ (Set.range a) = ⊤) (h : ∀ i, CongMod N (g (a i)) (a i)) : ∀ x, CongMod N (g x) x := by
  intro x
  have hx : x ∈ Submodule.span ℤ (Set.range a) := hspan ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h i
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨w, hw⟩ := hy; obtain ⟨w', hw'⟩ := hz
    exact ⟨w + w', by rw [map_add, hw, hw', smul_add]; abel⟩
  | smul n y _ hy =>
    obtain ⟨w, hw⟩ := hy
    exact ⟨n • w, by rw [map_zsmul, hw, smul_add, smul_comm]⟩

theorem unimod_comp (O : Type) [CommRing O] {X₀ X : Type} [AddCommGroup X₀] [Module O X₀] [AddCommGroup X] [Module O X]
    {N : ℕ} {k : X₀ →ₗ[ℤ] X} (hk : IsUnimodMod O N k) {g : X₀ →ₗ[ℤ] X₀}
    (h1 : ∀ (c : O) x, CongMod N (g (c • x)) (c • g x)) (h2 : (N : ℤ) ∣ LinearMap.det g - 1) :
    IsUnimodMod O N (k ∘ₗ g) := by
  obtain ⟨hk1, ε, hε⟩ := hk
  refine ⟨fun c x => ?_, ε, ?_⟩
  · obtain ⟨w, hw⟩ := h1 c x
    obtain ⟨w', hw'⟩ := hk1 c (g x)
    refine ⟨k w + w', ?_⟩
    simp only [LinearMap.comp_apply]
    rw [hw, map_add, map_nsmul, hw', smul_add]; abel
  · rw [← LinearMap.comp_assoc, LinearMap.det_comp]
    obtain ⟨u, hu⟩ := hε
    obtain ⟨v, hv⟩ := h2
    have e1 : LinearMap.det (ε.toLinearMap ∘ₗ k) = N * u + 1 := by linarith
    have e2 : LinearMap.det g = N * v + 1 := by linarith
    rw [e1, e2]
    exact ⟨u * (N * v + 1) + v, by ring⟩

theorem lin_sum {s l : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X ι : Type} [AddCommGroup X] [Fintype ι]
    (a : Fin l × Fin s → X) (δ : ι → LinearMap.BilinForm ℤ X) : lin W a (∑ i, δ i) = ∑ i, lin W a (δ i) := by
  simp only [lin, qW, LinearMap.sum_apply, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

theorem lin_smul {s l : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X]
    (a : Fin l × Fin s → X) (M : ℤ) (δ : LinearMap.BilinForm ℤ X) : lin W a (M • δ) = M * lin W a δ := by
  simp only [lin, qW, LinearMap.smul_apply, Finset.mul_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem prod_mono {s l m : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X V : Type} [AddCommGroup X] [CommRing V] (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (h : ∀ i y, 0 ≤ qW W (δ i) y) (a : Fin l × Fin s → X) :
    ∏ i, mono W t δ (fun v => a (i, v)) = ∏ j, t j ^ (lin W a (δ j)).toNat := by
  simp only [mono]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have h0 : 0 ≤ lin W a (δ j) := Finset.sum_nonneg fun i _ => h j _
  apply Int.natCast_inj.1
  rw [Int.toNat_of_nonneg h0, lin, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (h j _)

theorem prod_pow_mem {V ι : Type} [CommRing V] (I : Ideal V) (t : ι → V) (ht : ∀ i, t i ∈ I) (n : ι → ℕ) (S : Finset ι) :
    ∏ i ∈ S, t i ^ n i ∈ I ^ (∑ i ∈ S, n i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (ht i) _

theorem prod_pow_mem_mul {V ι : Type} [CommRing V] [Fintype ι] (t : ι → V) (n n' : ι → ℕ) (h : ∀ i, n i ≤ n' i)
    (j : ι) (hj : n j < n' j) :
    ∏ i, t i ^ n' i ∈ Ideal.span {∏ i, t i ^ n i} * Ideal.span (Set.range t) := by
  classical
  have e : ∏ i, t i ^ n' i = (∏ i, t i ^ n i) * ∏ i, t i ^ (n' i - n i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [← pow_add, Nat.add_sub_cancel' (h i)]
  rw [e]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
  refine Ideal.mem_of_dvd _ ((dvd_pow_self (t j) (Nat.sub_ne_zero_of_lt hj)).trans
    (Finset.dvd_prod_of_mem (fun i => t i ^ (n' i - n i)) (Finset.mem_univ j))) ?_
  exact Ideal.subset_span ⟨j, rfl⟩

theorem pow_le_span {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsPrincipalIdealRing V] {t : V}
    (ht : t ∈ maximalIdeal V) (ht0 : t ≠ 0) (b : ℕ) : ∃ j, maximalIdeal V ^ j ≤ Ideal.span {t ^ b} := by
  haveI : IsDiscreteValuationRing V :=
    { not_a_field' := fun h => ht0 (by rw [h] at ht; exact ht) }
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (pow_ne_zero b ht0) hϖ
  refine ⟨n, ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
  exact hn.dvd

end GlobalTheory.Poinc.leadingTermLemmas

open GlobalTheory.Poinc.leadingTermLemmas in

theorem GlobalTheory.Poinc.approx_of_vsys : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (bar : O → O), BddAct bar → ∀ (q : ℕ) (φ : InvFun O), IsPolFan bar q φ → ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∀ (N₁ : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y₀ : Φ.Y) (γ : Fin (Φ.m y₀) → LinearMap.BilinForm ℤ (Φ.X y₀)) (M : ℕ), 1 ≤ M → (∀ i, Φ.δ y₀ i = (M : ℤ) • γ i) → ∀ (d l : ℕ) (a : Fin l × Fin s → Φ.X y₀), Dominant bar φ d N₁ W γ a → ∀ (c : Fin l → Φ.Q) (e : ℕ), ∃ f : A, Φ.OrdGe φ d e f ∧ Φ.Leads y₀ a c e f := by
  classical
  intro O _ _ bar hB q φ hφ s W hW N₁ A _ _ Φ y₀ γ M hM hδ d l a hD c e
  obtain ⟨cW, hcW0, hcW⟩ := GlobalTheory.Poinc.QWDom.qW_ge s W hW
  obtain ⟨C, hC⟩ := Φ.lam
  have hq : ∀ y i μ, 0 ≤ qW W (Φ.δ y i) μ := fun y i μ => by
    have h1 := hcW (Φ.X y) (Φ.δ y i) (Φ.bal y i).1 (Φ.nonneg y i) μ
    have h2 : (0 : ℝ) ≤ ((∑ u, Φ.δ y i (μ u) (μ u) : ℤ) : ℝ) := by
      exact_mod_cast Finset.sum_nonneg fun u _ => Φ.nonneg y i _
    exact_mod_cast (mul_nonneg hcW0.le h2).trans h1
  have hl : ∀ y i (μ : Fin l × Fin s → Φ.X y), 0 ≤ lin W μ (Φ.δ y i) := fun y i μ =>
    Finset.sum_nonneg fun _ _ => hq y i _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max ((C * e : ℕ) / cW) (e / cW) := ⟨_, rfl⟩
  have hK1 : ((C * e : ℕ) : ℝ) ≤ cW * K := by
    rw [← div_le_iff₀' hcW0, hK]; exact le_max_left _ _
  have hK2 : (e : ℝ) ≤ cW * K := by
    rw [← div_le_iff₀' hcW0, hK]; exact le_max_right _ _
  obtain ⟨N₀, hN₀⟩ := GlobalTheory.Poinc.dichotomy O bar hB (Φ.X y₀) (Fin l × Fin s) a hD.span K
  obtain ⟨N, hNN₀, hN₁N, k, hkid, hk, hfour⟩ := Φ.four y₀ N₀
  obtain ⟨f, hf⟩ := hfour l a c e
  have hterm : ∀ y (β : LinearMap.BilinForm ℤ (Φ.X y)), β ∈ balForms bar (Φ.X y) → (∀ x, 0 ≤ β x x) →
      ∀ (lam : ℝ), 0 ≤ lam → (∀ x, x ≠ 0 → lam ≤ β x x) → ∀ μ ∈ orbit O N₁ N (k y) a,
      (∃ g : Φ.X y₀ ≃ₗ[O] Φ.X y, ∀ iu, g (a iu) = μ iu) ∨ cW * K * lam ≤ (lin W μ β : ℤ) := by
    intro y β hβ hnn lam hlam0 hlam μ hμ
    obtain ⟨g, g1, g2, -, g4⟩ := hμ
    rcases hN₀ N hNN₀ (Φ.X y) β hβ hnn lam hlam0 hlam (k y ∘ₗ g) μ (unimod_comp O (hk y) g1 g2)
      (fun i => g4 i) with h | hbig
    · exact Or.inl h
    · right
      calc cW * K * lam ≤ cW * ((∑ iu, β (μ iu) (μ iu) : ℤ) : ℝ) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hbig hcW0.le
        _ = ∑ i, cW * ((∑ u, β (μ (i, u)) (μ (i, u)) : ℤ) : ℝ) := by
            push_cast; rw [Fintype.sum_prod_type, Finset.mul_sum]
        _ ≤ ∑ i, ((qW W β fun u => μ (i, u) : ℤ) : ℝ) := Finset.sum_le_sum fun i _ => hcW (Φ.X y) β hβ.1 hnn _
        _ = _ := by rw [lin, Int.cast_sum]
  have hT : ∀ y (μ : Fin l × Fin s → Φ.X y),
      ∏ i, Φ.u y (fun v => μ (i, v)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun v => μ (i, v)) =
        Φ.coefT y μ c * ∏ j, Φ.t y j ^ (lin W μ (Φ.δ y j)).toNat := fun y μ => by
    rw [Finset.prod_mul_distrib, prod_mono W _ _ (hq y)]; rfl
  refine ⟨f, Φ.ordGe_of_forall fun y hP hm i b hb => ?_, ?_⟩
  · have hsub : ∀ i' : Fin (Φ.m y), i' = i := fun i' => Fin.ext (by have := i'.2; have := i.2; omega)
    by_cases hXy : Subsingleton (Φ.X y)
    · have h0 : φ.evalZ (Φ.δ y i) = 0 := φ.eval_of_subsingleton _
      have hb0 : b = 0 := by
        exact Nat.le_zero.1 (hb 0 (by rw [h0]; simp))
      refine Ideal.mem_sup_left ?_
      simp [hb0]
    rw [not_subsingleton_iff_nontrivial] at hXy
    obtain ⟨x₁, hx₁⟩ := exists_ne (0 : Φ.X y)
    have hpos : ∀ x, x ≠ 0 → 0 < Φ.δ y i x x := fun x hx => by
      obtain ⟨i', hi'⟩ := Φ.pos y x hx
      rwa [hsub i'] at hi'
    obtain ⟨x, hx, hxmin⟩ := leastVal (Φ.δ y i) hpos hx₁
    have hlam0 : (0 : ℝ) ≤ Φ.δ y i x x := by exact_mod_cast (hpos x hx).le
    obtain ⟨h₂, hh₂, hC₂⟩ := hC y hm i x hx
    obtain ⟨j, hj⟩ := pow_le_span (Φ.t_mem y i).1 (Φ.t_mem y i).2 b
    obtain ⟨S, hSo, -, hSa⟩ := hf y j
    rw [Ideal.map_pow] at hSa
    have hSa' := sup_le_sup_right hj _ hSa
    rw [← sub_add_cancel (Φ.ev y f) _]
    refine Ideal.add_mem _ hSa' (Ideal.sum_mem _ fun μ hμ => ?_)
    rw [hT, Fintype.prod_eq_single i (fun i' hi' => absurd (hsub i') hi')]
    refine Ideal.mul_mem_left _ _ ?_
    rcases hterm y _ (Φ.bal y i) (Φ.nonneg y i) _ hlam0 (fun x' hx' => by exact_mod_cast hxmin x' hx') μ (hSo hμ) with
      ⟨g, hg⟩ | hbig
    · refine Ideal.mem_sup_left (Ideal.mem_span_singleton.2 (pow_dvd_pow _ ?_))
      have := hD.le (pull g.toLinearMap (Φ.δ y i)) (pull_mem _ (Φ.bal y i)) (fun x => Φ.nonneg y i _)
      rw [evalZ_pull φ g.surjective] at this
      have e1 : lin W a (pull g.toLinearMap (Φ.δ y i)) = lin W μ (Φ.δ y i) := by
        simp only [lin, qW, ← hg]; simp
      rw [e1] at this
      refine hb _ (this.trans (le_of_eq ?_))
      exact_mod_cast (Int.toNat_of_nonneg (hl y i μ)).symm
    · refine Ideal.mem_sup_right (Ideal.mem_of_dvd _ ?_ (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hh₂) e))
      refine (pow_dvd_pow_of_dvd hC₂ e).trans ?_
      rw [← pow_mul]
      refine pow_dvd_pow _ ?_
      have h3 : ((C * e : ℕ) : ℝ) * (Φ.δ y i x x : ℝ) ≤ (lin W μ (Φ.δ y i) : ℤ) :=
        (mul_le_mul_of_nonneg_right hK1 hlam0).trans hbig
      have h4 : ((C * e : ℕ) : ℤ) * Φ.δ y i x x ≤ lin W μ (Φ.δ y i) := by exact_mod_cast h3
      apply Int.ofNat_le.1
      rw [Int.toNat_of_nonneg (hl y i μ)]
      push_cast at h4 ⊢
      rw [Int.toNat_of_nonneg (hpos x hx).le]
      linarith
  · obtain ⟨S, hSo, hSout, hSa⟩ := hf y₀ (max e ((∑ i, lin W a (Φ.δ y₀ i)).toNat + 1))
    have haorb : a ∈ orbit O N₁ N (k y₀) a :=
      ⟨LinearMap.id, fun c x => ⟨0, by simp⟩, by simp, fun x => ⟨0, by simp⟩, fun i => ⟨0, by simp [hkid]⟩⟩
    have haS : a ∈ S := by
      by_contra hn
      have := hSout a haorb hn
      omega
    have hrem : maximalIdeal (Φ.V y₀) ^ (max e ((∑ i, lin W a (Φ.δ y₀ i)).toNat + 1)) ⊔
        (maximalIdeal A ^ e).map (Φ.ev y₀) ≤ maximalIdeal (Φ.V y₀) ^ e := by
      refine sup_le (Ideal.pow_le_pow_right (le_max_left _ _)) ?_
      rw [Ideal.map_pow]
      haveI := Φ.ev_loc y₀
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit _ _ hx) e
    have hmT : Φ.monoT y₀ a = ∏ j, Φ.t y₀ j ^ (lin W a (Φ.δ y₀ j)).toNat := prod_mono W _ _ (hq y₀) a
    have hSa' := hrem hSa
    simp only [hT] at hSa'
    rw [← Finset.add_sum_erase S _ haS, ← hmT, ← sub_sub] at hSa'
    unfold VSys.Leads
    rw [← sub_add_cancel (Φ.ev y₀ f - Φ.coefT y₀ a c * Φ.monoT y₀ a) _]
    refine Ideal.add_mem _ (Ideal.mem_sup_right hSa') (Ideal.sum_mem _ fun μ hμ => Ideal.mul_mem_left _ _ ?_)
    have hμa := Finset.ne_of_mem_erase hμ
    have hμo := hSo (Finset.mem_of_mem_erase hμ)
    have hnn : ∀ x, 0 ≤ (∑ i, Φ.δ y₀ i) x x := fun x => by
      simp only [LinearMap.sum_apply]; exact Finset.sum_nonneg fun i _ => Φ.nonneg y₀ i x
    rcases hterm y₀ (∑ i, Φ.δ y₀ i) (sum_mem fun i _ => Φ.bal y₀ i) hnn 1 zero_le_one (fun x hx => by
        obtain ⟨i, hi⟩ := Φ.pos y₀ x hx
        have h1 : Φ.δ y₀ i x x ≤ (∑ i, Φ.δ y₀ i) x x := by
          simp only [LinearMap.sum_apply]
          exact Finset.single_le_sum (f := fun i => Φ.δ y₀ i x x) (fun i _ => Φ.nonneg y₀ i x) (Finset.mem_univ i)
        exact_mod_cast (show (1 : ℤ) ≤ _ by omega)) μ hμo with ⟨g, hg⟩ | hbig
    · obtain ⟨γ', -, -, h3, h4⟩ := hμo
      have hcong : ∀ x, CongMod N₁ (g x) x := by
        refine congMod_of_span N₁ g.toLinearMap.toAddMonoidHom a hD.span fun i => ?_
        obtain ⟨t, ht⟩ := hN₁N
        obtain ⟨w, hw⟩ := h4 i
        obtain ⟨w', hw'⟩ := h3 (a i)
        refine ⟨w' + t • w, ?_⟩
        show g (a i) = _
        rw [hg, hw, hkid, LinearMap.id_apply, hw', ht, mul_smul, smul_add]
        abel
      have hμe : (fun i => g (a i)) = μ := funext hg
      have hne : ∃ x, g x ≠ x := by
        by_contra hh
        push_neg at hh
        exact hμa (funext fun i => by rw [← hg, hh])
      obtain ⟨j, hj⟩ := hD.strict g hcong hne
      have hmin := hD.min g hcong
      rw [hμe] at hj hmin
      have hM' : (0 : ℤ) < M := by exact_mod_cast hM
      refine Ideal.mem_sup_left ?_
      rw [hmT]
      refine prod_pow_mem_mul _ _ _ (fun i => Int.toNat_le_toNat ?_) j ?_
      · rw [hδ, lin_smul, lin_smul]
        exact mul_le_mul_of_nonneg_left (hmin i) hM'.le
      · have h5 : lin W a (Φ.δ y₀ j) < lin W μ (Φ.δ y₀ j) := by
          rw [hδ, lin_smul, lin_smul]
          exact mul_lt_mul_of_pos_left hj hM'
        have := hl y₀ j a
        omega
    · refine Ideal.mem_sup_right (Ideal.pow_le_pow_right ?_
        (prod_pow_mem _ _ (fun i => (Φ.t_mem y₀ i).1) _ Finset.univ))
      rw [mul_one, lin_sum] at hbig
      have h4 : (e : ℤ) ≤ ∑ i, lin W μ (Φ.δ y₀ i) := by exact_mod_cast hK2.trans hbig
      apply Int.ofNat_le.1
      rw [Nat.cast_sum]
      exact h4.trans (le_of_eq (Finset.sum_congr rfl fun i _ => (Int.toNat_of_nonneg (hl y₀ i μ)).symm))
