import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private lemma prod_pow_mem {S σ : Type} [CommRing S] (I : Ideal S) (z : σ → S) (hz : ∀ i, z i ∈ I)
    (m : σ →₀ ℕ) {n : ℕ} (hn : n ≤ m.degree) : (m.prod fun i k => z i ^ k) ∈ I ^ n := by
  refine Ideal.pow_le_pow_right hn ?_
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hz i) _

private lemma order_of_mem {K τ : Type} [CommRing K] (n : ℕ) :
    ∀ g ∈ RingHom.ker (constantCoeff : MvPowerSeries τ K →+* K) ^ n, (n : ℕ∞) ≤ g.order := by
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) ?_
    · refine le_trans ?_ le_order_mul
      push_cast
      exact add_le_add (ih a ha) (one_le_order_iff_constCoeff_eq_zero.2 hb)
    · intro a b ha hb
      exact le_trans (le_min ha hb) min_order_le_add

private lemma coeff_map_zero {O K σ τ : Type} [CommRing O] [CommRing K] [Algebra O K] [Fintype σ]
    (ψ : MvPowerSeries σ O →ₐ[O] MvPowerSeries τ K)
    (hψ : ∀ i, constantCoeff (ψ (MvPowerSeries.X i)) = 0) (N : ℕ) (f : MvPowerSeries σ O)
    (hf : ∀ m : σ →₀ ℕ, m.degree < N → coeff m f = 0) (n : τ →₀ ℕ) (hn : n.degree < N) :
    coeff n (ψ f) = 0 := by
  classical
  have key : ∃ μ : Finset (σ →₀ ℕ), (μ : Set _) ⊆ {m : σ →₀ ℕ | N ≤ m.degree} ∧
      ∀ f : MvPowerSeries σ O, (∀ m, m ∉ {m : σ →₀ ℕ | N ≤ m.degree} → coeff m f = 0) →
      ∃ b : (σ →₀ ℕ) → MvPowerSeries σ O, (∀ m, b m ∈ wtPart O (fun _ : σ => (0 : ℤ)) 0) ∧
        f = ∑ m ∈ μ, b m * monomial m 1 :=
    part_span O (MvPowerSeries σ O) ℤ (WPres.free O fun _ : σ => (0 : ℤ))
      {m : σ →₀ ℕ | N ≤ m.degree} 0 (fun (m : σ →₀ ℕ) _ => by
        show Finsupp.weight (fun _ : σ => (0 : ℤ)) m = 0
        simp [Finsupp.weight_apply, Finsupp.sum])
  obtain ⟨μ, hμ, hs⟩ := key
  obtain ⟨b, -, hb⟩ := hs f (fun m hm => hf m (not_le.1 hm))
  have h1 : ψ f ∈ RingHom.ker (constantCoeff : MvPowerSeries τ K →+* K) ^ N := by
    rw [hb, map_sum]
    refine Ideal.sum_mem _ fun m hm => ?_
    have hπ : ψ (monomial m 1) = m.prod fun i k => ψ (MvPowerSeries.X i) ^ k := by
      rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.prod, map_prod]
      simp
    rw [map_mul, hπ]
    exact Ideal.mul_mem_left _ _ (prod_pow_mem _ _ hψ m (hμ hm))
  refine coeff_of_lt_order (lt_of_lt_of_le ?_ (order_of_mem N _ h1))
  exact_mod_cast hn

private lemma homog_ker {O K σ τ X : Type} [CommRing O] [CommRing K] [Algebra O K] [Fintype σ] [AddCommGroup X]
    (w : σ → X) (wt : τ → X) (ψ : MvPowerSeries σ O →ₐ[O] MvPowerSeries τ K)
    (hψ : ∀ i, constantCoeff (ψ (MvPowerSeries.X i)) = 0)
    (hg : ∀ j, ∀ f ∈ wtPart O w j, ψ f ∈ wtPart K wt j) : IsHomog O w (RingHom.ker ψ) := by
  classical
  intro f hf j
  rw [RingHom.mem_ker] at hf ⊢
  ext n
  rw [map_zero]
  by_cases hn : Finsupp.weight wt n = j
  swap
  · exact hg j _ (wcomp_mem O w j f) n hn
  have hfin : {m : σ →₀ ℕ | m.degree ≤ n.degree}.Finite := Finsupp.finite_of_degree_le _
  set T : Finset X := insert j (hfin.toFinset.image (Finsupp.weight w)) with hT
  have h1 := coeff_map_zero ψ hψ (n.degree + 1) (f - ∑ i ∈ T, wcomp O w i f) (fun m hm => by
    have hm' : Finsupp.weight w m ∈ T :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 (Nat.lt_succ_iff.1 hm)))
    rw [map_sub, map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_ite_eq, if_pos hm', sub_self]) n (Nat.lt_succ_self _)
  rw [map_sub, hf, zero_sub, map_neg, neg_eq_zero, map_sum, map_sum,
    Finset.sum_eq_single_of_mem j (Finset.mem_insert_self _ _)] at h1
  · exact h1
  · intro i _ hi
    exact hg i _ (wcomp_mem O w i f) n (fun h => hi (h.symm.trans hn))

theorem UpperTheory.V.Alg.chart_ker :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) (τ : Type) [Fintype τ] (wt : τ → X) (φ : R →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart W.part (W.origin h) wt φ →
      (RingHom.ker φ).IsPrime ∧ IsHomog O W.wt (RingHom.ker (φ.comp W.π)) ∧ RingHom.ker φ ≤ RingHom.ker (W.origin h) ∧
      (∀ D ∈ PtDer (W.origin h) O, ∀ f, φ f = 0 → D f = 0) ∧
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] (p : R →ₐ[O] R') (x' : R' →ₐ[O] O) (φ' : R' →ₐ[O] MvPowerSeries τ (FractionRing O)), Function.Surjective p → x'.comp p = W.origin h → φ'.comp p = φ →
        IsChart (fun j => (W.part j).map p.toLinearMap) x' wt φ' := by
  intro O X R _ _ _ _ _ _ W h τ _ wt φ H
  have hle : ∀ f, φ f = 0 → W.origin h f = 0 := fun f hf => by
    have := H.const f
    rw [hf, map_zero] at this
    exact IsFractionRing.injective O (FractionRing O) (by rw [← this, map_zero])
  haveI : IsDomain (MvPowerSeries τ (FractionRing O)) := NoZeroDivisors.to_isDomain _
  refine ⟨RingHom.ker_isPrime _, ?_, hle, ?_, ?_⟩
  · refine homog_ker W.wt wt _ (fun i => ?_) (fun j f hf => H.graded j _ ⟨f, hf, rfl⟩)
    rw [AlgHom.comp_apply, H.const, W.origin_π]
    simp
  · intro D hD f hf
    obtain ⟨c, hc, hcf⟩ := H.inj f (hle f hf) (fun i => by rw [hf, map_zero])
    have key : ∀ g ∈ RingHom.ker (W.origin h) ^ 2, D g = 0 := by
      intro g hg
      rw [pow_two] at hg
      refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) ?_
      · rw [RingHom.mem_ker] at ha hb
        rw [hD a b, ha, hb, zero_smul, zero_smul, add_zero]
      · intro a b ha hb
        rw [map_add, ha, hb, add_zero]
    have := key _ hcf
    rw [map_smul, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hc
  · intro R' _ _ p x' φ' hp hx hφ
    have hx1 : ∀ f, x' (p f) = W.origin h f := fun f => by rw [← hx]; rfl
    have hφ1 : ∀ f, φ' (p f) = φ f := fun f => by rw [← hφ]; rfl
    refine ⟨?_, fun f => ?_, fun i => ?_, fun f hf hl => ?_⟩
    · rintro j _ ⟨f, hf, rfl⟩
      show φ' (p f) ∈ _
      rw [hφ1]
      exact H.graded j f hf
    · obtain ⟨f, rfl⟩ := hp f
      rw [hφ1, hx1, H.const]
    · obtain ⟨f, hf⟩ := H.onto i
      exact ⟨p f, by rw [hφ1]; exact hf⟩
    · obtain ⟨f, rfl⟩ := hp f
      rw [hx1] at hf
      rw [hφ1] at hl
      obtain ⟨c, hc, hcf⟩ := H.inj f hf hl
      refine ⟨c, hc, ?_⟩
      rw [← map_smul]
      have h1 : RingHom.ker (W.origin h) ≤ (RingHom.ker x').comap p := fun g hg => by
        rw [Ideal.mem_comap, RingHom.mem_ker, hx1]
        exact hg
      exact Ideal.le_comap_pow (K := RingHom.ker x') p 2 (Ideal.pow_right_mono h1 2 hcf)
