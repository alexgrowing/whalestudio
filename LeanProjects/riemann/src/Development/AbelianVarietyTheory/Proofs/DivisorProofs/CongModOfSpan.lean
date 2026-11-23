import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConeInteriorDefiniteBalancedFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruentTupleUnimodularImageOrLargeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadingTermUniqueSupportedBalancedConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLatticeQuadraticSumGeDiagonalStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.LinearValuationCongruences
theorem rho {A K : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [NormedField K] [IsUltrametricDist K]
    (f : A →+* K) (h1 : ∀ h, ‖f h‖ ≤ 1) (h2 : ∀ h ∈ maximalIdeal A, ‖f h‖ < 1) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ h ∈ maximalIdeal A, ‖f h‖ ≤ ρ := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal A) : (maximalIdeal A).FG)
  let F : A → NNReal := fun g => ⟨‖f g‖, norm_nonneg _⟩
  have hmem : ∀ g ∈ s, g ∈ maximalIdeal A := fun g hg => hs ▸ Submodule.subset_span hg
  refine ⟨(s.sup F : NNReal), NNReal.coe_nonneg _, ?_, fun h hh => ?_⟩
  · have : s.sup F < 1 := (Finset.sup_lt_iff (by simp)).2 fun g hg => NNReal.coe_lt_coe.1 (h2 g (hmem g hg))
    exact_mod_cast this
  · rw [← hs] at hh
    induction hh using Submodule.span_induction with
    | mem x hx => exact NNReal.coe_le_coe.2 (Finset.le_sup (f := F) hx)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
    | smul r x _ hx =>
      rw [smul_eq_mul, map_mul, norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (h1 r)).trans hx

theorem linVal {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {d : ℕ} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {r m : ℕ} {γ : Fin r → LinearMap.BilinForm ℤ X} {a : Fin m → X} (hγ : φ.LinearOn γ)
    (hs : Supports bar φ d γ a) {β : LinearMap.BilinForm ℤ X} {k : ℕ} {c : Fin r → ℕ} (hk : 0 < k)
    (hβ : k • β = ∑ j, c j • γ j) : (d : ℝ) * φ.evalZ β = ((∑ i, β (a i) (a i) : ℤ) : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hβR : ∀ x y, (β x y : ℝ) = ∑ j, ((c j : ℝ) / k) * (γ j x y : ℝ) := fun x y => by
    have h0 := LinearMap.congr_fun₂ hβ x y
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] at h0
    have h : (k : ℝ) * β x y = ∑ j, (c j : ℝ) * (γ j x y : ℝ) := by exact_mod_cast h0
    rw [show ∑ j, ((c j : ℝ) / k) * (γ j x y : ℝ) = (∑ j, (c j : ℝ) * γ j x y) / k by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring]
    rw [eq_div_iff hkR.ne', ← h]; ring
  have hev : φ.evalZ β = ∑ j, ((c j : ℝ) / k) * φ.evalZ (γ j) := by
    rw [← hγ _ (fun j => by positivity)]
    show φ.eval X (fun x y => (β x y : ℝ)) = _
    congr 1; funext x y; exact hβR x y
  rw [hev, Finset.mul_sum]
  calc ∑ j, (d : ℝ) * ((c j : ℝ) / k * φ.evalZ (γ j)) = ∑ j, (c j : ℝ) / k * ((d : ℝ) * φ.evalZ (γ j)) :=
        Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j, (c j : ℝ) / k * ∑ i, (γ j (a i) (a i) : ℝ) :=
        Finset.sum_congr rfl fun j _ => by rw [hs.eq j]; push_cast; rfl
    _ = ∑ i, ∑ j, (c j : ℝ) / k * (γ j (a i) (a i) : ℝ) := by simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    _ = _ := by push_cast; exact Finset.sum_congr rfl fun i _ => (hβR _ _).symm

theorem dom {K ι : Type} [NormedField K] [IsUltrametricDist K] (S : Finset ι) (g : ι → K) {a : ι} (ha : a ∈ S)
    (hlt : ∀ μ ∈ S, μ ≠ a → ‖g μ‖ < ‖g a‖) (z : K) (hz : ‖z - ∑ μ ∈ S, g μ‖ < ‖g a‖) : ‖z‖ = ‖g a‖ := by
  classical
  have hpos : 0 < ‖g a‖ := (norm_nonneg _).trans_lt hz
  have hrest : ‖∑ μ ∈ S.erase a, g μ‖ < ‖g a‖ := by
    rcases (S.erase a).eq_empty_or_nonempty with h | h
    · simp [h, hpos]
    · obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image (S.erase a) (fun μ => ‖g μ‖) h
      exact (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) hmax).trans_lt
        (hlt μ (Finset.mem_of_mem_erase hμ) (Finset.ne_of_mem_erase hμ))
  have hsum : ‖∑ μ ∈ S, g μ‖ = ‖g a‖ := by
    rw [← Finset.add_sum_erase S g ha, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hrest.ne',
      max_eq_left hrest.le]
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := z - ∑ μ ∈ S, g μ) (y := ∑ μ ∈ S, g μ)
    (by rw [hsum]; exact hz.ne)
  rw [sub_add_cancel, hsum, max_eq_right hz.le] at this
  exact this

theorem leastVal {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hpos : ∀ x, x ≠ 0 → 0 < β x x) {x₀ : X}
    (hx₀ : x₀ ≠ 0) : ∃ x, x ≠ 0 ∧ ∀ x', x' ≠ 0 → β x x ≤ β x' x' := by
  classical
  have hex : ∃ n : ℕ, ∃ x, x ≠ 0 ∧ β x x = n :=
    ⟨(β x₀ x₀).toNat, x₀, hx₀, (Int.toNat_of_nonneg (hpos x₀ hx₀).le).symm⟩
  obtain ⟨x, hx, hxn⟩ := Nat.find_spec hex
  refine ⟨x, hx, fun x' hx' => ?_⟩
  rw [hxn, ← Int.toNat_of_nonneg (hpos x' hx').le]
  exact_mod_cast Nat.find_min' hex ⟨x', hx', (Int.toNat_of_nonneg (hpos x' hx').le).symm⟩

theorem congMod_of_span {X : Type} [AddCommGroup X] (N : ℕ) (g : X →+ X) {m : ℕ} (a : Fin m → X)
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

theorem qW_single {s : ℕ} (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ) {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (x : X) : qW W β (fun u => if u = 0 then x else 0) = W 0 0 * β x x := by
  unfold qW
  rw [Fintype.sum_eq_single 0 (fun u hu => Fintype.sum_eq_zero _ fun v => by simp [hu])]
  rw [Fintype.sum_eq_single 0 (fun v hv => by simp [hv])]
  simp
end GlobalTheory.Poinc.LinearValuationCongruences

open GlobalTheory.Poinc.LinearValuationCongruences in

theorem GlobalTheory.Poinc.approx_of_fpre : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (bar : O → O), BddAct bar → ∀ (q : ℕ) (φ : InvFun O), IsPolFan bar q φ → ∀ d₀, HasSupports bar q φ d₀ → ∀ (s : ℕ) (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ), PosW W → ∀ (N₁ p : ℕ) [Fact p.Prime], 3 ≤ N₁ → ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (Φ : FPre bar q p A), Φ.abelian₂ → Φ.Four W N₁ → Φ.Approx φ ((W 0 0).toNat * d₀) := by
  intro O _ _ bar hB q φ hφ d₀ hS s W hW N₁ p _ hN₁ A _ _ _ Φ hLam hFour y₀ e
  obtain ⟨cW, hcW0, hcW⟩ := GlobalTheory.T.weightedLatticeQuadraticSum_ge_diagonal (s + 1) W hW
  obtain ⟨C, hC⟩ := hLam
  have hW00 : 0 < W 0 0 := by
    have := hW.diag_pos (i := 0)
    simp at this
    linarith
  have hdcast : (((W 0 0).toNat * d₀ : ℕ) : ℝ) = (W 0 0 : ℝ) * d₀ := by
    rw [Nat.cast_mul]; congr 1; exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg hW00.le)
  have hnn : ∀ y (x : Φ.X y), 0 ≤ Φ.β y x x := fun y x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (Φ.pos y x hx).le
  by_cases hX₀ : Subsingleton (Φ.X y₀)
  · obtain ⟨N, -, -, k, Q, t, -, hk, -⟩ := hFour y₀ 0
    have hsub : ∀ y, Subsingleton (Φ.X y) := fun y => by
      obtain ⟨-, ε, -⟩ := hk y
      exact ε.toEquiv.subsingleton
    have h0 : ∀ y, φ.evalZ (Φ.β y) = 0 := fun y => by
      haveI := hsub y
      exact φ.eval_of_subsingleton _
    refine ⟨1, ?_, fun y => Or.inl ?_⟩
    · simp [h0]
    · simp [h0, Φ.ev_le]
  rw [not_subsingleton_iff_nontrivial] at hX₀
  have hPF := hφ (Φ.X y₀) (Φ.rank_le y₀)
  obtain ⟨r, γ, k₀, c₀, hγ, hk₀, hc₀, hβ₀⟩ :=
    GlobalTheory.T.exists_smoothCone_interior_definite_balancedForm O bar φ (Φ.X y₀) hPF (Φ.β y₀) (Φ.bal y₀) (Φ.pos y₀)
  obtain ⟨m, a₀, hsup⟩ := hS (Φ.X y₀) (Φ.rank_le y₀) r γ hγ
  have hD := linVal hγ.linear hsup hk₀ hβ₀
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = (W 0 0 : ℝ) * ((∑ i, Φ.β y₀ (a₀ i) (a₀ i) : ℤ) : ℝ) := ⟨_, rfl⟩
  have hT' : (((W 0 0).toNat * d₀ : ℕ) : ℝ) * φ.evalZ (Φ.β y₀) = T := by rw [hdcast, mul_assoc, hD, hT]
  obtain ⟨a, ha⟩ : ∃ a : Fin m × Fin (s + 1) → Φ.X y₀, ∀ i u, a (i, u) = if u = 0 then a₀ i else 0 :=
    ⟨fun iu => if iu.2 = 0 then a₀ iu.1 else 0, fun _ _ => rfl⟩
  have ha' : ∀ i, (fun u => a (i, u)) = fun u => if u = 0 then a₀ i else 0 := fun i => funext (ha i)
  have hspan : Submodule.span ℤ (Set.range a) = ⊤ := by
    refine eq_top_iff.2 (hsup.span.symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨i, rfl⟩
    exact ⟨(i, 0), by simp [ha]⟩
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := rho (Φ.ev y₀) (Φ.ev_le y₀) (Φ.ev_lt y₀)
  obtain ⟨E₀, hE₀⟩ : ∃ E : ℝ, E = Real.exp (-(Φ.sc y₀ * T)) := ⟨_, rfl⟩
  have hE₀pos : 0 < E₀ := hE₀ ▸ Real.exp_pos _
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hE₀pos hρ1
  have hsmall : ∀ h ∈ maximalIdeal A, ‖Φ.ev y₀ h‖ ^ (max e n) < E₀ := fun h hh =>
    lt_of_le_of_lt ((pow_le_pow_left₀ (norm_nonneg _) (hρ h hh) _).trans
      (pow_le_pow_of_le_one hρ0 hρ1.le (le_max_right e n))) hn
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max (C * (max e n : ℕ) / cW) ((T + 1) / cW) := ⟨_, rfl⟩
  have hK1 : C * (max e n : ℕ) ≤ cW * K := by
    rw [← div_le_iff₀' hcW0, hK]; exact le_max_left _ _
  have hK2 : T < cW * K := by
    have : (T + 1) / cW ≤ K := hK ▸ le_max_right _ _
    rw [div_le_iff₀' hcW0] at this
    linarith
  obtain ⟨N₀, hN₀⟩ := GlobalTheory.T.congruent_tuple_unimodular_image_or_large O bar hB (Φ.X y₀) (Fin m × Fin (s + 1)) a hspan K
  obtain ⟨N, hNN₀, hN₁N, k, Q, t, hkid, hk, ⟨hTle, hTeq⟩, hfour⟩ := hFour y₀ N₀
  choose c hc using fun i => hTeq y₀ (fun u => a (i, u))
  obtain ⟨f, hf⟩ := hfour m a c (max e n)
  have hterm : ∀ y (lam : ℝ), 0 ≤ lam → (∀ x, x ≠ 0 → lam ≤ Φ.β y x x) → ∀ μ ∈ orbit O N₁ N (k y) a,
      (∃ g : Φ.X y₀ ≃ₗ[O] Φ.X y, (∀ iu, g (a iu) = μ iu) ∧
        ∑ i, (qW W (Φ.β y) (fun u => μ (i, u)) : ℝ) = (W 0 0 : ℝ) * ((∑ i, Φ.β y (g (a₀ i)) (g (a₀ i)) : ℤ) : ℝ) ∧
        (W 0 0 : ℝ) * d₀ * φ.evalZ (Φ.β y) ≤ ∑ i, (qW W (Φ.β y) (fun u => μ (i, u)) : ℝ)) ∨
      cW * K * lam ≤ ∑ i, (qW W (Φ.β y) (fun u => μ (i, u)) : ℝ) := by
    intro y lam hlam0 hlam μ hμ
    obtain ⟨g, g1, g2, -, g4⟩ := hμ
    rcases hN₀ N hNN₀ (Φ.X y) (Φ.β y) (Φ.bal y) (hnn y) lam hlam0 hlam (k y ∘ₗ g) μ (unimod_comp O (hk y) g1 g2)
      (fun i => g4 i) with ⟨g', hg'⟩ | hbig
    · left
      have hμi : ∀ i, (fun u => μ (i, u)) = fun u => if u = 0 then g' (a₀ i) else 0 := fun i => funext fun u => by
        rw [← hg', ha]; by_cases hu : u = 0 <;> simp [hu]
      have hsum : ∑ i, (qW W (Φ.β y) (fun u => μ (i, u)) : ℝ) =
          (W 0 0 : ℝ) * ((∑ i, Φ.β y (g' (a₀ i)) (g' (a₀ i)) : ℤ) : ℝ) := by
        simp only [hμi, qW_single]; push_cast; rw [Finset.mul_sum]
      refine ⟨g', hg', hsum, ?_⟩
      have := hsup.le (pull g'.toLinearMap (Φ.β y)) (pull_mem _ (Φ.bal y)) (fun x => hnn y _)
      rw [evalZ_pull φ g'.surjective] at this
      rw [hsum, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast hW00.le)
      simpa using this
    · right
      calc cW * K * lam ≤ cW * ((∑ iu, Φ.β y (μ iu) (μ iu) : ℤ) : ℝ) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hbig hcW0.le
        _ = ∑ i, cW * ((∑ u, Φ.β y (μ (i, u)) (μ (i, u)) : ℤ) : ℝ) := by
            push_cast; rw [Fintype.sum_prod_type, Finset.mul_sum]
        _ ≤ _ := Finset.sum_le_sum fun i _ => hcW (Φ.X y) (Φ.β y) (Φ.bal y).1 (hnn y) _
  have hnorm : ∀ y (μ : Fin m × Fin (s + 1) → Φ.X y), ‖∏ i, t y (fun u => μ (i, u)) (c i)‖ ≤
      Real.exp (-(Φ.sc y * ∑ i, (qW W (Φ.β y) (fun u => μ (i, u)) : ℝ))) := by
    intro y μ
    rw [norm_prod, Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hTle y _ _
  refine ⟨f, ?_, fun y => ?_⟩
  · obtain ⟨h₁, hh₁, hf₁⟩ := hf y₀
    obtain ⟨S, hSo, hSout, hSa⟩ := hf₁ (E₀ / 2) (by positivity)
    have haorb : a ∈ orbit O N₁ N (k y₀) a :=
      ⟨LinearMap.id, fun c x => ⟨0, by simp⟩, by simp, fun x => ⟨0, by simp⟩, fun i => ⟨0, by simp [hkid]⟩⟩
    have hqa : ∑ i, (qW W (Φ.β y₀) (fun u => a (i, u)) : ℝ) = T := by
      simp only [ha', qW_single]; rw [hT, Int.cast_sum, Finset.mul_sum]; push_cast; rfl
    have hta : ‖∏ i, t y₀ (fun u => a (i, u)) (c i)‖ = E₀ := by
      rw [norm_prod]; simp only [hc]
      rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum, hqa, hE₀]
    have haS : a ∈ S := by
      by_contra hn
      have := hSout a haorb hn
      rw [hqa, ← hE₀] at this
      linarith
    rw [hT', ← hE₀, ← hta]
    refine dom S (fun μ => ∏ i, t y₀ (fun u => μ (i, u)) (c i)) haS (fun μ hμS hμa => ?_) _ ?_
    · rw [hta, hE₀]
      refine (hnorm y₀ μ).trans_lt (Real.exp_lt_exp.2 (neg_lt_neg (mul_lt_mul_of_pos_left ?_ (Φ.sc_pos y₀))))
      have hμo := hSo hμS
      rcases hterm y₀ 1 zero_le_one (fun x hx => by
          have := Φ.pos y₀ x hx; exact_mod_cast (show (1 : ℤ) ≤ _ by omega)) μ hμo with
        ⟨g, hg, hsum, -⟩ | hbig
      · rw [hsum, hT]
        by_contra hle
        push_neg at hle
        have hle' : ((∑ i, Φ.β y₀ (g (a₀ i)) (g (a₀ i)) : ℤ) : ℝ) ≤ ((∑ i, Φ.β y₀ (a₀ i) (a₀ i) : ℤ) : ℝ) :=
          le_of_mul_le_mul_left hle (by exact_mod_cast hW00)
        have hge := hsup.le (pull g.toLinearMap (Φ.β y₀)) (pull_mem _ (Φ.bal y₀)) (fun x => hnn y₀ _)
        rw [evalZ_pull φ g.surjective] at hge
        have heq : (d₀ : ℝ) * φ.evalZ (Φ.β y₀) = ((∑ i, Φ.β y₀ (g (a₀ i)) (g (a₀ i)) : ℤ) : ℝ) := by
          refine le_antisymm (by simpa using hge) ?_
          rw [hD]; exact hle'
        obtain ⟨γ', -, -, h3, h4⟩ := hμo
        have hcong : ∀ x, CongMod N₁ (g x) x := by
          refine congMod_of_span N₁ g.toLinearMap.toAddMonoidHom a₀ hsup.span fun i => ?_
          obtain ⟨t, ht⟩ := hN₁N
          obtain ⟨w, hw⟩ := h4 (i, 0)
          obtain ⟨w', hw'⟩ := h3 (a (i, 0))
          refine ⟨w' + t • w, ?_⟩
          have e1 : g (a₀ i) = μ (i, 0) := by rw [← hg, ha]; simp
          show g (a₀ i) = _
          rw [e1, hw, hkid, LinearMap.id_apply, hw', ht, mul_smul, smul_add]
          simp only [ha, ↓reduceIte]
          abel
        have hid := GlobalTheory.T.leadingTerm_unique_supported_balancedCone O bar φ d₀ (Φ.X y₀) hPF r m γ a₀ hγ hsup (Φ.β y₀) k₀ c₀ hk₀ hc₀ hβ₀ (Φ.pos y₀) g N₁ hN₁
          hcong heq
        exact hμa (funext fun iu => by rw [← hg, hid])
      · linarith
    · rw [hta]
      exact hSa.trans_lt (max_lt (by linarith) (hsmall h₁ hh₁))
  · by_cases hXy : Subsingleton (Φ.X y)
    · left
      have : φ.evalZ (Φ.β y) = 0 := φ.eval_of_subsingleton _
      simp [this, Φ.ev_le]
    rw [not_subsingleton_iff_nontrivial] at hXy
    obtain ⟨x₁, hx₁⟩ := exists_ne (0 : Φ.X y)
    obtain ⟨x, hx, hxmin⟩ := leastVal (Φ.β y) (Φ.pos y) hx₁
    have hlam0 : (0 : ℝ) ≤ Φ.β y x x := by exact_mod_cast (Φ.pos y x hx).le
    obtain ⟨h₂, hh₂, hC₂⟩ := hC y x hx
    obtain ⟨h₁, hh₁, hf₁⟩ := hf y
    obtain ⟨S, hSo, -, hSa⟩ := hf₁ (Real.exp (-(Φ.sc y * ((((W 0 0).toNat * d₀ : ℕ) : ℝ) * φ.evalZ (Φ.β y)))))
      (Real.exp_pos _)
    have hsum : ‖∑ μ ∈ S, ∏ i, t y (fun u => μ (i, u)) (c i)‖ ≤
        max (Real.exp (-(Φ.sc y * ((((W 0 0).toNat * d₀ : ℕ) : ℝ) * φ.evalZ (Φ.β y))))) (‖Φ.ev y h₂‖ ^ (max e n)) := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (le_max_of_le_left (Real.exp_pos _).le)
        fun μ hμ => (hnorm y μ).trans ?_
      rcases hterm y _ hlam0 (fun x' hx' => by exact_mod_cast hxmin x' hx') μ (hSo hμ) with ⟨g, -, -, hle⟩ | hbig
      · refine le_max_of_le_left (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ (Φ.sc_pos y).le)))
        rw [hdcast]; exact hle
      · refine le_max_of_le_right ?_
        have h3 : C * (max e n : ℕ) * (Φ.β y x x : ℝ) ≤ ∑ i, (qW W (Φ.β y) (fun u => μ (i, u)) : ℝ) :=
          (mul_le_mul_of_nonneg_right hK1 hlam0).trans hbig
        have h4 := mul_le_mul_of_nonneg_left h3 (Φ.sc_pos y).le
        calc Real.exp (-(Φ.sc y * ∑ i, (qW W (Φ.β y) (fun u => μ (i, u)) : ℝ)))
            ≤ Real.exp ((max e n : ℕ) * -(C * (Φ.sc y * (Φ.β y x x : ℝ)))) := Real.exp_le_exp.2 (by nlinarith)
          _ = Real.exp (-(C * (Φ.sc y * (Φ.β y x x : ℝ)))) ^ (max e n) := Real.exp_nat_mul _ _
          _ ≤ ‖Φ.ev y h₂‖ ^ (max e n) := pow_le_pow_left₀ (Real.exp_pos _).le hC₂ _
    have hfy := (IsUltrametricDist.norm_add_le_max (Φ.ev y f - ∑ μ ∈ S, ∏ i, t y (fun u => μ (i, u)) (c i))
      (∑ μ ∈ S, ∏ i, t y (fun u => μ (i, u)) (c i))).trans (max_le_max hSa hsum)
    rw [sub_add_cancel] at hfy
    have hpow : ∀ h : A, ‖Φ.ev y h‖ ^ (max e n) ≤ ‖Φ.ev y h‖ ^ e := fun h =>
      pow_le_pow_of_le_one (norm_nonneg _) (Φ.ev_le y h) (le_max_left e n)
    simp only [le_max_iff] at hfy
    rcases hfy with (h | h) | (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨h₁, hh₁, h.trans (hpow h₁)⟩
    · exact Or.inl h
    · exact Or.inr ⟨h₂, hh₂, h.trans (hpow h₂)⟩
