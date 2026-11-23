import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.StarCover

theorem exists_points {X : Type} [AddCommGroup X] {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) :
    ∃ (n : ℕ) (p : Fin n → X × X), ∀ r : Fin m → ℝ,
      (∀ k, ∑ j, r j * (γ j (p k).1 (p k).2 : ℝ) = 0) → ∀ x y, ∑ j, r j * (γ j x y : ℝ) = 0 := by
  classical
  let S : X × X → (Fin m → ℚ) := fun q j => (γ j q.1 q.2 : ℚ)
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℚ (Set.range S)
  obtain ⟨n, f, hf⟩ := (hli.setFinite).fin_embedding
  have hfb : ∀ k, f k ∈ b := fun k => hf ▸ Set.mem_range_self k
  have hpre : ∀ k, ∃ q, S q = f k := fun k => hbS (hfb k)
  let p : Fin n → X × X := fun k => (hpre k).choose
  have hp : ∀ k, S (p k) = f k := fun k => (hpre k).choose_spec
  refine ⟨n, p, fun r hr x y => ?_⟩
  have hmem : S (x, y) ∈ Submodule.span ℚ (Set.range f) := by
    rw [hf, hspan]; exact Submodule.subset_span ⟨(x, y), rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
  have hj : ∀ j, (γ j x y : ℝ) = ∑ k, (c k : ℝ) * (γ j (p k).1 (p k).2 : ℝ) := fun j => by
    have := congrFun hc j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hp, S] at this
    have h2 := congrArg (fun q : ℚ => (q : ℝ)) this
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast] at h2
    exact h2.symm
  calc ∑ j, r j * (γ j x y : ℝ) = ∑ k, (c k : ℝ) * ∑ j, r j * (γ j (p k).1 (p k).2 : ℝ) := by
        simp only [hj, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = 0 := by simp [hr]

end GlobalTheory.StarCover

namespace GlobalTheory.StarCover
open GlobalTheory.MinkWeylReal

theorem dotR_comb {n m : ℕ} (a : Fin n → ℚ) (u : Fin m → Fin n → ℚ) (r : Fin m → ℝ) :
    dotR a (∑ j, r j • castR (u j)) = ∑ j, r j * ((a ⬝ᵥ u j : ℚ) : ℝ) := by
  simp only [dotR, castR, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Rat.cast_sum, Rat.cast_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mem_rcone_image {n m : ℕ} (u : Fin m → Fin n → ℚ) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) :
    ∑ j, r j • castR (u j) ∈ rcone (Finset.univ.image u) := by
  classical
  refine ⟨fun y => ∑ j ∈ Finset.univ.filter (fun j => u j = y), r j,
    fun y _ => Finset.sum_nonneg fun j _ => hr j, ?_⟩
  symm
  refine Finset.sum_image' _ fun j _ => ?_
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]

theorem exists_of_mem_rcone_image {n m : ℕ} (u : Fin m → Fin n → ℚ) (x : Fin n → ℝ)
    (hx : x ∈ rcone (Finset.univ.image u)) :
    ∃ r : Fin m → ℝ, (∀ j, 0 ≤ r j) ∧ x = ∑ j, r j • castR (u j) := by
  classical
  obtain ⟨c, hc, rfl⟩ := hx
  let k : Fin m → ℝ := fun j => ((Finset.univ.filter (fun i => u i = u j)).card : ℝ)
  have hk : ∀ j, 0 < k j := fun j => by
    simp only [k, Nat.cast_pos, Finset.card_pos]
    exact ⟨j, by simp⟩
  refine ⟨fun j => c (u j) / k j, fun j => div_nonneg (hc _ (by simp)) (hk j).le, ?_⟩
  refine Finset.sum_image' _ fun j _ => ?_
  have : ∀ i ∈ Finset.univ.filter (fun i => u i = u j), (c (u i) / k i) • castR (u i) = (c (u j) / k j) • castR (u j) :=
    fun i hi => by
      have hi' := (Finset.mem_filter.mp hi).2
      have hki : k i = k j := by simp only [k, hi']
      rw [hi', hki]
  rw [Finset.sum_congr rfl this, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  change c (u j) = k j * (c (u j) / k j)
  field_simp [(hk j).ne']

end GlobalTheory.StarCover

namespace GlobalTheory.StarCover
open GlobalTheory.MinkWeylReal

theorem toReal_apply' {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (x y : X) :
    toReal β x y = (β x y : ℝ) := by simp [toReal]

theorem comb_apply {X : Type} [AddCommGroup X] {m : ℕ} (r : Fin m → ℝ) (γ : Fin m → LinearMap.BilinForm ℤ X)
    (x y : X) : (∑ j, r j • toReal (γ j)) x y = ∑ j, r j * (γ j x y : ℝ) := by
  simp [LinearMap.sum_apply, toReal_apply']

theorem castR_mem_rcone {n m : ℕ} (u : Fin m → Fin n → ℚ) (j : Fin m) :
    castR (u j) ∈ rcone (Finset.univ.image u) := by
  classical
  refine ⟨fun y => if y = u j then 1 else 0, fun y _ => by dsimp only; split_ifs <;> norm_num, ?_⟩
  simp [ite_smul]

end GlobalTheory.StarCover

namespace GlobalTheory.StarCover
open GlobalTheory.MinkWeylReal

theorem star_cover : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X)
    (v : LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ i y z, γ i y z = γ i z y) → (∀ i y, 0 ≤ γ i y y) →
    v ≠ 0 → InRCone γ v → B ∈ rcone γ → ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
      IsFaceCut γ s h ∧ 0 < h v ∧ B ∈ rcone (Fin.cons v fun j => γ (s j)) := by
  classical
  intro X _ m γ v B hsym hpsd hv0 ⟨c, hc, hvc⟩ ⟨t, ht, hBt⟩
  obtain ⟨n, p, hp⟩ := exists_points γ
  set u : Fin m → Fin n → ℚ := fun j k => (γ j (p k).1 (p k).2 : ℚ) with hu
  set T := Finset.univ.image u with hT
  obtain ⟨A, hA⟩ := minkR T
  have hcomb : ∀ r : Fin m → ℝ, (∑ j, r j • castR (u j)) = fun k => ∑ j, r j * (γ j (p k).1 (p k).2 : ℝ) :=
    fun r => by funext k; simp [castR, u, Finset.sum_apply]
  have hv_app : ∀ x y, (v x y : ℝ) = ∑ j, c j * (γ j x y : ℝ) := fun x y => by
    rw [← toReal_apply', hvc, comb_apply]
  have hB_app : ∀ x y, B x y = ∑ j, t j * (γ j x y : ℝ) := fun x y => by rw [hBt, comb_apply]
  set Ev : Fin n → ℝ := ∑ j, c j • castR (u j) with hEv
  set EB : Fin n → ℝ := ∑ j, t j • castR (u j) with hEB
  have hEvT : Ev ∈ rcone T := mem_rcone_image u c hc
  have hEBT : EB ∈ rcone T := mem_rcone_image u t ht
  have hAv : ∀ a ∈ A, 0 ≤ dotR a Ev := (hA Ev).mp hEvT
  have hAB : ∀ a ∈ A, 0 ≤ dotR a EB := (hA EB).mp hEBT
  have hAu : ∀ a ∈ A, ∀ j, 0 ≤ a ⬝ᵥ u j := fun a ha j => by
    have := (hA _).mp (castR_mem_rcone u j) a ha
    rw [dotR_castR] at this
    exact_mod_cast this

  have hne : (A.filter fun a => 0 < dotR a Ev).Nonempty := by
    by_contra hno
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hno
    have hneg : (-1 : ℝ) • Ev ∈ rcone T := (hA _).mpr fun a ha => by
      rw [dotR_smul]; have := hno ha; push_neg at this; linarith
    obtain ⟨r, hr, hrEq⟩ := exists_of_mem_rcone_image u _ hneg
    have hzero : ∀ x y, ∑ j, (r j + c j) * (γ j x y : ℝ) = 0 := hp _ fun k => by
      have := congrFun hrEq k
      rw [hcomb r, hEv, hcomb c] at this
      simp only [Pi.smul_apply, smul_eq_mul] at this
      simp only [add_mul, Finset.sum_add_distrib]; linarith
    have hvyy : ∀ y, v y y = 0 := fun y => by
      have h1 := hzero y y
      have h2 : ∀ j, 0 ≤ (γ j y y : ℝ) := fun j => by exact_mod_cast hpsd j y
      have h3 : ∑ j, c j * (γ j y y : ℝ) ≤ ∑ j, (r j + c j) * (γ j y y : ℝ) :=
        Finset.sum_le_sum fun j _ => by nlinarith [hr j, h2 j]
      have h4 : 0 ≤ ∑ j, c j * (γ j y y : ℝ) := Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (h2 j)
      have : (v y y : ℝ) = 0 := by rw [hv_app]; linarith
      exact_mod_cast this
    have hvs : ∀ x y, v x y = v y x := fun x y => by
      have : (v x y : ℝ) = v y x := by
        rw [hv_app, hv_app]; exact Finset.sum_congr rfl fun j _ => by rw [hsym j x y]
      exact_mod_cast this
    apply hv0
    refine LinearMap.ext₂ fun x y => ?_
    have := hvyy (x + y)
    simp only [map_add, LinearMap.add_apply, hvyy x, hvyy y, hvs y x] at this
    simp only [LinearMap.zero_apply]; omega
  obtain ⟨a, haF, hamin⟩ := Finset.exists_min_image _ (fun a => dotR a EB / dotR a Ev) hne
  obtain ⟨haA, hapos⟩ := Finset.mem_filter.mp haF
  set ts := dotR a EB / dotR a Ev with hts
  have hts0 : 0 ≤ ts := div_nonneg (hAB a haA) hapos.le
  have hB'T : EB - ts • Ev ∈ rcone T := (hA _).mpr fun a' ha' => by
    rw [dotR_sub, dotR_smul]
    by_cases hpos : 0 < dotR a' Ev
    · have := hamin a' (Finset.mem_filter.mpr ⟨ha', hpos⟩)
      rw [le_div_iff₀ hpos] at this
      linarith
    · push_neg at hpos; nlinarith [hAB a' ha']
  have hB'a : dotR a (EB - ts • Ev) = 0 := by
    rw [dotR_sub, dotR_smul, hts]; field_simp; ring
  obtain ⟨d, hd, hdEq⟩ := exists_of_mem_rcone_image u _ hB'T
  have hdz : ∀ j, d j * ((a ⬝ᵥ u j : ℚ) : ℝ) = 0 := by
    have := hB'a; rw [hdEq, dotR_comb] at this
    exact fun j => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hd j)
      (by exact_mod_cast hAu a haA j))).mp this j (Finset.mem_univ j)
  obtain ⟨N, hN, z, hz⟩ := GordanGenProof.exists_int_multiple a
  let w : (X × X) →₀ ℤ := ∑ k, Finsupp.single (p k) (z k)
  let h := linW w
  have hh : ∀ β : LinearMap.BilinForm ℤ X, h β = ∑ k, z k * β (p k).1 (p k).2 := fun β => by
    simp only [h, linW_apply, w]
    rw [← Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by ring)]
    simp [Finsupp.sum_single_index]
  have hzk : ∀ k, (z k : ℝ) = (N : ℝ) * (a k : ℝ) := fun k => by
    have := congrFun hz k
    simp only [GordanCones.toQ, Pi.smul_apply, smul_eq_mul] at this
    have h2 := congrArg (fun q : ℚ => (q : ℝ)) this
    simpa using h2
  have hhR : ∀ β : LinearMap.BilinForm ℤ X, (h β : ℝ) = N * dotR a (fun k => (β (p k).1 (p k).2 : ℝ)) := fun β => by
    rw [hh]; push_cast; simp only [hzk, dotR, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hhγ : ∀ j, (h (γ j) : ℝ) = N * ((a ⬝ᵥ u j : ℚ) : ℝ) := fun j => by
    rw [hhR, ← dotR_castR]; congr 2
  have hhv : (h v : ℝ) = N * dotR a Ev := by
    rw [hhR]; congr 2; funext k; rw [hEv, hcomb c]; exact hv_app _ _
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set Z := Finset.univ.filter fun j => h (γ j) = 0 with hZ
  let s : Fin Z.card ↪ Fin m := (Z.orderEmbOfFin rfl).toEmbedding
  have hsZ : ∀ j, j ∈ Set.range s ↔ j ∈ Z := fun j => by
    have := Finset.range_orderEmbOfFin Z rfl
    simp only [s, RelEmbedding.coe_toEmbedding]; rw [this]; rfl
  refine ⟨Z.card, s, h, ⟨fun j => ?_, fun j => ?_⟩, ?_, ?_⟩
  · have : (0 : ℝ) ≤ h (γ j) := by rw [hhγ]; exact mul_nonneg hNR.le (by exact_mod_cast hAu a haA j)
    exact_mod_cast this
  · rw [hsZ]; simp [Z]
  · have : (0 : ℝ) < h v := by rw [hhv]; exact mul_pos hNR hapos
    exact_mod_cast this
  · have hdZ : ∀ j, j ∉ Z → d j = 0 := fun j hj => by
      have hne' : h (γ j) ≠ 0 := by simpa [Z] using hj
      have : ((a ⬝ᵥ u j : ℚ) : ℝ) ≠ 0 := fun h0 => hne' (by
        have := hhγ j; rw [h0, mul_zero] at this; exact_mod_cast this)
      exact (mul_eq_zero.mp (hdz j)).resolve_right this
    have hsum : ∀ F : Fin m → (X →ₗ[ℤ] X →ₗ[ℤ] ℝ), ∑ i, d (s i) • F (s i) = ∑ j, d j • F j := fun F => by
      calc ∑ i, d (s i) • F (s i) = ∑ j ∈ Finset.univ.map s, d j • F j := (Finset.sum_map Finset.univ s (fun j => d j • F j)).symm
        _ = ∑ j ∈ Z, d j • F j := by
          congr 1; ext j; rw [← hsZ]; simp
        _ = ∑ j, d j • F j := Finset.sum_subset (Finset.subset_univ Z) (fun j _ hj => by rw [hdZ j hj, zero_smul])
    have hexp : ∀ e : X × X, ∑ j, (t j - ts * c j - d j) * (γ j e.1 e.2 : ℝ) =
        ∑ j, t j * (γ j e.1 e.2 : ℝ) - ts * ∑ j, c j * (γ j e.1 e.2 : ℝ) - ∑ j, d j * (γ j e.1 e.2 : ℝ) := fun e => by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have key : ∀ x y, ∑ j, (t j - ts * c j - d j) * (γ j x y : ℝ) = 0 := hp _ fun k => by
      have := congrFun hdEq k
      rw [hEB, hEv, hcomb, hcomb, hcomb] at this
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [hexp (p k)]; linarith
    refine ⟨Fin.cons ts fun i => d (s i), fun i => Fin.cases hts0 (fun i => hd _) i, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hsum (fun j => toReal (γ j))]
    refine LinearMap.ext₂ fun x y => ?_
    have k1 := key x y
    rw [hexp (x, y)] at k1
    rw [hB_app]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, toReal_apply', hv_app, comb_apply]
    linarith

end GlobalTheory.StarCover

example : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ i y z, γ i y z = γ i z y) → (∀ i y, 0 ≤ γ i y y) → v ≠ 0 → InRCone γ v → B ∈ rcone γ → ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h ∧ 0 < h v ∧ B ∈ rcone (Fin.cons v fun j => γ (s j)) := GlobalTheory.StarCover.star_cover
