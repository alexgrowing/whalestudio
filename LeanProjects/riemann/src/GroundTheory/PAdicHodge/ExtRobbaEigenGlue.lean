import Mathlib
import GroundTheory.PAdicHodge.ExistsWeightLeOfConvergesAt
import GroundTheory.PAdicHodge.ExtRobbaDMSplit
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

def lowerPart (b : T.B) : T.B :=
  algebraMap Γ T.B (T.partialSum (T.num b) (T.den b)) * IsLocalization.Away.invSelf T.π ^ T.den b

def upperPart (b : T.B) : T.B :=
  algebraMap Γ T.B (T.num b - T.partialSum (T.num b) (T.den b)) *
    IsLocalization.Away.invSelf T.π ^ T.den b

theorem lowerPart_add_upperPart (b : T.B) : T.lowerPart b + T.upperPart b = b := by
  rw [lowerPart, upperPart, ← add_mul, ← map_add, add_sub_cancel, ← T.eq_num_mul]

theorem coeffB_lowerPart (b : T.B) (n : ℤ) :
    T.coeffB (T.lowerPart b) n = if n < 0 then T.coeffB b n else 0 := by
  rw [lowerPart, T.coeffB_eq (T.mul_pow_eq_of_invSelf _), T.coeffB_eq (T.num_spec b)]
  simp only
  rcases lt_or_ge (n + T.den b) 0 with h | h
  · rw [T.zcoeff_of_neg _ h, T.zcoeff_of_neg _ h]; simp
  · lift n + T.den b to ℕ using h with k hk
    rw [zcoeff_natCast, zcoeff_natCast, partialSum, coeff_finSum]
    by_cases hn : n < 0
    · rw [if_pos (by omega), if_pos hn]
    · rw [if_neg (by omega), if_neg hn]

theorem coeffB_upperPart (b : T.B) (n : ℤ) :
    T.coeffB (T.upperPart b) n = if n < 0 then 0 else T.coeffB b n := by
  rw [upperPart, T.coeffB_eq (T.mul_pow_eq_of_invSelf _), T.coeffB_eq (T.num_spec b)]
  simp only
  rcases lt_or_ge (n + T.den b) 0 with h | h
  · rw [T.zcoeff_of_neg _ h, T.zcoeff_of_neg _ h]; simp
  · lift n + T.den b to ℕ using h with k hk
    rw [zcoeff_natCast, zcoeff_natCast, coeff_sub_partialSum]
    by_cases hn : n < 0
    · rw [if_pos (by omega), if_pos hn]
    · rw [if_neg (by omega), if_neg hn]

theorem norm_coeffB_lowerPart_le (b : T.B) (n : ℤ) :
    ‖T.coeffB (T.lowerPart b) n‖ ≤ ‖T.coeffB b n‖ := by
  rw [coeffB_lowerPart]; split_ifs <;> simp

theorem norm_coeffB_upperPart_le (b : T.B) (n : ℤ) :
    ‖T.coeffB (T.upperPart b) n‖ ≤ ‖T.coeffB b n‖ := by
  rw [coeffB_upperPart]; split_ifs <;> simp

variable {T}

theorem ConvAll.lowerPart {b : T.B} (hb : T.ConvAll b) : T.ConvAll (T.lowerPart b) :=
  fun ρ h0 h1 => (convergesAt_of_norm_le h0 (T.norm_coeffB_lowerPart_le b) (hb ρ h0 h1)).1

theorem ConvAll.upperPart {b : T.B} (hb : T.ConvAll b) : T.ConvAll (T.upperPart b) :=
  fun ρ h0 h1 => (convergesAt_of_norm_le h0 (T.norm_coeffB_upperPart_le b) (hb ρ h0 h1)).1

theorem gaussNorm_lowerPart_le {b : T.B} (hb : T.ConvAll b) {r r' : ℝ} (h0 : 0 < r')
    (hle : r' ≤ r) (h1 : r' < 1) :
    gaussNorm (T.coeffB (T.lowerPart b)) r ≤ gaussNorm (T.coeffB b) r' := by
  refine gaussNorm_le fun n => ?_
  rw [coeffB_lowerPart]
  split_ifs with hn
  · have h3 : r ^ n ≤ r' ^ n := by
      rw [show r ^ n = (r ^ (-n))⁻¹ by rw [zpow_neg, inv_inv],
        show r' ^ n = (r' ^ (-n))⁻¹ by rw [zpow_neg, inv_inv]]
      exact inv_anti₀ (by positivity) (zpow_le_zpow_left₀ (by omega) h0.le hle)
    exact (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans ((hb r' h0 h1).le_gaussNorm n)
  · rw [norm_zero, zero_mul]; exact gaussNorm_nonneg h0

theorem gaussNorm_upperPart_le {b : T.B} (hb : T.ConvAll b) {r r' : ℝ} (h0 : 0 < r)
    (hle : r ≤ r') (h1 : r' < 1) :
    gaussNorm (T.coeffB (T.upperPart b)) r ≤ gaussNorm (T.coeffB b) r' := by
  refine gaussNorm_le fun n => ?_
  rw [coeffB_upperPart]
  split_ifs with hn
  · rw [norm_zero, zero_mul]; exact gaussNorm_nonneg (h0.trans_le hle)
  · exact (mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ (by omega) h0.le hle)
      (norm_nonneg _)).trans ((hb r' (h0.trans_le hle) h1).le_gaussNorm n)

end TeichLift

end GroundTheory.PAdicHodge

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem extNorm_add_add_le_max {σ : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) σ) (a b c : T.RobbaExt σ) :
    T.extNorm σ ρ (a + b + c) ≤ max (T.extNorm σ ρ a) (max (T.extNorm σ ρ b) (T.extNorm σ ρ c)) :=
  (T.extNorm_add_le ρ _ _).trans (max_le ((T.extNorm_add_le ρ _ _).trans
    (max_le_max le_rfl (le_max_left _ _))) (le_max_of_le_right (le_max_right _ _)))

theorem gaussNorm_ofAll_sub {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b)
    {σ : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) σ) :
    gaussNorm (T.coeffB (a - b)) ρ = T.extNorm σ ρ (T.ofAll a ha σ - T.ofAll b hb σ) := by
  rw [← ofAll_sub ha hb, extNorm_ofAll]

theorem exists_mem_annulus (r : ℕ → Set.Ioo (0 : ℝ) 1) (hr0 : Tendsto (fun t => (r t : ℝ)) atTop (𝓝 0))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ r 0) : ∃ s, (r (s + 1) : ℝ) ≤ ρ ∧ ρ ≤ r s := by
  classical
  have hex : ∃ t, (r (t + 1) : ℝ) < ρ := by
    have := ((tendsto_add_atTop_iff_nat 1).2 hr0).eventually (gt_mem_nhds hρ0)
    exact this.exists
  refine ⟨Nat.find hex, (Nat.find_spec hex).le, ?_⟩
  rcases h : Nat.find hex with _ | s
  · exact hρ
  · have := Nat.find_min hex (show s < Nat.find hex by omega)
    exact not_lt.1 this

theorem exists_glue (r : ℕ → Set.Ioo (0 : ℝ) 1) (hr : ∀ t, (r (t + 1) : ℝ) ≤ r t)
    (hr0 : Tendsto (fun t => (r t : ℝ)) atTop (𝓝 0)) (x : (t : ℕ) → ℕ → T.RobbaExt (r t))
    (hC : ∀ t, ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ K ≥ J₀,
      T.extNorm (r t) (topRad (r t)) (x t J - x t K) ≤ ε ∧
      T.extNorm (r t) ⟨r (t + 1), (r (t + 1)).2.1, hr t⟩ (x t J - x t K) ≤ ε)
    (hD : ∀ t, ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀,
      T.extNorm (r (t + 1)) (topRad (r (t + 1))) (T.res (hr t) (x t J) - x (t + 1) J) ≤ ε) :
    ∃ g : T.RobbaExt (r 0), ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀,
      T.extNorm (r 0) (topRad (r 0)) (g - x 0 J) ≤ ε ∧
      T.extNorm (r 0) ⟨r 1, (r 1).2.1, hr 0⟩ (g - x 0 J) ≤ ε := by
  have hanti : Antitone fun t => (r t : ℝ) := antitone_nat_of_succ_le hr
  have hhalf : ∀ J : ℕ, (0 : ℝ) < (1 / 2) ^ J := fun J => by positivity
  have hhalf_le : ∀ ε > (0 : ℝ), ∃ J₀ : ℕ, ∀ J ≥ J₀, ((1 : ℝ) / 2) ^ J ≤ ε := by
    intro ε hε
    obtain ⟨J₀, hJ₀⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨J₀, fun J hJ => (pow_le_pow_of_le_one (by norm_num) (by norm_num) hJ).trans hJ₀.le⟩

  choose d hdc hdx using fun (t J : ℕ) =>
    exists_approx_convAll (x t J) (⟨r (t + 1), (r (t + 1)).2.1, hr t⟩ : Set.Ioc (0 : ℝ) (r t))
      (hhalf J)

  have hdC : ∀ t, ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ K ≥ J₀, ∀ ρ : Set.Ioc (0 : ℝ) (r t),
      (r (t + 1) : ℝ) ≤ ρ → gaussNorm (T.coeffB (d t J - d t K)) ρ ≤ ε := by
    intro t ε hε
    obtain ⟨J₁, hJ₁⟩ := hC t ε hε
    obtain ⟨J₂, hJ₂⟩ := hhalf_le ε hε
    refine ⟨max J₁ J₂, fun J hJ K hK ρ hρ => ?_⟩
    rw [gaussNorm_ofAll_sub (hdc t J) (hdc t K)]
    have e : T.ofAll (d t J) (hdc t J) (r t) - T.ofAll (d t K) (hdc t K) (r t) =
        -(x t J - T.ofAll (d t J) (hdc t J) (r t)) + (x t J - x t K) +
          (x t K - T.ofAll (d t K) (hdc t K) (r t)) := by ring
    rw [e]
    refine (extNorm_add_add_le_max ρ _ _ _).trans (max_le ?_ (max_le ?_ ?_))
    · rw [extNorm_neg]; exact (hdx t J ρ hρ).trans (hJ₂ J (le_of_max_le_right hJ))
    · obtain ⟨h1, h2⟩ := hJ₁ J (le_of_max_le_left hJ) K (le_of_max_le_left hK)
      exact (T.extNorm_le_max _ (topRad (r t)) ρ hρ ρ.2.2 _).trans (max_le h2 h1)
    · exact (hdx t K ρ hρ).trans (hJ₂ K (le_of_max_le_right hK))

  set δ : ℕ → ℕ → T.B := fun t J => d t J - d (t + 1) J with hδdef
  have hδc : ∀ t J, T.ConvAll (δ t J) := fun t J => (hdc t J).sub (hdc (t + 1) J)
  have hδ : ∀ t, ∀ ε > 0, ∀ᶠ J in atTop, gaussNorm (T.coeffB (δ t J)) (r (t + 1)) ≤ ε := by
    intro t ε hε
    obtain ⟨J₁, hJ₁⟩ := hD t ε hε
    obtain ⟨J₂, hJ₂⟩ := hhalf_le ε hε
    refine eventually_atTop.2 ⟨max J₁ J₂, fun J hJ => ?_⟩
    rw [show (r (t + 1) : ℝ) = ((topRad (r (t + 1)) : Set.Ioc (0 : ℝ) (r (t + 1))) : ℝ) from rfl,
      gaussNorm_ofAll_sub (hdc t J) (hdc (t + 1) J)]
    have e : T.ofAll (d t J) (hdc t J) (r (t + 1)) - T.ofAll (d (t + 1) J) (hdc (t + 1) J) (r (t + 1)) =
        -T.res (hr t) (x t J - T.ofAll (d t J) (hdc t J) (r t)) +
          (T.res (hr t) (x t J) - x (t + 1) J) +
          (x (t + 1) J - T.ofAll (d (t + 1) J) (hdc (t + 1) J) (r (t + 1))) := by
      rw [map_sub, res_ofAll]; ring
    rw [e]
    refine (extNorm_add_add_le_max _ _ _ _).trans (max_le ?_ (max_le (hJ₁ J (le_of_max_le_left hJ)) ?_))
    · rw [extNorm_neg, extNorm_res]
      exact (hdx t J _ le_rfl).trans (hJ₂ J (le_of_max_le_right hJ))
    · exact (hdx (t + 1) J _ (hr (t + 1))).trans (hJ₂ J (le_of_max_le_right hJ))

  have hsel : ∀ k : ℕ, ∃ J, k ≤ J ∧ ∀ t < k, gaussNorm (T.coeffB (δ t J)) (r (t + 1)) ≤ (1 / 2) ^ k := by
    intro k
    have h1 : ∀ᶠ J in atTop, ∀ t ∈ Finset.range k,
        gaussNorm (T.coeffB (δ t J)) (r (t + 1)) ≤ (1 / 2) ^ k :=
      (Finset.range k).eventually_all.2 fun t _ => hδ t _ (hhalf k)
    obtain ⟨J, hJ1, hJ2⟩ := ((eventually_ge_atTop k).and h1).exists
    exact ⟨J, hJ1, fun t ht => hJ2 t (Finset.mem_range.2 ht)⟩
  choose Jk hJk hJδ using hsel

  set G : ℕ → T.B := fun k => d 0 (Jk k) - ∑ t ∈ Finset.range k, T.lowerPart (δ t (Jk k)) with hGdef
  have hGc : ∀ k, T.ConvAll (G k) := fun k =>
    (hdc 0 (Jk k)).sub (convAll_sum _ _ fun t _ => (hδc t (Jk k)).lowerPart)
  have hkey : ∀ s k, s ≤ k → ∀ ρ : ℝ, (r (s + 1) : ℝ) ≤ ρ → ρ ≤ r s →
      gaussNorm (T.coeffB (G k - d s (Jk k))) ρ ≤ (1 / 2) ^ k := by
    intro s k hsk ρ hρ1 hρ2
    set J := Jk k
    have hρ0 : 0 < ρ := (r (s + 1)).2.1.trans_le hρ1
    have hρ1' : ρ < 1 := hρ2.trans_lt (r s).2.2
    have h1 : ∑ t ∈ Finset.range s, δ t J = d 0 J - d s J :=
      Finset.sum_range_sub' (fun t => d t J) s
    have h2 := Finset.sum_range_add_sum_Ico (fun t => T.lowerPart (δ t J)) hsk
    have h3 : ∀ t, T.upperPart (δ t J) = δ t J - T.lowerPart (δ t J) := fun t =>
      eq_sub_of_add_eq' (T.lowerPart_add_upperPart _)
    have e : G k - d s J = ∑ t ∈ Finset.range s, T.upperPart (δ t J) -
        ∑ t ∈ Finset.Ico s k, T.lowerPart (δ t J) := by
      rw [Finset.sum_congr rfl (fun t _ => h3 t), Finset.sum_sub_distrib, h1, hGdef]
      simp only
      rw [← h2]; ring
    rw [e, sub_eq_add_neg]
    have hU := T.gaussNorm_finsetSum_le (Finset.range s) (fun t => T.upperPart (δ t J)) hρ0 hρ1'
      (hhalf k).le fun t ht => by
        have ht' := Finset.mem_range.1 ht
        refine ⟨(hδc t J).upperPart ρ hρ0 hρ1', ?_⟩
        have hle : ρ ≤ r (t + 1) := hρ2.trans (hanti (show t + 1 ≤ s by omega))
        exact (gaussNorm_upperPart_le (hδc t J) hρ0 hle (r (t + 1)).2.2).trans
          (hJδ k t (by omega))
    have hL := T.gaussNorm_finsetSum_le (Finset.Ico s k) (fun t => T.lowerPart (δ t J)) hρ0 hρ1'
      (hhalf k).le fun t ht => by
        have ht' := Finset.mem_Ico.1 ht
        refine ⟨(hδc t J).lowerPart ρ hρ0 hρ1', ?_⟩
        have hle : (r (t + 1) : ℝ) ≤ ρ := (hanti (show s + 1 ≤ t + 1 by omega)).trans hρ1
        exact (gaussNorm_lowerPart_le (hδc t J) (r (t + 1)).2.1 hle (r (t + 1)).2.2).trans
          (hJδ k t ht'.2)
    obtain ⟨hLn1, hLn2⟩ := T.convergesAt_coeffB_neg hρ0 hρ1' hL.1
    refine (T.convergesAt_coeffB_add hρ0 hρ1' hU.1 hLn1).2.trans (max_le hU.2 ?_)
    rw [hLn2]; exact hL.2

  have hGC : ∀ ρ : Set.Ioc (0 : ℝ) (r 0), ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      gaussNorm (T.coeffB (G m - G n)) ρ < ε := by
    intro ρ ε hε
    obtain ⟨s, hs1, hs2⟩ := exists_mem_annulus r hr0 ρ.2.1 ρ.2.2
    obtain ⟨J₁, hJ₁⟩ := hdC s (ε / 2) (half_pos hε)
    obtain ⟨J₂, hJ₂⟩ := hhalf_le (ε / 2) (half_pos hε)
    refine ⟨max s (max J₁ J₂), fun m hm n hn => ?_⟩
    have hρ0 : (0 : ℝ) < ρ := ρ.2.1
    have hρ1 : (ρ : ℝ) < 1 := rad_lt_one (r 0) ρ
    have e : G m - G n = (G m - d s (Jk m)) + (d s (Jk m) - d s (Jk n)) + -(G n - d s (Jk n)) := by
      ring
    have c1 := hkey s m (le_of_max_le_left hm) ρ hs1 hs2
    have c2 := hkey s n (le_of_max_le_left hn) ρ hs1 hs2
    have hmJ : J₁ ≤ Jk m := (le_of_max_le_left (le_of_max_le_right hm)).trans (hJk m)
    have hnJ : J₁ ≤ Jk n := (le_of_max_le_left (le_of_max_le_right hn)).trans (hJk n)
    have c4 := hJ₁ (Jk m) hmJ (Jk n) hnJ ⟨ρ, ρ.2.1, hs2⟩ hs1
    have hm2 := hJ₂ m (le_of_max_le_right (le_of_max_le_right hm))
    have hn2 := hJ₂ n (le_of_max_le_right (le_of_max_le_right hn))
    have cv : ∀ b : T.B, T.ConvAll b → ConvergesAt (T.coeffB b) ρ := fun b hb => hb ρ hρ0 hρ1
    have hA := T.convergesAt_coeffB_add hρ0 hρ1 (cv (G m - d s (Jk m)) ((hGc m).sub (hdc s _)))
      (cv (d s (Jk m) - d s (Jk n)) ((hdc s _).sub (hdc s _)))
    obtain ⟨hN1, hN2⟩ := T.convergesAt_coeffB_neg hρ0 hρ1 (cv (G n - d s (Jk n)) ((hGc n).sub (hdc s _)))
    have hB := T.convergesAt_coeffB_add hρ0 hρ1 hA.1 hN1
    rw [e]
    refine lt_of_le_of_lt (hB.2.trans (max_le (hA.2.trans (max_le (c1.trans hm2) c4)) ?_))
      (half_lt_self hε)
    rw [hN2]; exact c2.trans hn2
  obtain ⟨g, hg⟩ := exists_tendsto_of_gaussNorm (T := T) (σ := r 0)
    (fun k => ⟨G k, hGc k (r 0) (r 0).2.1 (r 0).2.2⟩) hGC
  refine ⟨g, fun ε hε => ?_⟩

  have hgk : ∀ ρ : Set.Ioc (0 : ℝ) (r 0), ∀ᶠ k in atTop,
      T.extNorm (r 0) ρ (g - T.ofAll (G k) (hGc k) (r 0)) ≤ ε := by
    intro ρ
    have h1 : Tendsto (fun k => T.extNorm (r 0) ρ (g - T.ofAll (G k) (hGc k) (r 0))) atTop
        (𝓝 (T.extNorm (r 0) ρ (g - g))) :=
      ((T.continuous_extNorm ρ).tendsto _).comp (tendsto_const_nhds.sub hg)
    rw [sub_self, extNorm_zero] at h1
    exact h1.eventually (ge_mem_nhds hε)
  obtain ⟨J₁, hJ₁⟩ := hdC 0 ε hε
  obtain ⟨J₂, hJ₂⟩ := hhalf_le ε hε
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ((eventually_ge_atTop J₁).and ((eventually_ge_atTop J₂).and
    ((hgk (topRad (r 0))).and (hgk ⟨r 1, (r 1).2.1, hr 0⟩)))).exists
  have hbound : ∀ ρ : Set.Ioc (0 : ℝ) (r 0), (r 1 : ℝ) ≤ ρ →
      T.extNorm (r 0) ρ (g - T.ofAll (G k) (hGc k) (r 0)) ≤ ε →
      ∀ J ≥ max J₁ J₂, T.extNorm (r 0) ρ (g - x 0 J) ≤ ε := by
    intro ρ hρ hgρ J hJ
    have e : g - x 0 J = (g - T.ofAll (G k) (hGc k) (r 0)) +
        (T.ofAll (G k - d 0 (Jk k) + (d 0 (Jk k) - d 0 J)) (((hGc k).sub (hdc 0 _)).add
          ((hdc 0 _).sub (hdc 0 J))) (r 0)) + -(x 0 J - T.ofAll (d 0 J) (hdc 0 J) (r 0)) := by
      rw [ofAll_add ((hGc k).sub (hdc 0 _)) ((hdc 0 _).sub (hdc 0 J)), ofAll_sub (hGc k) (hdc 0 _),
        ofAll_sub (hdc 0 _) (hdc 0 J)]; ring
    rw [e]
    refine (extNorm_add_add_le_max ρ _ _ _).trans (max_le hgρ (max_le ?_ ?_))
    · rw [extNorm_ofAll]
      have hρ0 : (0 : ℝ) < ρ := ρ.2.1
      have hρ1 : (ρ : ℝ) < 1 := rad_lt_one (r 0) ρ
      refine (T.convergesAt_coeffB_add hρ0 hρ1 (((hGc k).sub (hdc 0 _)) ρ hρ0 hρ1)
        (((hdc 0 _).sub (hdc 0 J)) ρ hρ0 hρ1)).2.trans (max_le ?_ ?_)
      · exact (hkey 0 k (Nat.zero_le _) ρ hρ ρ.2.2).trans (hJ₂ k hk2)
      · exact hJ₁ (Jk k) (hk1.trans (hJk k)) J (le_of_max_le_left hJ) ρ hρ
    · rw [extNorm_neg]; exact (hdx 0 J ρ hρ).trans (hJ₂ J (le_of_max_le_right hJ))
  exact ⟨max J₁ J₂, fun J hJ => ⟨hbound _ (hr 0) hk3 J hJ, hbound _ le_rfl hk4 J hJ⟩⟩

end TeichLift

end GroundTheory.PAdicHodge

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

section Dense

theorem exists_norm_mem_Ioo_of_perfect (p : ℕ) [hp : Fact p.Prime] {L : Type*}
    [NontriviallyNormedField L] [CharP L p] [PerfectRing L p] {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∃ c : L, α < ‖c‖ ∧ ‖c‖ < β := by
  have hβ : 0 < β := hα.trans hαβ
  obtain ⟨t, ht0, ht1⟩ := NormedField.exists_norm_lt_one L
  have hr0 : 0 < α / β := div_pos hα hβ
  have hr1 : α / β < 1 := (div_lt_one hβ).2 hαβ
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one ht0 hr1
  set s : L := (iterateFrobeniusEquiv L p m).symm t
  have hs : s ^ p ^ m = t := by
    rw [← iterateFrobeniusEquiv_def]; exact RingEquiv.apply_symm_apply _ _
  have hsn : ‖s‖ ^ p ^ m = ‖t‖ := by rw [← norm_pow, hs]
  have hpm : m ≤ p ^ m := (Nat.lt_pow_self hp.out.one_lt).le
  have hγ1 : ‖s‖ < 1 := by
    by_contra h
    have := one_le_pow₀ (n := p ^ m) (not_lt.1 h)
    linarith
  have hγ0 : 0 < ‖s‖ := by
    rcases (norm_nonneg s).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_pow (pow_ne_zero _ hp.out.ne_zero)] at hsn; linarith
  have hγ : α / β < ‖s‖ := by
    have h1 : (α / β) ^ p ^ m < ‖s‖ ^ p ^ m := by
      rw [hsn]; exact (pow_le_pow_of_le_one hr0.le hr1.le hpm).trans_lt hm
    exact lt_of_pow_lt_pow_left₀ _ (norm_nonneg _) h1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hβ (one_lt_inv₀ hγ0 |>.2 hγ1)
  refine ⟨s⁻¹ ^ n, ?_, ?_⟩
  · rw [norm_zpow, norm_inv]
    have e : ‖s‖⁻¹ ^ n = ‖s‖ * ‖s‖⁻¹ ^ (n + 1) := by
      rw [zpow_add_one₀ (inv_ne_zero hγ0.ne'), mul_comm (‖s‖⁻¹ ^ n), ← mul_assoc,
        mul_inv_cancel₀ hγ0.ne', one_mul]
    rw [e]
    calc α = α / β * β := by field_simp
      _ < ‖s‖ * β := mul_lt_mul_of_pos_right hγ hβ
      _ ≤ ‖s‖ * ‖s‖⁻¹ ^ (n + 1) := mul_le_mul_of_nonneg_left hn2 hγ0.le
  · rw [norm_zpow, norm_inv]; exact hn1

end Dense

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem extNorm_sum_le {σ : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) σ) {ι : Type*} (s : Finset ι)
    (f : ι → T.RobbaExt σ) {M : ℝ} (hM : 0 ≤ M) (h : ∀ i ∈ s, T.extNorm σ ρ (f i) ≤ M) :
    T.extNorm σ ρ (∑ i ∈ s, f i) ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, extNorm_zero]; exact hM
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (T.extNorm_add_le ρ _ _).trans (max_le (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))

namespace TeichFrob

variable (F : T.TeichFrob)

theorem continuous_extFrobSymm (τ : Set.Ioo (0 : ℝ) 1) : Continuous (F.extFrobSymm τ) :=
  Completion.continuous_map

def powRad {σ : Set.Ioo (0 : ℝ) 1} (r : Set.Ioc (0 : ℝ) σ) : Set.Ioc (0 : ℝ) (F.powRadius σ) :=
  ⟨(r : ℝ) ^ p ^ F.a, pow_pos r.2.1 _, pow_le_pow_left₀ r.2.1.le r.2.2 _⟩

@[simp] theorem coe_powRad {σ : Set.Ioo (0 : ℝ) 1} (r : Set.Ioc (0 : ℝ) σ) :
    ((F.powRad r : Set.Ioc (0 : ℝ) (F.powRadius σ)) : ℝ) = (r : ℝ) ^ p ^ F.a := rfl

theorem extNorm_extFrob (σ : Set.Ioo (0 : ℝ) 1) (r : Set.Ioc (0 : ℝ) σ) (x : T.RobbaExt σ) :
    T.extNorm (F.powRadius σ) (F.powRad r) (F.extFrob σ x) = T.extNorm σ r x ^ p ^ F.a := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((T.continuous_extNorm _).comp (F.continuous_extFrob σ))
      ((T.continuous_extNorm r).pow _)
  | ih b =>
    rw [F.extFrob_coe, extNorm_coe, extNorm_coe, coe_econFrob, coe_powRad]
    exact F.gaussNorm_coeffB_toB r.2.1 (rad_lt_one σ r) (T.convergesAt_rad σ b r)

def powRadRoot {τ : Set.Ioo (0 : ℝ) 1} (r : Set.Ioc (0 : ℝ) (F.rootRadius τ)) : Set.Ioc (0 : ℝ) τ :=
  ⟨(r : ℝ) ^ p ^ F.a, pow_pos r.2.1 _, by
    have h := pow_le_pow_left₀ r.2.1.le r.2.2 (p ^ F.a)
    have e : ((F.rootRadius τ : Set.Ioo (0 : ℝ) 1) : ℝ) ^ p ^ F.a = τ :=
      congrArg Subtype.val (F.powRadius_rootRadius τ)
    exact h.trans e.le⟩

@[simp] theorem coe_powRadRoot {τ : Set.Ioo (0 : ℝ) 1} (r : Set.Ioc (0 : ℝ) (F.rootRadius τ)) :
    ((F.powRadRoot r : Set.Ioc (0 : ℝ) τ) : ℝ) = (r : ℝ) ^ p ^ F.a := rfl

theorem extNorm_extFrobSymm (τ : Set.Ioo (0 : ℝ) 1) (r : Set.Ioc (0 : ℝ) (F.rootRadius τ))
    (x : T.RobbaExt τ) :
    T.extNorm (F.rootRadius τ) r (F.extFrobSymm τ x) ^ p ^ F.a = T.extNorm τ (F.powRadRoot r) x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq (((T.continuous_extNorm r).comp (F.continuous_extFrobSymm τ)).pow _)
      (T.continuous_extNorm _)
  | ih b =>
    rw [F.extFrobSymm_coe, extNorm_coe, extNorm_coe, coe_econFrobSymm, coe_powRadRoot]
    have hc := T.convergesAt_rad _ (F.econFrobSymm τ b) r
    rw [coe_econFrobSymm] at hc
    have := F.gaussNorm_coeffB_toB r.2.1 (rad_lt_one _ r) hc
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm

theorem extFrob_res_extFrobSymm {τ σ : Set.Ioo (0 : ℝ) 1} (h : (σ : ℝ) ≤ F.rootRadius τ)
    (h' : ((F.powRadius σ : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ τ) (x : T.RobbaExt τ) :
    F.extFrob σ (T.res h (F.extFrobSymm τ x)) = T.res h' x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((F.continuous_extFrob σ).comp ((T.continuous_res h).comp
      (F.continuous_extFrobSymm τ))) (T.continuous_res h')
  | ih b =>
    rw [F.extFrobSymm_coe, res_coe, F.extFrob_coe, res_coe]
    congr 1
    apply Subtype.ext
    rw [coe_econFrob, coe_incl, coe_incl, coe_econFrobSymm, RingEquiv.apply_symm_apply]

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
