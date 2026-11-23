import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PBundlePair
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section Charts

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]
  [Algebra S Ω]

theorem prod_zpow_add_baseDeg (y : (Σ k, ι k) → Ω) (k₀ : K) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (δ : K → ℤ) (m : ℤ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(δ + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      (∏ k, y ⟨k, c k⟩ ^ (-δ k)) * y ⟨k₀, c k₀⟩ ^ (-m) := by
  have hterm : ∀ k, y ⟨k, c k⟩ ^ (-(δ + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      y ⟨k, c k⟩ ^ (-δ k) * (if k = k₀ then y ⟨k, c k⟩ ^ (-m) else 1) := by
    intro k
    simp only [Pi.add_apply, Pi.smul_apply, IndefiniteRowSideFullHecke.Kleiman2.baseDeg, smul_eq_mul]
    by_cases hk : k = k₀
    · subst hk
      rw [Pi.single_eq_same, if_pos rfl, mul_one, neg_add, zpow_add₀ (hc _)]
    · rw [Pi.single_eq_of_ne hk, if_neg hk, mul_zero, add_zero, mul_one]
  rw [Finset.prod_congr rfl (fun k _ => hterm k), Finset.prod_mul_distrib, Finset.prod_ite_eq',
    if_pos (Finset.mem_univ _)]

def baseRatio (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (c : ∀ k, ι k) : Ω :=
  Kleiman.xProd I * (y ⟨k₀, c k₀⟩ ^ I.1.card)⁻¹

omit [Fintype K] [DecidableEq K] in

theorem baseRatio_mem (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (c : ∀ k, ι k) :
    baseRatio y k₀ I c ∈ chartRingOver S y c := by
  have h : baseRatio y k₀ I c = ∏ i ∈ I.1, y ⟨k₀, e.symm i⟩ / y ⟨k₀, c k₀⟩ := by
    rw [Finset.prod_div_distrib, Finset.prod_const, div_eq_mul_inv]
    rfl
  rw [h]
  exact prod_mem fun i _ => Algebra.subset_adjoin ⟨⟨k₀, e.symm i⟩, rfl⟩

theorem mem_chartSecOver_iff (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (δ : K → ℤ)
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (t : Ω) :
    t ∈ chartSecOver S y k₀ e δ I ↔ ∃ n : ℕ, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      baseRatio y k₀ I c ^ n * (t * ∏ k, y ⟨k, c k⟩ ^ (-δ k)) ∈ chartRingOver S y c := by
  simp only [chartSecOver, Set.mem_ofPred_eq]
  refine exists_congr fun n => ?_
  rw [mem_secOver_iff_charts]
  refine forall_congr' fun c => forall_congr' fun hc => ?_
  rw [prod_zpow_add_baseDeg y k₀ c hc]
  have h : Kleiman.xProd I ^ n * t * ((∏ k, y ⟨k, c k⟩ ^ (-δ k)) *
      y ⟨k₀, c k₀⟩ ^ (-(((n * I.1.card : ℕ) : ℤ)))) =
      baseRatio y k₀ I c ^ n * (t * ∏ k, y ⟨k, c k⟩ ^ (-δ k)) := by
    rw [zpow_neg, zpow_natCast, baseRatio, mul_pow, inv_pow, ← pow_mul, mul_comm I.1.card n]
    ring
  rw [h]

omit [DecidableEq K] in

theorem exists_forall_baseRatio [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ}
    {e : ι k₀ ≃ Fin (N + 1)} (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (w : (∀ k, ι k) → Ω)
    (h : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      ∃ n : ℕ, baseRatio y k₀ I c ^ n * w c ∈ chartRingOver S y c) :
    ∃ n : ℕ, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      baseRatio y k₀ I c ^ n * w c ∈ chartRingOver S y c := by
  have hev : ∀ c : ∀ k, ι k, ∀ᶠ n : ℕ in Filter.atTop, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      baseRatio y k₀ I c ^ n * w c ∈ chartRingOver S y c := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n₀, hn₀⟩ := h c hc
      refine Filter.eventually_atTop.mpr ⟨n₀, fun n hn _ => ?_⟩
      have hsplit : baseRatio y k₀ I c ^ n * w c =
          baseRatio y k₀ I c ^ (n - n₀) * (baseRatio y k₀ I c ^ n₀ * w c) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
      rw [hsplit]
      exact mul_mem (pow_mem (baseRatio_mem y k₀ I c) _) hn₀
    · exact Filter.Eventually.of_forall fun _ h' => absurd h' hc
  exact (Filter.eventually_all.mpr hev).exists

theorem prod_zpow_mem_secOver (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ : K → ℤ) (hδ : ∀ k, 0 ≤ δ k) :
    ∏ k, y ⟨k, c k⟩ ^ δ k ∈ secOver S y δ := by
  rw [mem_secOver_iff_charts]
  intro c' _
  rw [← Finset.prod_mul_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (hδ k)
  have h : y ⟨k, c k⟩ ^ δ k * y ⟨k, c' k⟩ ^ (-δ k) = (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ m := by
    rw [hm, zpow_neg, zpow_natCast, zpow_natCast, div_pow, div_eq_mul_inv]
  rw [h]
  refine pow_mem ?_ m
  exact Algebra.subset_adjoin ⟨⟨k, c k⟩, rfl⟩

end Charts

theorem ChartSecMul.proof (h₁ : BundleOfDeg.Statement) : ChartSecMul.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y k₀ N e hM γ β I
  have hsub : ∀ δ : K → ℤ, ∃ Q : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm),
      (Q.sub I : Set Ω) = chartSecOver S y k₀ e δ I := by
    intro δ
    obtain ⟨Q, hQ⟩ := h₁ S K ι Ω y k₀ N e hM δ
    refine ⟨Q, Set.ext fun t => ?_⟩
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [Kleiman.SubSystem.gam, hQ]
  choose Q hQ using hsub
  have hmemP : ∀ δ t, t ∈ (Q δ).sub I ↔ t ∈ chartSecOver S y k₀ e δ I := fun δ t =>
    Set.ext_iff.mp (hQ δ) t

  have hmul : ∀ a b c : K → ℤ, a + b = c → (Q a).sub I * (Q b).sub I ≤ (Q c).sub I := by
    rintro a b _ rfl
    rw [Submodule.mul_le]
    intro g hg f hf
    rw [hmemP, mem_chartSecOver_iff] at hg hf ⊢
    obtain ⟨n₁, hn₁⟩ := hg
    obtain ⟨n₂, hn₂⟩ := hf
    refine ⟨n₁ + n₂, fun c hc => ?_⟩
    have hY : ∏ k, y ⟨k, c k⟩ ^ (-(a + b) k) =
        (∏ k, y ⟨k, c k⟩ ^ (-a k)) * ∏ k, y ⟨k, c k⟩ ^ (-b k) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, neg_add, zpow_add₀ (hc k)]
    have hsplit : baseRatio y k₀ I c ^ (n₁ + n₂) * (g * f * ∏ k, y ⟨k, c k⟩ ^ (-(a + b) k)) =
        (baseRatio y k₀ I c ^ n₁ * (g * ∏ k, y ⟨k, c k⟩ ^ (-a k))) *
          (baseRatio y k₀ I c ^ n₂ * (f * ∏ k, y ⟨k, c k⟩ ^ (-b k))) := by
      rw [hY, pow_add]
      ring
    rw [hsplit]
    exact mul_mem (hn₁ c hc) (hn₂ c hc)

  have hA : ∀ a : Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I, (a : Ω) ∈ (Q 0).sub I := by
    intro a
    have h1 : (1 : Ω) ∈ (Q 0).sub I := by
      refine (hmemP 0 1).mpr (mem_chartSecOver_of_mem S y k₀ e 0 I ?_)
      rw [mem_secOver_iff_charts]
      intro c _
      simp
    have := ((Q 0).sub I).smul_mem a h1
    rwa [Kleiman.chartRing_smul_def, mul_one] at this

  have hinv : ∀ δ : K → ℤ, (∀ k, 0 ≤ δ k) → 1 ≤ (Q δ).sub I * (Q (-δ)).sub I := by
    intro δ hδ
    obtain ⟨Q', hQ'⟩ := (Q δ).invertible I
    rw [← hQ']
    refine mul_le_mul_right (fun z hz => ?_) _
    rw [hmemP, mem_chartSecOver_iff]
    refine exists_forall_baseRatio y k₀ I _ fun c hc => ?_
    have hyc : (∏ k, y ⟨k, c k⟩ ^ δ k) ∈ (Q δ).sub I :=
      (hmemP δ _).mpr (mem_chartSecOver_of_mem S y k₀ e δ I (prod_zpow_mem_secOver y c δ hδ))
    have hw : z * ∏ k, y ⟨k, c k⟩ ^ δ k ∈ (1 : Submodule (Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) Ω) := by
      rw [← hQ', mul_comm z]
      exact Submodule.mul_mem_mul hyc hz
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp hw
    obtain ⟨n, hn⟩ := (mem_chartSecOver_iff y k₀ e 0 I _).mp ((hmemP 0 _).mp (hA a))
    refine ⟨n, ?_⟩
    have he : z * ∏ k, y ⟨k, c k⟩ ^ (-(-δ) k) = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ (-(0 : K → ℤ) k) := by
      simp only [Pi.neg_apply, neg_neg, Pi.zero_apply, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]
      exact ha.symm
    rw [he]
    exact hn c hc
  have hshift : ∀ ε δ : K → ℤ, (∀ k, 0 ≤ δ k) →
      (Q ε).sub I ≤ (Q (ε + δ)).sub I * (Q (-δ)).sub I := by
    intro ε δ hδ
    calc (Q ε).sub I = (Q ε).sub I * 1 := (mul_one _).symm
      _ ≤ (Q ε).sub I * ((Q δ).sub I * (Q (-δ)).sub I) := mul_le_mul_right (hinv δ hδ) _
      _ = (Q ε).sub I * (Q δ).sub I * (Q (-δ)).sub I := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_left (hmul _ _ _ rfl) _
  have hshift' : ∀ ε δ : K → ℤ, (∀ k, 0 ≤ δ k) →
      (Q ε).sub I ≤ (Q (ε - δ)).sub I * (Q δ).sub I := by
    intro ε δ hδ
    calc (Q ε).sub I = (Q ε).sub I * 1 := (mul_one _).symm
      _ ≤ (Q ε).sub I * ((Q δ).sub I * (Q (-δ)).sub I) := mul_le_mul_right (hinv δ hδ) _
      _ = (Q ε).sub I * (Q (-δ)).sub I * (Q δ).sub I := by rw [mul_comm ((Q δ).sub I), mul_assoc]
      _ ≤ _ := mul_le_mul_left (hmul _ _ _ (sub_eq_add_neg ε δ).symm) _

  have hbp : ∀ k, 0 ≤ (fun k => max (β k) 0) k := fun k => le_max_right _ _
  have hbm : ∀ k, 0 ≤ (fun k => max (-β k) 0) k := fun k => le_max_right _ _
  have hγ : γ + β + (fun k => max (-β k) 0) - (fun k => max (β k) 0) = γ := by
    funext k
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [max_def, max_def]
    split_ifs <;> omega
  have hβ : (fun k => max (β k) 0) + -(fun k => max (-β k) 0) = β := by
    funext k
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [max_def, max_def]
    split_ifs <;> omega
  have hle : (Q (γ + β)).sub I ≤ (Q γ).sub I * (Q β).sub I := by
    calc (Q (γ + β)).sub I
        ≤ (Q (γ + β + fun k => max (-β k) 0)).sub I * (Q (-fun k => max (-β k) 0)).sub I :=
          hshift _ _ hbm
      _ ≤ (Q (γ + β + (fun k => max (-β k) 0) - fun k => max (β k) 0)).sub I *
            (Q fun k => max (β k) 0).sub I * (Q (-fun k => max (-β k) 0)).sub I :=
          mul_le_mul_left (hshift' _ _ hbp) _
      _ = (Q γ).sub I * ((Q fun k => max (β k) 0).sub I * (Q (-fun k => max (-β k) 0)).sub I) := by
          rw [hγ, mul_assoc]
      _ ≤ (Q γ).sub I * (Q β).sub I := mul_le_mul_right (hmul _ _ _ hβ) _
  have heq : (Q γ).sub I * (Q β).sub I = (Q (γ + β)).sub I := le_antisymm (hmul _ _ _ rfl) hle
  rw [← hQ γ, ← hQ β, ← Submodule.mul_eq_span_mul_set, heq, hQ]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
