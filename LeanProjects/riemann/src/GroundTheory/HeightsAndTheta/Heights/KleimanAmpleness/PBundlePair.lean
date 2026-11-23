import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisLast
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerExtra
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

noncomputable section

section FirstTyping

variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}

theorem twist_sub_eq_mul (F Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, w, hw, rfl⟩
    exact ⟨q, hq, w, hw, rfl⟩
  · rintro ⟨q, hq, w, hw, rfl⟩
    exact ⟨q, hq, w, hw, rfl⟩

theorem pow_sub_eq (Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) (b : ℕ) :
    (Q.pow b).sub I = Q.sub I ^ b := by
  induction b with
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    change Kleiman.twistMod S x 0 I = _
    rw [Kleiman.twistMod_eq_span 0 I hi, zpow_zero, pow_zero, Submodule.one_eq_span]
  | succ b ih =>
    change ((Q.pow b).twist Q).sub I = _
    rw [twist_sub_eq_mul, ih, pow_succ']

theorem exists_mul_eq_prod_pow {I : Finset (Fin (N + 1))} {s : Kleiman.Poly S N} (hs : s ∈ Kleiman.monos I) :
    ∃ (r d d' : ℕ) (s' : Kleiman.Poly S N), s.IsHomogeneous d ∧ s'.IsHomogeneous d' ∧
      d + d' = r * I.card ∧ s * s' = (∏ j ∈ I, X j) ^ r := by
  classical
  induction hs using Submonoid.closure_induction with
  | mem z hz =>
    obtain ⟨j, hj, rfl⟩ := hz
    have hj' : j ∈ I := by exact_mod_cast hj
    refine ⟨1, 1, (I.erase j).card, ∏ l ∈ I.erase j, X l, isHomogeneous_X S j, ?_, ?_, ?_⟩
    · simpa using IsHomogeneous.prod (I.erase j) (fun l => (X l : Kleiman.Poly S N)) (fun _ => 1)
        (fun l _ => isHomogeneous_X S l)
    · rw [one_mul, add_comm]
      exact Finset.card_erase_add_one hj'
    · rw [pow_one]
      exact Finset.mul_prod_erase I (fun l => (X l : Kleiman.Poly S N)) hj'
  | one => exact ⟨0, 0, 0, 1, isHomogeneous_one _ _, isHomogeneous_one _ _, by simp, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨r, d, d', s', h1, h2, h3, h4⟩ := ha
    obtain ⟨r₂, d₂, d₂', t', g1, g2, g3, g4⟩ := hb
    refine ⟨r + r₂, d + d₂, d' + d₂', s' * t', h1.mul g1, h2.mul g2, by rw [add_mul]; omega, ?_⟩
    rw [pow_add, ← h4, ← g4]
    ring

theorem mem_sub_iff_gam (Q : Kleiman.LineBundle S x) (I : Kleiman.Chart x) (t : Ω) :
    t ∈ Q.sub I ↔ ∃ n : ℕ, Kleiman.xProd I ^ n * t ∈ Q.gam ((n * I.1.card : ℕ) : ℤ) := by
  classical
  have hxI : Kleiman.xProd I ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => (Kleiman.mem_support x).mp (I.2.2 hi)
  have hprod : ∀ r : ℕ, aeval x ((∏ j ∈ I.1, (X j : Kleiman.Poly S N)) ^ r) = Kleiman.xProd I ^ r := by
    intro r
    simp [Kleiman.xProd, map_prod]
  constructor
  · intro ht
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi)
    have hsub : (Kleiman.singleChart hxi).1 ⊆ I.1 := Finset.singleton_subset_iff.mpr hi
    obtain ⟨a, ⟨u, hu⟩, hat⟩ := (Q.mem_iff _ I hsub t).mp ht
    have hev : ∀ᶠ n : ℕ in Filter.atTop, ∀ J, x i ^ n • ((a : Ω) • t) ∈
        (Q.twist (Kleiman.twistSys S x (n : ℤ))).sub J :=
      Filter.eventually_all.mpr fun J =>
        Kleiman.ExtensionProof.eventually_pow_smul_mem Q.toSubFamily hxi hat J
    obtain ⟨n, hn⟩ := hev.exists
    have hgam : x i ^ n • ((a : Ω) • t) ∈ Q.gam (n : ℤ) := Kleiman.ExtensionProof.mem_gam.mpr hn
    have hinv : (a : Ω) * ((↑u⁻¹ : Kleiman.chartRing S x I) : Ω) = 1 := by
      have := congrArg Subtype.val (Units.mul_inv u)
      rw [hu] at this
      exact this
    obtain ⟨g, s, r, hs, hg, hsr, hb⟩ := (↑u⁻¹ : Kleiman.chartRing S x I).2
    obtain ⟨r', d, d', s', hsd, hs', hdd, hss⟩ := exists_mul_eq_prod_pow hs
    have hs0 : aeval x s ≠ 0 := Kleiman.eval_ne_zero_of_mem_monos I hs
    have hrd : r = d := hsr.inj_right hsd (fun h => hs0 (by rw [h, map_zero]))
    subst hrd
    have h1 : (∏ l ∈ I.1.erase i, (X l : Kleiman.Poly S N)).IsHomogeneous (I.1.erase i).card := by
      simpa using IsHomogeneous.prod (I.1.erase i) (fun l => (X l : Kleiman.Poly S N)) (fun _ => 1)
        (fun l _ => isHomogeneous_X S l)
    have hPh := ((h1.pow n).mul hg).mul hs'
    have hmem := Kleiman.ExtensionProof.smul_mem_gam Q.toSubSystem hPh hgam
    refine ⟨n + r', ?_⟩
    have hc := Finset.card_erase_add_one hi
    have hdeg : ((n : ℤ) + (((I.1.erase i).card * n + r + d' : ℕ) : ℤ)) =
        (((n + r') * I.1.card : ℕ) : ℤ) := by
      rw [← hc] at hdd ⊢
      have hdd' : ((r : ℤ) + d') = r' * ((I.1.erase i).card + 1) := by exact_mod_cast hdd
      push_cast
      linear_combination hdd'
    rw [hdeg] at hmem
    convert hmem using 1
    have hag : (a : Ω) * aeval x g = aeval x s := by
      rw [hb] at hinv
      field_simp at hinv
      linear_combination hinv
    have hss' : aeval x s * aeval x s' = (x i * ∏ l ∈ I.1.erase i, x l) ^ r' := by
      have := congrArg (aeval x) hss
      simp only [map_mul, map_pow, map_prod, aeval_X] at this
      rw [this, Finset.mul_prod_erase I.1 x hi]
    simp only [smul_eq_mul, map_mul, map_pow, map_prod, aeval_X, Kleiman.xProd]
    rw [← Finset.mul_prod_erase I.1 x hi]
    linear_combination (-(x i * ∏ l ∈ I.1.erase i, x l) ^ n * t) * hss' +
      (-(x i * ∏ l ∈ I.1.erase i, x l) ^ n * t * aeval x s') * hag
  · rintro ⟨n, hn⟩
    have h1 := (Kleiman.ExtensionProof.mem_gam.mp hn) I
    have hs : (∏ j ∈ I.1, (X j : Kleiman.Poly S N)) ^ n ∈ Kleiman.monos I.1 :=
      pow_mem (prod_mem fun j hj => Kleiman.X_mem_monos hj) n
    have hsh : ((∏ j ∈ I.1, (X j : Kleiman.Poly S N)) ^ n).IsHomogeneous (I.1.card * n) := by
      have := IsHomogeneous.prod I.1 (fun l => (X l : Kleiman.Poly S N)) (fun _ => 1)
        (fun l _ => isHomogeneous_X S l)
      simpa using this.pow n
    have h2 := Kleiman.ExtensionProof.inv_smul_mem Q.toSubSystem h1 hs hsh (by push_cast; ring)
    rw [hprod, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hxI), one_mul] at h2
    exact h2

end FirstTyping

section SecondTyping

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]
  [Algebra S Ω]

theorem mem_secOver_iff_charts (y : (Σ k, ι k) → Ω) (δ : K → ℤ) (t : Ω) :
    t ∈ secOver S y δ ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      t * ∏ k, y ⟨k, c k⟩ ^ (-δ k) ∈ chartRingOver S y c := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]

theorem forall_mem_chartSecOver_iff (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (δ : K → ℤ) (t : Ω) :
    (∀ I, t ∈ chartSecOver S y k₀ e δ I) ↔ t ∈ secOver S y δ := by
  constructor
  · intro h
    rw [mem_secOver_iff_charts]
    intro c hc
    have hxi : (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (e (c k₀)) ≠ 0 := by
      simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hc k₀
    obtain ⟨n, hn⟩ := h (Kleiman.singleChart hxi)
    rw [mem_secOver_iff_charts] at hn
    have h1 := hn c hc
    have hterm : ∀ k, y ⟨k, c k⟩ ^ (-(δ + (((n * (Kleiman.singleChart hxi).1.card : ℕ) : ℤ)) •
        IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
        y ⟨k, c k⟩ ^ (-δ k) * (if k = k₀ then (y ⟨k, c k⟩ ^ n)⁻¹ else 1) := by
      intro k
      simp only [Pi.add_apply, Pi.smul_apply, IndefiniteRowSideFullHecke.Kleiman2.baseDeg, smul_eq_mul, Kleiman.singleChart,
        Finset.card_singleton, mul_one]
      by_cases hk : k = k₀
      · subst hk
        rw [Pi.single_eq_same, if_pos rfl, mul_one, neg_add, zpow_add₀ (hc _), zpow_neg (y _) (n : ℤ),
          zpow_natCast]
      · rw [Pi.single_eq_of_ne hk, if_neg hk, mul_zero, add_zero, mul_one]
    rw [Finset.prod_congr rfl (fun k _ => hterm k), Finset.prod_mul_distrib, Finset.prod_ite_eq',
      if_pos (Finset.mem_univ _)] at h1
    convert h1 using 1
    have hx : Kleiman.xProd (Kleiman.singleChart hxi) = y ⟨k₀, c k₀⟩ := by
      simp [Kleiman.xProd, Kleiman.singleChart, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
    rw [hx]
    have := pow_ne_zero n (hc k₀)
    field_simp
  · intro h I
    exact mem_chartSecOver_of_mem S y k₀ e δ I h

end SecondTyping

theorem BundlePair.proof (h₁ : BundleOfDeg.Statement) (h₂ : ChartSecMul.Statement)
    (h₃ : ChartSecGen.Statement) : BundlePair.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y k₀ N e hM γ β
  have hsub : ∀ δ : K → ℤ, ∃ Q : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm),
      ∀ I, (Q.sub I : Set Ω) = chartSecOver S y k₀ e δ I := by
    intro δ
    obtain ⟨Q, hQ⟩ := h₁ S K ι Ω y k₀ N e hM δ
    refine ⟨Q, fun I => Set.ext fun t => ?_⟩
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [Kleiman.SubSystem.gam, hQ]
  have hsecs : ∀ (Q : Kleiman.SubSystem S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω) (δ : K → ℤ),
      (∀ I, (Q.sub I : Set Ω) = chartSecOver S y k₀ e δ I) → Q.secs = secOver S y δ := by
    intro Q δ hQ
    ext t
    rw [← forall_mem_chartSecOver_iff]
    simp only [Kleiman.SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
    exact forall_congr' fun I => by rw [← hQ I]; rfl
  obtain ⟨G, hG⟩ := hsub γ
  obtain ⟨B, hB⟩ := hsub β
  have hpow : ∀ (b : ℕ) I, ((G.twist (B.pow b)).sub I : Set Ω) = chartSecOver S y k₀ e (γ + b • β) I := by
    intro b I
    rw [twist_sub_eq_mul, pow_sub_eq]
    induction b with
    | zero => simp [hG I]
    | succ b ih =>
      rw [pow_succ', mul_assoc, Submodule.mul_eq_span_mul_set (B.sub I) (B.sub I ^ b * G.sub I), hB I, ih,
        h₂ S K ι Ω y k₀ N e hM β (γ + b • β) I]
      congr 1
      rw [add_smul, one_smul]
      abel
  refine ⟨G, B, fun b => hsecs _ _ (hpow b), fun n η => ?_⟩
  rw [hsecs B.toSubSystem β hB]
  constructor
  · rintro ⟨h, hg⟩
    exact ⟨h, fun I => SetLike.coe_injective
      (((h₃ S K ι Ω y k₀ N e hM β n η h).mp hg I).trans (hB I).symm)⟩
  · rintro ⟨h, hs⟩
    exact ⟨h, (h₃ S K ι Ω y k₀ N e hM β n η h).mpr fun I => by rw [hs I, hB I]⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
