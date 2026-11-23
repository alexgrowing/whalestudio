import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementG
import Formalism.GaussJetBounds.GaussJetProofs.GField
import Formalism.GaussJetBounds.GaussJetProofs.FJEval
import Formalism.GaussJetBounds.GaussJetProofs.Labels
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.KOneConsequence

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

namespace EGauss

section Transfer

variable {F K : Type} [NormedField F] [NormedField K] (φ : F →+* K) {ν r0 r1 : ℕ}

lemma map_sPos (p : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    MvPowerSeries.map φ (sPos (K := F) p s ab) = sPos p s ab := by
  ext n
  rw [MvPowerSeries.coeff_map]
  change φ (∑ l ∈ range (n.degree + 1), _) = ∑ l ∈ range (n.degree + 1), _
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

lemma map_hhS [NeZero ν] (p : ℕ) (u : ZMod (2 * ν) → F) :
    MvPowerSeries.map φ (hhS (r0 := r0) (r1 := r1) p u) = hhS p (fun s => φ (u s)) := by
  unfold hhS
  simp only [map_sum, map_mul, map_pow, MvPowerSeries.map_C, map_sPos]

lemma inClass_map {ι : Type} (hφ : ∀ z, ‖φ z‖ = ‖z‖) (pp : F) (hh G : MvPowerSeries ι F)
    (h : InClass pp hh G) :
    InClass (φ pp) (MvPowerSeries.map φ hh) (MvPowerSeries.map φ G) := by
  obtain ⟨U, hU, hc⟩ := h
  refine ⟨fun i => MvPowerSeries.map φ (U i), fun i n => ?_, fun n => ?_⟩
  · rw [MvPowerSeries.coeff_map, hφ]
    exact hU i n
  · rw [MvPowerSeries.coeff_map, hc n, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_inv₀, map_pow, ← MvPowerSeries.coeff_map, map_mul, map_pow]

end Transfer

section Comb

variable {K : Type} [Field K] {ν r0 r1 : ℕ}

lemma minorAt_one {σ : Type} (s : σ) {l : ℕ} (h : l = 1) (T : Fin l → Fin r0 → K)
    (I : Fin l → Fin r1) :
    minorAt s T I = ∑ a, MvPolynomial.C (T ⟨0, by omega⟩ a) *
      MvPolynomial.X (s, a, I ⟨0, by omega⟩) := by
  subst h
  unfold minorAt
  rw [Matrix.det_fin_one]
  rfl

lemma entry_exists [NeZero ν] {At Al : Type} [Fintype At] [Fintype Al]
    (ξ : ZMod (2 * ν) → Fin r0 → K) (g : At → TpV ν r1) (pos : Al → ZMod (2 * ν)) (ht : Al → ℕ)
    (Tm : ∀ x, Fin (ht x) → Fin r0 → K) (Ic : ∀ x, Fin (ht x) → Fin r1) :
    ∃ (C : ℕ) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν))
      (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1),
      (∏ x, topForm ξ (g x)) * ∏ x, minorAt (pos x) (Tm x) (Ic x) = entryOp ξ e l sf T I ∧
      (∀ f : TpV ν r1 → ℕ, ∑ y, f y * e y = ∑ x, f (g x)) ∧
      (∀ f : ZMod (2 * ν) → (h : ℕ) → (Fin h → Fin r1) → ℕ,
        ∑ c, f (sf c) (l c) (I c) = ∑ x, f (pos x) (ht x) (Ic x)) ∧
      (∀ c i a, ∃ x i', T c i a = Tm x i' a) := by
  classical
  let q := (Fintype.equivFin Al).symm
  refine ⟨Fintype.card Al, fun y => (univ.filter (fun x => g x = y)).card, fun c => ht (q c),
    fun c => pos (q c), fun c => Tm (q c), fun c => Ic (q c), ?_, ?_, ?_, ?_⟩
  · unfold entryOp lowOp
    congr 1
    · rw [← Finset.prod_fiberwise univ g]
      refine Finset.prod_congr rfl fun y _ => ?_
      rw [Finset.prod_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.prod_const]
    · exact (Equiv.prod_comp q (fun x => minorAt (pos x) (Tm x) (Ic x))).symm
  · intro f
    rw [← Finset.sum_fiberwise univ g]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const,
      smul_eq_mul, mul_comm]
  · intro f
    exact Equiv.sum_comp q (fun x => f (pos x) (ht x) (Ic x))
  · intro c i a
    exact ⟨q c, i, rfl⟩

lemma sum_sub_sigma {S : Type} [Fintype S] [DecidableEq S] (colN : S → ℕ)
    (P : (Σ s, Fin (colN s)) → Prop) [DecidablePred P] (f : (Σ s, Fin (colN s)) → ℕ) (s : S) :
    ∑ x : {x // P x}, (if x.1.1 = s then f x.1 else 0) =
      ∑ c : Fin (colN s), if P ⟨s, c⟩ then f ⟨s, c⟩ else 0 := by
  rw [← Finset.sum_subtype (univ.filter P) (by simp) (fun x => if x.1 = s then f x else 0),
    Finset.sum_filter, Fintype.sum_sigma, Finset.sum_eq_single s]
  · simp
  · intro s' _ h
    simp [h]
  · simp

end Comb

section Struct

variable {K : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν]

theorem struct (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1)
    (Y : ZMod (2 * ν) × Fin r0 × Fin r0 → K) :
    ∃ (C : ℕ) (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ)
      (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K)
      (I' : ∀ c, Fin (l c) → Fin r1),
      (∏ s : ZMod (2 * ν), minorProd
        (fun (i : Fin r0) (b : Fin r1) =>
          (∑ a : Fin r0, MvPolynomial.C (Y (s, i, a)) * MvPolynomial.X (s, a, b) :
            MvPolynomial (ZV ν r0 r1) K)) (hts s) (hp s) (I s)) = entryOp ξ e l sf T I' ∧
      (∀ s a, ∃ y, ξ s a = Y y) ∧ (∀ c i a, ∃ y, T c i a = Y y) ∧
      alN e = alG TT colN hts ∧ capN sf = capG TT colN hts ∧ lsN l sf = lsG TT colN hts ∧
      ∀ (J : Finset (Fin r1)) (i : ℕ), 1 ≤ i →
        (∑ x : TpV ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)
            then e x else 0) +
          ∑ c, (if (sf c).val % 2 = 1 then ((univ.image (I' c)) ∩ J).card else 0)) ≤
        ∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
          (if s.val % 2 = 0 then min (hts s c) i - ((univ.image (I s c)) ∩ J).card
          else ((univ.image (I s c)) ∩ J).card) := by
  classical
  let A := Σ s, Fin (colN s)
  let top : A → Prop := fun x => x.1 ∈ TT ∧ hts x.1 x.2 = 1
  let ξ : ZMod (2 * ν) → Fin r0 → K := fun s a => Y (s, ⟨0, a.pos⟩, a)
  let fac : A → MvPolynomial (ZV ν r0 r1) K := fun x =>
    minorAt x.1 (fun i a => Y (x.1, ⟨i.val, lt_of_lt_of_le i.isLt (hp x.1 x.2)⟩, a)) (I x.1 x.2)
  let g : {x : A // top x} → TpV ν r1 := fun x =>
    (x.1.1, I x.1.1 x.1.2 ⟨0, by rw [x.2.2]; exact one_pos⟩)
  obtain ⟨C, e, l, sf, T, I', hop, he, hl, hT⟩ := entry_exists ξ g
    (fun x : {x : A // ¬ top x} => x.1.1) (fun x => hts x.1.1 x.1.2)
    (fun x i a => Y (x.1.1, ⟨i.val, lt_of_lt_of_le i.isLt (hp x.1.1 x.1.2)⟩, a))
    (fun x => I x.1.1 x.1.2)
  have hal : ∀ s, alN e s = ∑ c : Fin (colN s), if top ⟨s, c⟩ then 1 else 0 := by
    intro s
    rw [← sum_sub_sigma colN top (fun _ => 1) s]
    have h := he (fun y => if y.1 = s then 1 else 0)
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s (by intro s' _ h; simp [h]) (by simp)] at h
    simpa [alN] using h
  have hcap : ∀ s, capN sf s = ∑ c : Fin (colN s), if ¬ top ⟨s, c⟩ then 1 else 0 := by
    intro s
    rw [← sum_sub_sigma colN (fun x => ¬ top x) (fun _ => 1) s,
      ← hl (fun s' _ _ => if s' = s then 1 else 0)]
    unfold capN
    rw [Finset.card_filter]
  have hls : ∀ s, lsN l sf s = ∑ c : Fin (colN s), if ¬ top ⟨s, c⟩ then hts s c else 0 := by
    intro s
    rw [← sum_sub_sigma colN (fun x => ¬ top x) (fun x => hts x.1 x.2) s,
      ← hl (fun s' h _ => if s' = s then h else 0)]
    simp [lsN, Finset.sum_filter]
  have halG : ∀ s, (∑ c : Fin (colN s), if top ⟨s, c⟩ then 1 else 0) = alG TT colN hts s := by
    intro s
    unfold alG
    by_cases hs : s ∈ TT
    · rw [if_pos hs, Finset.card_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [top, hs, true_and]
    · simp [top, hs]
  refine ⟨C, ξ, e, l, sf, T, I', ?_, fun s a => ⟨_, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hop]
    have h1 : ∀ x : {x : A // top x}, topForm ξ (g x) = fac x.1 := by
      intro x
      simp only [fac]
      rw [minorAt_one x.1.1 x.2.2]
      rfl
    rw [Finset.prod_congr rfl (fun x _ => h1 x)]
    have h2 := Fintype.prod_subtype_mul_prod_subtype top fac
    rw [Fintype.prod_sigma] at h2
    exact h2.symm
  · intro c i a
    obtain ⟨x, i', h⟩ := hT c i a
    exact ⟨_, h⟩
  · funext s
    rw [hal, halG]
  · funext s
    have h : (∑ c : Fin (colN s), if top ⟨s, c⟩ then 1 else 0) +
        (∑ c : Fin (colN s), if ¬ top ⟨s, c⟩ then 1 else 0) = colN s := by
      rw [← Finset.sum_add_distrib]
      trans ∑ _c : Fin (colN s), 1
      · refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> rfl
      · simp
    rw [halG] at h
    rw [hcap]
    unfold capG
    omega
  · funext s
    have h : (∑ c : Fin (colN s), if top ⟨s, c⟩ then 1 else 0) +
        (∑ c : Fin (colN s), if ¬ top ⟨s, c⟩ then hts s c else 0) = ∑ c, hts s c := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : top ⟨s, c⟩
      · simp [hc, hc.2]
      · simp [hc]
    rw [halG] at h
    rw [hls]
    unfold lsG
    omega
  · intro J i hi
    have e1 : ∑ x : TpV ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)
        then e x else 0) = ∑ x : {x : A // top x},
          if ((g x).1.val % 2 = 0 ∧ (g x).2 ∉ J) ∨ ((g x).1.val % 2 = 1 ∧ (g x).2 ∈ J)
            then 1 else 0 := by
      rw [← he (fun y => if (y.1.val % 2 = 0 ∧ y.2 ∉ J) ∨ (y.1.val % 2 = 1 ∧ y.2 ∈ J)
        then 1 else 0)]
      refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs <;> simp
    rw [e1, hl (fun s _ Ih => if s.val % 2 = 1 then ((univ.image Ih) ∩ J).card else 0)]
    let W : A → ℕ := fun x =>
      if x.1.val % 2 = 0 then min (hts x.1 x.2) i - ((univ.image (I x.1 x.2)) ∩ J).card
      else ((univ.image (I x.1 x.2)) ∩ J).card
    have e2 := Fintype.sum_subtype_add_sum_subtype top W
    rw [Fintype.sum_sigma] at e2
    refine le_trans ?_ (le_of_eq e2)
    refine add_le_add (Finset.sum_le_sum fun x _ => ?_) (Finset.sum_le_sum fun x _ => ?_)
    · obtain ⟨⟨s, c⟩, hs, hc⟩ := x
      have hc' : hts s c = 1 := hc
      have him : univ.image (I s c) = {I s c ⟨0, by rw [hc']; exact one_pos⟩} := by
        ext b
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨j, rfl⟩
          congr 1
          apply Fin.ext
          have := j.isLt
          simp only
          omega
        · rintro rfl
          exact ⟨_, rfl⟩
      have hmin : min 1 i = 1 := min_eq_left hi
      simp only [W, g, him, hc', hmin]
      by_cases hb : I s c ⟨0, by rw [hc']; exact one_pos⟩ ∈ J
      · rw [Finset.singleton_inter_of_mem hb]
        rcases Nat.mod_two_eq_zero_or_one s.val with h | h <;> simp [h, hb]
      · rw [Finset.singleton_inter_of_notMem hb]
        rcases Nat.mod_two_eq_zero_or_one s.val with h | h <;> simp [h, hb]
    · simp only [W]
      rcases Nat.mod_two_eq_zero_or_one x.1.1.val with h | h <;> simp [h]

end Struct

section Reduce

lemma norm_p_complex (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have h := Formalism.DworkPowerSeriesWeights.norm_intCast_padicComplex p (p : ℤ)
  rw [Int.cast_natCast, Int.cast_natCast] at h
  rw [h]
  exact Padic.norm_p

theorem reduce (p : ℕ) [Fact p.Prime] (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → ℂ_[p])
    (F : MvPowerSeries (ZV ν r0 r1) ℂ_[p]) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1)
    (hp2 : 2 < p) (hu : ∀ s, ‖u s‖ ≤ 1) (hF : InClass (p : ℂ_[p]) (hhS p u) F) :
    ∃ (K : Type) (_ : NormedField K), IsUltrametricDist K ∧
      ∃ (C : ℕ) (u' : ZMod (2 * ν) → K) (F' : MvPowerSeries (ZV ν r0 r1) K)
        (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ)
        (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K)
        (I' : ∀ c, Fin (l c) → Fin r1),
        EntryHyp p ν r0 r1 C u' F' TT ξ e l T ∧
        (∀ n, ‖MvPolynomial.coeff n (frameJet colN hts hp I F)‖ ≤
          ‖jetPair (entryOp ξ e l sf T I') F'‖) ∧
        alN e = alG TT colN hts ∧ capN sf = capG TT colN hts ∧ lsN l sf = lsG TT colN hts ∧
        ∀ (J : Finset (Fin r1)) (i : ℕ), 1 ≤ i →
          (∑ x : TpV ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)
              then e x else 0) +
            ∑ c, (if (sf c).val % 2 = 1 then ((univ.image (I' c)) ∩ J).card else 0)) ≤
          ∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
            (if s.val % 2 = 0 then min (hts s c) i - ((univ.image (I s c)) ∩ J).card
            else ((univ.image (I s c)) ∩ J).card) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨K, instK, hult, hchar, φ, Y, hφ, hgauss, hgen⟩ :=
    Formalism.DworkPowerSeriesWeights.residuallyGenericExists p (ZMod (2 * ν) × Fin r0 × Fin r0)
  have hnp : ‖(p : K)‖ = (p : ℝ)⁻¹ := by rw [← map_natCast φ, hφ, norm_p_complex]
  have hY : ∀ y, ‖Y y‖ ≤ 1 := by
    intro y
    have h := hgauss (MvPolynomial.X y)
    rw [MvPolynomial.eval₂_X] at h
    rw [h]
    refine ciSup_le fun m => ?_
    classical
    rw [MvPolynomial.coeff_X]
    split_ifs <;> simp
  obtain ⟨C, ξ, e, l, sf, T, I', hop, hξ, hT, hal, hcap, hls, hB⟩ :=
    struct TT colN hts hp I Y
  refine ⟨K, instK, hult, C, fun s => φ (u s), MvPowerSeries.map φ F, ξ, e, l, sf, T, I',
    ⟨hpp, hp2, hnp, fun s => by rw [hφ]; exact hu s, ?_, ?_, ?_, ?_⟩, ?_, hal, hcap, hls, hB⟩
  · have h := inClass_map φ hφ _ _ _ hF
    rwa [map_natCast, map_hhS] at h
  · intro s a
    obtain ⟨y, h⟩ := hξ s a
    rw [h]
    exact hY y
  · intro c i a
    obtain ⟨y, h⟩ := hT c i a
    rw [h]
    exact hY y
  · intro x hx
    have h : alN e x.1 = 0 := by
      rw [hal]
      unfold alG
      rw [if_neg hx]
    unfold alN at h
    exact (Finset.sum_eq_zero_iff.1 h) x.2 (Finset.mem_univ _)
  · intro n
    refine le_trans (le_ciSup (Formalism.DworkPowerSeriesWeights.bddAbove_norm_coeff _) n) ?_
    rw [← hgauss, ← hop]
    unfold frameJet
    rw [Formalism.DworkPowerSeriesWeights.eval₂_jetPairPoly, map_prod]
    simp only [Formalism.DworkPowerSeriesWeights.ringMap_minorProd, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    exact le_rfl

end Reduce

end EGauss

open EGauss

theorem gauss_a_one_of_entry (hE : EntryExcessBound) : FrameJetExcessBound := by
  intro p _ ν r0 r1 _ u F TT colN hts hp I hp2 hu hF n
  obtain ⟨K, instK, hult, C, u', F', ξ, e, l, sf, T, I', hyp, hco, hal, hcap, hls, -⟩ :=
    reduce p ν r0 r1 u F TT colN hts hp I hp2 hu hF
  have h := hE K p ν r0 r1 C u' F' TT ξ e l sf T I' hyp
  rw [hal, hcap, hls] at h
  exact (hco n).trans h

theorem gauss_a_two_of_entry (hE : EntryCappedBound) : FrameJetCappedBound := by
  intro p _ ν r0 r1 _ u F TT colN hts hp I hp2 hu hF n
  obtain ⟨K, instK, hult, C, u', F', ξ, e, l, sf, T, I', hyp, hco, hal, hcap, hls, -⟩ :=
    reduce p ν r0 r1 u F TT colN hts hp I hp2 hu hF
  have h := hE K p ν r0 r1 C u' F' TT ξ e l sf T I' hyp
  rw [hal, hcap, hls] at h
  exact (hco n).trans h

theorem GaussB_of (hE : EntryB) : GaussB := by
  intro p _ ν r0 r1 i _ u F TT colN hts hp I hp2 hi hu hF n
  obtain ⟨K, instK, hult, C, u', F', ξ, e, l, sf, T, I', hyp, hco, hal, hcap, hls, hB⟩ :=
    reduce p ν r0 r1 u F TT colN hts hp I hp2 hu hF
  have h := hE K p ν r0 r1 C u' F' TT ξ e l sf T I' (univ.filter (fun b : Fin r1 => b.val < i)) hyp
  rw [hal, hcap, hls] at h
  refine le_trans ?_ h
  have hnp : ‖(p : K)‖ = (p : ℝ)⁻¹ := hyp.2.2.1
  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (Fact.out : p.Prime).pos)
  have hp1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  rw [norm_mul, norm_mul, norm_pow, norm_pow, hnp, norm_p_complex]
  exact mul_le_mul (pow_le_pow_of_le_one hp0.le hp1 (hB _ i hi)) (hco n) (norm_nonneg _)
    (pow_nonneg hp0.le _)

theorem gauss_a_one_bound : FrameJetExcessBound := gauss_a_one_of_entry Top.entry_a_one

theorem gauss_a_two_bound : FrameJetCappedBound := gauss_a_two_of_entry Top.entry_a_two

theorem gauss_b : GaussB := GaussB_of Top.entryB

end Formalism.InvariantFactorPaths.G7
