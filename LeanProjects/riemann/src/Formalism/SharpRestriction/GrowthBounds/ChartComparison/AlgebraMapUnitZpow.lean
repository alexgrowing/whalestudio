import Formalism.SharpRestriction.GrowthBounds.ChartComparison.ComparisonZeroWeightBase
import Formalism.LocalRingCardinality.Lemmas

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.L2.G.Cmp IsDiscreteValuationRing

section Scalar

variable {LL O Kf : Type} [Field LL] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

theorem val_ne_zero (val : AddValuation LL (WithTop ℤ)) {x : LL} {m : ℤ} (hx : val x = (m : WithTop ℤ)) : x ≠ 0 := by
  rintro rfl
  rw [AddValuation.map_zero] at hx
  exact WithTop.top_ne_coe hx

theorem val_inv (val : AddValuation LL (WithTop ℤ)) {x : LL} {m : ℤ} (hx : val x = (m : WithTop ℤ)) :
    val x⁻¹ = ((-m : ℤ) : WithTop ℤ) := by
  have h0 := val_ne_zero val hx
  have h1 : val x⁻¹ + val x = 0 := by rw [← AddValuation.map_mul, inv_mul_cancel₀ h0, AddValuation.map_one]
  have h2 : val x⁻¹ ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    exact inv_ne_zero h0
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 h2
  rw [← hq, hx, ← WithTop.coe_add] at h1
  have h3 : q + m = 0 := by exact_mod_cast h1
  rw [← hq]
  congr 1
  omega

theorem val_pow (val : AddValuation LL (WithTop ℤ)) {x : LL} {m : ℤ} (hx : val x = (m : WithTop ℤ)) (k : ℕ) :
    val (x ^ k) = (((k : ℤ) * m : ℤ) : WithTop ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AddValuation.map_mul, ih, hx, ← WithTop.coe_add]
    congr 1
    push_cast
    ring

theorem val_zpow (val : AddValuation LL (WithTop ℤ)) {x : LL} {m : ℤ} (hx : val x = (m : WithTop ℤ)) (n : ℤ) :
    val (x ^ n) = ((n * m : ℤ) : WithTop ℤ) := by
  cases n with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact val_pow val hx k
  | negSucc k =>
    rw [zpow_negSucc, val_inv val (val_pow val hx (k + 1))]
    congr 1
    rw [Int.negSucc_eq]
    push_cast
    ring

theorem unit_of_val_zero (hinj : Function.Injective (algebraMap O Kf)) (e : LL →+* Kf) (val : AddValuation LL (WithTop ℤ))
    (hint : ∀ x, (0 : WithTop ℤ) ≤ val x ↔ e x ∈ Set.range (algebraMap O Kf)) {x : LL}
    (hx : val x = ((0 : ℤ) : WithTop ℤ)) : ∃ ζ : Oˣ, e x = algebraMap O Kf ζ := by
  have h0 := val_ne_zero val hx
  obtain ⟨o1, h1⟩ := (hint x).1 (by rw [hx]; exact le_refl _)
  obtain ⟨o2, h2⟩ := (hint x⁻¹).1 (by rw [val_inv val hx]; exact le_refl _)
  have h3 : o1 * o2 = 1 := by
    apply hinj
    rw [map_mul, h1, h2, ← map_mul, mul_inv_cancel₀ h0, map_one, map_one]
  exact ⟨Units.mkOfMulEqOne o1 o2 h3, h1.symm⟩

theorem algebraMap_unit_zpow (η : Oˣ) (n : ℤ) :
    algebraMap O Kf ((η ^ n : Oˣ) : O) = (algebraMap O Kf (η : O)) ^ n := by
  have h1 := map_zpow (Units.map (algebraMap O Kf : O →* Kf)) η n
  have h2 := congrArg (fun z : Kfˣ => (z : Kf)) h1
  simp only [Units.coe_map, Units.val_zpow_eq_zpow_val] at h2
  exact h2

theorem valScalar_gen (hinj : Function.Injective (algebraMap O Kf)) (e : LL →+* Kf) (val : AddValuation LL (WithTop ℤ))
    (hint : ∀ x, (0 : WithTop ℤ) ≤ val x ↔ e x ∈ Set.range (algebraMap O Kf)) (p E : ℕ) (hE : 0 < E)
    (hp : val (p : LL) = (((E : ℕ) : ℤ) : WithTop ℤ)) (a : LL) (n : ℤ) (han : val a = (n : WithTop ℤ)) (s : ℝ) (ϖ : O)
    (hϖ : Irreducible ϖ) (o : O)
    (ho : e a = algebraMap O Kf ϖ ^ ⌈s * ((addVal O (p : O)).toNat : ℝ)⌉ * algebraMap O Kf o) : (E : ℝ) * s ≤ (n : ℝ) := by
  have hp0 : (p : LL) ≠ 0 := val_ne_zero val hp
  have hPO : algebraMap O Kf (p : O) = e (p : LL) := by rw [map_natCast, map_natCast]
  have hP0 : (p : O) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hPO
    exact hp0 ((map_eq_zero e).1 hPO.symm)
  obtain ⟨U, η, hη⟩ := eq_unit_mul_pow_irreducible hP0 hϖ
  have hU : (addVal O (p : O)).toNat = U := by
    rw [hη, addVal_def' η hϖ U]
    rfl
  rw [hU] at ho
  have hU1 : 1 ≤ U := by
    by_contra hU0
    have hU0' : U = 0 := by omega
    rw [hU0', pow_zero, mul_one] at hη
    have h1 : e ((p : LL)⁻¹) ∈ Set.range (algebraMap O Kf) := by
      refine ⟨((η⁻¹ : Oˣ) : O), ?_⟩
      rw [map_inv₀, ← hPO, hη]
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    have h2 := (hint _).2 h1
    rw [val_inv val hp] at h2
    have h3 : (0 : ℤ) ≤ -((E : ℕ) : ℤ) := by exact_mod_cast h2
    omega
  by_contra hlt
  rw [not_le] at hlt
  have hk : s * (U : ℝ) ≤ (⌈s * (U : ℝ)⌉ : ℝ) := Int.le_ceil _
  generalize ⌈s * (U : ℝ)⌉ = k at ho hk
  have hd : (U : ℤ) * n + 1 ≤ k * (E : ℤ) := by
    have hUr : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU1
    have hEr : (0 : ℝ) < (E : ℝ) := by exact_mod_cast hE
    have h1 : (U : ℝ) * (n : ℝ) < (k : ℝ) * (E : ℝ) := by
      calc (U : ℝ) * (n : ℝ) < (U : ℝ) * ((E : ℝ) * s) := mul_lt_mul_of_pos_left hlt hUr
        _ = (s * (U : ℝ)) * (E : ℝ) := by ring
        _ ≤ (k : ℝ) * (E : ℝ) := mul_le_mul_of_nonneg_right hk hEr.le
    have h2 : (U : ℤ) * n < k * (E : ℤ) := by exact_mod_cast h1
    omega
  have hu : val (a ^ E * (p : LL) ^ (-n)) = ((0 : ℤ) : WithTop ℤ) := by
    rw [AddValuation.map_mul, val_pow val han E, val_zpow val hp (-n), ← WithTop.coe_add]
    congr 1
    ring
  obtain ⟨ζ, hζ⟩ := unit_of_val_zero hinj e val hint hu
  have hϖK : algebraMap O Kf ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hinj (by rw [h0, map_zero]))
  have hηK : algebraMap O Kf (η : O) ≠ 0 := fun h0 => η.ne_zero (hinj (by rw [h0, map_zero]))
  obtain ⟨d, hdd⟩ : ∃ d : ℕ, k * (E : ℤ) + -((U : ℤ) * n) = ((d + 1 : ℕ) : ℤ) :=
    ⟨(k * (E : ℤ) - (U : ℤ) * n - 1).toNat, by push_cast; rw [Int.toNat_of_nonneg (by omega)]; ring⟩
  have h1 : algebraMap O Kf (ζ : O) = algebraMap O Kf ϖ ^ (k * (E : ℤ)) * algebraMap O Kf o ^ E *
      ((algebraMap O Kf (η : O)) ^ (-n) * algebraMap O Kf ϖ ^ (-((U : ℤ) * n))) := by
    rw [← hζ, map_mul, map_pow, map_zpow₀, ho, ← hPO, hη, map_mul, map_pow, mul_pow, mul_zpow, ← zpow_natCast,
      ← zpow_mul, ← zpow_natCast (algebraMap O Kf ϖ) U, ← zpow_mul, mul_neg]
  have hA : (algebraMap O Kf (η : O)) ^ (-n) * (algebraMap O Kf (η : O)) ^ n = 1 := by
    rw [← zpow_add₀ hηK, neg_add_cancel, zpow_zero]
  have hB : algebraMap O Kf ϖ ^ (k * (E : ℤ)) * algebraMap O Kf ϖ ^ (-((U : ℤ) * n)) = algebraMap O Kf ϖ ^ (d + 1) := by
    rw [← zpow_add₀ hϖK, hdd, zpow_natCast]
  have h2 : algebraMap O Kf (ζ : O) * (algebraMap O Kf (η : O)) ^ n = algebraMap O Kf ϖ ^ (d + 1) * algebraMap O Kf o ^ E := by
    calc algebraMap O Kf (ζ : O) * (algebraMap O Kf (η : O)) ^ n
        = (algebraMap O Kf ϖ ^ (k * (E : ℤ)) * algebraMap O Kf ϖ ^ (-((U : ℤ) * n))) * algebraMap O Kf o ^ E *
            ((algebraMap O Kf (η : O)) ^ (-n) * (algebraMap O Kf (η : O)) ^ n) := by rw [h1]; ring
      _ = _ := by rw [hA, hB, mul_one]
  have h3 : ((ζ * η ^ n : Oˣ) : O) = ϖ * (ϖ ^ d * o ^ E) := by
    apply hinj
    rw [Units.val_mul, map_mul, algebraMap_unit_zpow, h2, map_mul, map_mul, map_pow, map_pow, pow_succ]
    ring
  exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (h3 ▸ (ζ * η ^ n).isUnit))

end Scalar

section Free

variable {LL V : Type} [Field LL] [AddCommGroup V] [Module LL V]

theorem free_gen (A : Subring LL) (val : AddValuation LL (WithTop ℤ)) (hval : ∀ a, a ∈ A ↔ 0 ≤ val a)
    (S0 : Finset V) (hspan : Submodule.span LL (S0 : Set V) = ⊤) :
    ∃ (ι : Type) (b : Module.Basis ι LL V), Submodule.span A (S0 : Set V) = Submodule.span A (Set.range b) := by
  classical
  have hex : ∃ n, ∃ S : Finset V, S.card = n ∧ Submodule.span A (S : Set V) = Submodule.span A (S0 : Set V) :=
    ⟨S0.card, S0, rfl, rfl⟩
  obtain ⟨S, hcard, hS⟩ := Nat.find_spec hex
  have hmin := fun k (hk : k < Nat.find hex) => Nat.find_min hex hk
  have hli : LinearIndependent LL (fun x : S => (x : V)) := by
    by_contra hnot
    obtain ⟨g, hg, i1, hi1⟩ := Fintype.not_linearIndependent_iff.1 hnot
    have hne : (Finset.univ.filter fun i : S => g i ≠ 0).Nonempty := ⟨i1, by simp [hi1]⟩
    obtain ⟨i0, hi0, hmin0⟩ := Finset.exists_min_image _ (fun i => val (g i)) hne
    have h0 : g i0 ≠ 0 := (Finset.mem_filter.1 hi0).2
    have hc : ∀ i, -((g i0)⁻¹ * g i) ∈ A := by
      intro i
      apply A.neg_mem
      by_cases hgi : g i = 0
      · rw [hgi, mul_zero]; exact A.zero_mem
      · exact (hval _).2 (val_quot_nonneg val h0 (hmin0 i (by simp [hgi])))
    have hsum : g i0 • (i0 : V) + ∑ i ∈ Finset.univ.erase i0, g i • (i : V) = 0 := by
      rw [Finset.add_sum_erase _ (fun i : S => g i • (i : V)) (Finset.mem_univ i0)]
      exact hg
    have hx : (i0 : V) = ∑ i ∈ Finset.univ.erase i0, (-((g i0)⁻¹ * g i)) • (i : V) := by
      have h1 : g i0 • (i0 : V) = -∑ i ∈ Finset.univ.erase i0, g i • (i : V) := eq_neg_of_add_eq_zero_left hsum
      have h2 : (i0 : V) = (g i0)⁻¹ • (g i0 • (i0 : V)) := by rw [smul_smul, inv_mul_cancel₀ h0, one_smul]
      rw [h2, h1, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, neg_smul]
    have hmem' : ∑ i ∈ Finset.univ.erase i0, (-((g i0)⁻¹ * g i)) • (i : V) ∈
        Submodule.span A ((S.erase (i0 : V) : Finset V) : Set V) := by
      refine Submodule.sum_mem _ fun i hi => ?_
      refine Submodule.smul_mem (Submodule.span A ((S.erase (i0 : V) : Finset V) : Set V)) ⟨_, hc i⟩
        (Submodule.subset_span ?_)
      rw [Finset.mem_coe, Finset.mem_erase]
      exact ⟨fun h => (Finset.mem_erase.1 hi).1 (Subtype.ext h), i.2⟩
    have hmem : (i0 : V) ∈ Submodule.span A ((S.erase (i0 : V) : Finset V) : Set V) := by
      rwa [← hx] at hmem'
    have heq : Submodule.span A ((S.erase (i0 : V) : Finset V) : Set V) = Submodule.span A (S : Set V) := by
      apply le_antisymm
      · exact Submodule.span_mono (by exact_mod_cast Finset.erase_subset _ _)
      · rw [Submodule.span_le]
        intro x hx'
        by_cases hxi : x = (i0 : V)
        · rw [hxi]; exact hmem
        · exact Submodule.subset_span (by rw [Finset.mem_coe, Finset.mem_erase]; exact ⟨hxi, hx'⟩)
    have hlt : (S.erase (i0 : V)).card < Nat.find hex := by
      rw [← hcard]
      exact Finset.card_erase_lt_of_mem i0.2
    exact hmin _ hlt ⟨S.erase (i0 : V), rfl, heq.trans hS⟩
  have hle : ∀ x ∈ Submodule.span A (S : Set V), x ∈ Submodule.span LL (S : Set V) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span hz
    | zero => exact Submodule.zero_mem _
    | add y z _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
    | smul a y _ h1 => exact Submodule.smul_mem _ (a : LL) h1
  have htop : ⊤ ≤ Submodule.span LL (Set.range fun x : S => (x : V)) := by
    rw [Subtype.range_coe_subtype, ← hspan, Submodule.span_le]
    intro x hx
    exact hle x (by rw [hS]; exact Submodule.subset_span hx)
  refine ⟨S, Module.Basis.mk hli htop, ?_⟩
  rw [Module.Basis.coe_mk, Subtype.range_coe_subtype, ← hS]
  rfl

end Free

section Rec

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

theorem valScalar_of (hinj : Function.Injective (algebraMap (D.gat u w h).O (D.gat u w h).Kf)) : ValScalar c u w h := by
  intro a s ϖ ha hϖ ho
  obtain ⟨o, ho⟩ := ho
  exact valScalar_gen hinj (c.embW u w h) (D.what₂.places.val w) (c.embW_int u w h) (D.what₂.places.resChar w)
    (D.what₂.places.ramIdx w) (D.what₂.places.ramIdx_pos w) (D.what₂.places.val_resChar w) a _ (D.val_eq w a ha) s ϖ hϖ o ho

theorem valScalar_of_place (v : Fin (D.gat u w h).P.nV) : ValScalar c u w h :=
  valScalar_of c u w h (haveI := ((D.gat u w h).P.setting v).frac_O; IsFractionRing.injective _ _)

theorem locFree (j : ℕ) : LocFree Tw u μ w j := by
  obtain ⟨S0, hS0⟩ := ((Tw.fm u μ).lat_good j).2.1
  have hO : ∀ r : 𝓞 D.what₂.LL, (r : D.what₂.LL) ∈ Formalism.BasicNotions.intW D.what₂.places w := fun r =>
    (D.val_nonneg_iff w _).2 ((D.plEq w).valuation_le_one r)
  have h1 : Formalism.BasicNotions.locW D.what₂.places w ((Tw.fm u μ).lat j).L =
      Submodule.span (Formalism.BasicNotions.intW D.what₂.places w) (S0 : Set ((Tw.fm u μ).lat j).V) := by
    unfold Formalism.BasicNotions.locW
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      rw [SetLike.mem_coe, ← hS0] at hx
      show x ∈ _
      induction hx using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span hz
      | zero => exact Submodule.zero_mem _
      | add y z _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
      | smul r y _ h1 =>
        have : r • y = (⟨(r : D.what₂.LL), hO r⟩ : Formalism.BasicNotions.intW D.what₂.places w) • y :=
          (algebraMap_smul D.what₂.LL r y).symm
        rw [this]
        exact Submodule.smul_mem _ _ h1
    · apply Submodule.span_mono
      intro x hx
      rw [SetLike.mem_coe, ← hS0]
      exact Submodule.subset_span hx
  have h2 : Submodule.span D.what₂.LL (S0 : Set ((Tw.fm u μ).lat j).V) = ⊤ := by
    rw [eq_top_iff, ← ((Tw.fm u μ).lat_good j).2.2, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, ← hS0] at hx
    show x ∈ _
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span hz
    | zero => exact Submodule.zero_mem _
    | add y z _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
    | smul r y _ h1 =>
      rw [← algebraMap_smul D.what₂.LL r y]
      exact Submodule.smul_mem _ _ h1
  obtain ⟨ι, b, hb⟩ := free_gen (Formalism.BasicNotions.intW D.what₂.places w) (D.what₂.places.val w) (fun _ => Iff.rfl) S0 h2
  exact ⟨ι, b, h1.trans hb⟩

end Rec

end Formalism.MainNotions.G.CmpJ

end
