import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEuclideanSections
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLatticeCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallBallVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics Module

noncomputable section

section Bounded

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ : ℕ} {s : Ω}

theorem IsBoundedH.mono {c c' : ℝ} (hs : IsBoundedH P y A τ c s) (hc : c ≤ c') :
    IsBoundedH P y A τ c' s := by
  intro dg dh g h z hg hh hd he hz
  refine (hs dg dh g h z hg hh hd he hz).trans ?_
  have h0 : 0 ≤ A.h z ^ τ := pow_nonneg (A.pos z hz.1).le τ
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (norm_nonneg (eval z (map (Int.castRingHom ℂ) h)))) h0

theorem IsSmallH.isBoundedH_one (hs : IsSmallH P y A τ s) : IsBoundedH P y A τ 1 s := by
  intro dg dh g h z hg hh hd he hz
  simpa [one_mul] using hs dg dh g h z hg hh hd he hz

end Bounded

section Count

variable {r : ℕ}

theorem exists_shortLatticeBasis (L : Submodule ℤ (EuclideanSpace ℝ (Fin r))) [DiscreteTopology L]
    [IsZLattice ℝ L] (S : Set (EuclideanSpace ℝ (Fin r))) (hSL : S ⊆ L)
    (hLS : (L : Set (EuclideanSpace ℝ (Fin r))) ⊆ Submodule.span ℝ S) {c : ℝ} (hc : ∀ v ∈ S, ‖v‖ ≤ c) :
    Nonempty (ShortLatticeBasis L c) := by
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℝ S
  have htop : Submodule.span ℝ b = ⊤ := by
    rw [hspan, eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := L)]
    exact Submodule.span_le.2 hLS
  let bb : Basis b ℝ (EuclideanSpace ℝ (Fin r)) :=
    Basis.mk hli (by rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, htop])
  let e : b ≃ Fin (finrank ℝ (EuclideanSpace ℝ (Fin r))) := bb.indexEquiv (finBasis ℝ _)
  exact ⟨{ vec := fun i => ((e.symm i : b) : EuclideanSpace ℝ (Fin r))
           mem := fun i => hSL (hbS (e.symm i).2)
           linearIndependent := hli.comp e.symm e.symm.injective
           norm_le := fun i => hc _ (hbS (e.symm i).2) }⟩

theorem log_ncard_ball_le (L : Submodule ℤ (EuclideanSpace ℝ (Fin r))) [DiscreteTopology L] [IsZLattice ℝ L]
    {c : ℝ} (hc : 0 ≤ c) (B : ShortLatticeBasis L c) :
    {x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.Finite ∧
      Real.log ({x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.ncard : ℝ) ≤
        Real.log 6 + r * Real.log (1 + r * c) - Real.log (ZLattice.covolume L) := by
  obtain ⟨hfin, hcount⟩ := LatticeCount.proof (EuclideanSpace ℝ (Fin r)) L c 1 B zero_le_one
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin r)) = r := finrank_euclideanSpace_fin
  rw [hdim] at hcount
  have hV := SmallBallVolume.proof r
  have hN1 : (1 : ℝ) ≤ ({x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.ncard : ℝ) := by
    have : 0 < {x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.ncard :=
      (Set.ncard_pos hfin).2 ⟨0, L.zero_mem, by simp⟩
    exact_mod_cast this
  have hcov := ZLattice.covolume_pos L
  have hq : 0 < (1 + (r : ℝ) * c) ^ r := by positivity
  refine ⟨hfin, ?_⟩
  have h1 : ({x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.ncard : ℝ) ≤ 6 * (1 + (r : ℝ) * c) ^ r / ZLattice.covolume L := by
    rw [le_div_iff₀ hcov]
    calc _ ≤ unitBallVolume r * (1 + (r : ℝ) * c) ^ r := hcount
      _ ≤ 6 * (1 + (r : ℝ) * c) ^ r := mul_le_mul_of_nonneg_right hV hq.le
  calc _ ≤ Real.log (6 * (1 + (r : ℝ) * c) ^ r / ZLattice.covolume L) :=
        Real.log_le_log (by linarith) h1
    _ = _ := by
      rw [Real.log_div (by positivity) hcov.ne', Real.log_mul (by norm_num) hq.ne', Real.log_pow]

theorem log_card_le_of_injective {α : Type*} {V : Type*} [NormedAddCommGroup V] [Module ℤ V]
    (L : Submodule ℤ V) (f : α → V) (hf : Function.Injective f) (hmem : ∀ a, f a ∈ L ∧ ‖f a‖ ≤ 1)
    (hfin : {x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.Finite) :
    Real.log (Nat.card α) ≤ Real.log ({x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.ncard : ℝ) := by
  have hle : Nat.card α ≤ {x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.ncard := by
    have := hfin.to_subtype
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective (fun a => ⟨f a, hmem a⟩)
      (fun a b h => hf (congrArg Subtype.val h))
  have hpos : 0 < {x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.ncard :=
    (Set.ncard_pos hfin).2 ⟨0, L.zero_mem, by simp⟩
  rcases Nat.eq_zero_or_pos (Nat.card α) with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_nonneg (by exact_mod_cast hpos)
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hle)

end Count

section Asymptotics

theorem isBigO_natCast_add_one :
    (fun n : ℕ => (n : ℝ) + 1) =O[atTop] fun n : ℕ => (n : ℝ) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  linarith

theorem isLittleO_natCast_pow_pow {p q : ℕ} (h : p < q) :
    (fun n : ℕ => (n : ℝ) ^ p) =o[atTop] fun n : ℕ => (n : ℝ) ^ q :=
  (isLittleO_pow_pow_atTop_of_lt h).comp_tendsto tendsto_natCast_atTop_atTop

theorem eventually_error_le (D : ℕ) (C c : ℝ) (hc : 0 ≤ c) (r : ℕ → ℕ)
    (hr : ∀ n, (r n : ℝ) ≤ C * ((n : ℝ) + 1) ^ D) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.log 6 + (r n : ℝ) * Real.log (1 + r n * c) ≤
      ε * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
  set C₀ := max C 0 with hC₀
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  set k := C₀ * c with hk
  have hk0 : 0 ≤ k := mul_nonneg hC₀0 hc

  have hbound : ∀ n : ℕ, (r n : ℝ) * Real.log (1 + r n * c) ≤
      C₀ * ((n : ℝ) + 1) ^ D * (Real.log (1 + k) + D * Real.log ((n : ℝ) + 1)) := by
    intro n
    have hm1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ D := one_le_pow₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    have hrn : (r n : ℝ) ≤ C₀ * ((n : ℝ) + 1) ^ D :=
      (hr n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hlog0 : 0 ≤ Real.log (1 + r n * c) := Real.log_nonneg (by nlinarith [(r n).cast_nonneg (α := ℝ)])
    have hlog : Real.log (1 + r n * c) ≤ Real.log (1 + k) + D * Real.log ((n : ℝ) + 1) := by
      have h1 : 1 + (r n : ℝ) * c ≤ (1 + k) * ((n : ℝ) + 1) ^ D := by
        have : (r n : ℝ) * c ≤ k * ((n : ℝ) + 1) ^ D := by
          rw [hk, mul_assoc, mul_comm c, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right hrn hc
        nlinarith
      calc Real.log (1 + r n * c) ≤ Real.log ((1 + k) * ((n : ℝ) + 1) ^ D) :=
            Real.log_le_log (by nlinarith [(r n).cast_nonneg (α := ℝ)]) h1
        _ = _ := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    calc (r n : ℝ) * Real.log (1 + r n * c) ≤ C₀ * ((n : ℝ) + 1) ^ D * Real.log (1 + r n * c) :=
          mul_le_mul_of_nonneg_right hrn hlog0
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)

  have hpow : (fun n : ℕ => ((n : ℝ) + 1) ^ D) =O[atTop] fun n : ℕ => (n : ℝ) ^ D :=
    isBigO_natCast_add_one.pow D
  have h1 : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
    simpa using isLittleO_natCast_pow_pow (p := 0) (q := D + 1) (Nat.succ_pos D)
  have h2 : (fun n : ℕ => ((n : ℝ) + 1) ^ D) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) :=
    hpow.trans_isLittleO (isLittleO_natCast_pow_pow (Nat.lt_succ_self D))
  have hlogn : (fun n : ℕ => Real.log ((n : ℝ) + 1)) =o[atTop] fun n : ℕ => (n : ℝ) := by
    have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact (Real.isLittleO_log_id_atTop.comp_tendsto ht).trans_isBigO isBigO_natCast_add_one
  have h3 : (fun n : ℕ => ((n : ℝ) + 1) ^ D * Real.log ((n : ℝ) + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
    have := hpow.mul_isLittleO hlogn
    refine this.congr_right ?_
    intro n
    rw [pow_succ]
  have hB : (fun n : ℕ => Real.log 6 +
      C₀ * ((n : ℝ) + 1) ^ D * (Real.log (1 + k) + D * Real.log ((n : ℝ) + 1))) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
    have := (h1.const_mul_left (Real.log 6)).add
      ((h2.const_mul_left (C₀ * Real.log (1 + k))).add (h3.const_mul_left (C₀ * D)))
    refine this.congr_left ?_
    intro n
    ring
  have hF : (0 : ℝ) < ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  filter_upwards [hB.def (div_pos hε hF)] with n hn
  have hpos : 0 ≤ (n : ℝ) ^ (D + 1) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos] at hn
  calc Real.log 6 + (r n : ℝ) * Real.log (1 + r n * c)
      ≤ Real.log 6 + C₀ * ((n : ℝ) + 1) ^ D * (Real.log (1 + k) + D * Real.log ((n : ℝ) + 1)) := by
        linarith [hbound n]
    _ ≤ |Real.log 6 + C₀ * ((n : ℝ) + 1) ^ D * (Real.log (1 + k) + D * Real.log ((n : ℝ) + 1))| :=
        le_abs_self _
    _ ≤ ε / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1) := hn
    _ = ε * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by ring

end Asymptotics

theorem G7.proof (hG1 : SuccessiveMinimaSpan.Statement) (hE : EuclideanSections.Statement) : G7.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD hII har hb hA hc
  obtain ⟨r, φ, hinj, hdisc, hlat, hnorm, ⟨Cr, hr⟩, hdeg⟩ := hE K ι Ω y D A P0 II hD hII har hb hA hc
  obtain ⟨C, hC⟩ := hG1 K ι Ω y D A P0 hD har hb hA
  set c := max C 0 with hcdef
  have hc0 : 0 ≤ c := le_max_right _ _

  have key : ∀ n : ℕ, ∀ [DiscreteTopology (imageLattice (φ n))] [IsZLattice ℝ (imageLattice (φ n))],
      smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n ≤
        Real.log 6 + r n * Real.log (1 + r n * c) -
          Real.log (ZLattice.covolume (imageLattice (φ n))) := by
    intro n _ _

    have hle : AddSubgroup.closure
        {s | s ∈ chartLat y A.a n ∧ IsBoundedH (mCoordIdeal y) y A n C s} ≤ chartLat y A.a n :=
      (hC n).le
    have hsp : ∀ (t : Ω) (ht : t ∈ AddSubgroup.closure
        {s | s ∈ chartLat y A.a n ∧ IsBoundedH (mCoordIdeal y) y A n C s}),
        φ n ⟨t, hle ht⟩ ∈ Submodule.span ℝ
          (φ n '' {s : chartLat y A.a n | IsBoundedH (mCoordIdeal y) y A n c (s : Ω)}) := by
      intro t ht
      induction ht using AddSubgroup.closure_induction with
      | mem x hx =>
        exact Submodule.subset_span ⟨⟨x, hx.1⟩, hx.2.mono (le_max_left _ _), rfl⟩
      | zero =>
        have : (⟨0, hle (zero_mem _)⟩ : chartLat y A.a n) = 0 := rfl
        rw [this, map_zero]
        exact zero_mem _
      | add x z hx hz ihx ihz =>
        have : (⟨x + z, hle (add_mem hx hz)⟩ : chartLat y A.a n) = ⟨x, hle hx⟩ + ⟨z, hle hz⟩ := rfl
        rw [this, map_add]
        exact add_mem ihx ihz
      | neg x hx ihx =>
        have : (⟨-x, hle (neg_mem hx)⟩ : chartLat y A.a n) = -⟨x, hle hx⟩ := rfl
        rw [this, map_neg]
        exact neg_mem ihx
    obtain ⟨B⟩ := exists_shortLatticeBasis (imageLattice (φ n))
      (φ n '' {s : chartLat y A.a n | IsBoundedH (mCoordIdeal y) y A n c (s : Ω)})
      (by rintro _ ⟨s, -, rfl⟩; exact ⟨s, rfl⟩)
      (by
        rintro _ ⟨s, rfl⟩
        have hs : (s : Ω) ∈ AddSubgroup.closure
            {s | s ∈ chartLat y A.a n ∧ IsBoundedH (mCoordIdeal y) y A n C s} := by
          rw [hC n]; exact s.2
        exact hsp s hs)
      (by rintro _ ⟨s, hs, rfl⟩; exact hnorm n c s hc0 hs)
    obtain ⟨hfin, hlog⟩ := log_ncard_ball_le (imageLattice (φ n)) hc0 B
    refine le_trans ?_ hlog
    exact log_card_le_of_injective (imageLattice (φ n))
      (fun a : {s : chartLat y A.a n // IsSmallH (mCoordIdeal y) y A n (s : Ω)} => φ n a.1)
      (fun a b h => Subtype.val_injective (hinj n h))
      (fun a => ⟨⟨a.1, rfl⟩, hnorm n 1 a.1 zero_le_one (IsSmallH.isBoundedH_one a.2)⟩) hfin

  have hu0 : ∀ n : ℕ, 0 ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n /
      ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
    intro n
    apply div_nonneg _ (by positivity)
    exact Real.log_natCast_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine Filter.limsup_le_of_le (isCoboundedUnder_le_of_le atTop hu0) ?_
  filter_upwards [hdeg (ε / 2) (half_pos hε), eventually_error_le D Cr c hc0 r hr (half_pos hε),
    eventually_ge_atTop 1] with n h1 h2 hn
  have := hdisc n
  have : IsZLattice ℝ (imageLattice (φ n)) := hlat n
  have h1' : -Real.log (ZLattice.covolume (imageLattice (φ n))) ≤
      (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε / 2) *
        ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := h1
  have hk := key n
  have hN : 0 < (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  rw [div_le_iff₀ hN]
  nlinarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
