import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.QALetterNe
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Imports

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYAc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem int_of_bd (W : LocWach PD LL O v n)
    (hH4 : ∀ r : ℕ, ((r + padicValNat PD.p r.factorial : ℕ) : ℚ) ≤ r * PD.p / ((PD.p : ℚ) - 1))
    (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    {r a : ℕ} {s : LL} (hs : Formalism.MainNotions.LiftingTheory.Bd W r s) (ha : (r : ℚ) * PD.p / ((PD.p : ℚ) - 1) ≤ a) :
    ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ a * s := by
  have hc : (((r + padicValNat PD.p r.factorial : ℕ) : ℚ)) ≤ a := (hH4 r).trans ha
  apply hOv
  rw [AddValuation.map_mul, Formalism.MainNotions.LiftingTheory.tr_v_pow W a]
  unfold Formalism.MainNotions.LiftingTheory.Bd at hs
  by_cases htop : v s = ⊤
  · rw [htop, WithTop.add_top]
    exact le_top
  · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hq] at hs ⊢
    have hq' : -((r + padicValNat PD.p r.factorial : ℕ) : ℚ) ≤ q := WithTop.coe_le_coe.mp hs
    rw [← WithTop.coe_add, ← WithTop.coe_zero]
    exact WithTop.coe_le_coe.mpr (by linarith)

theorem smulA_mem (W : LocWach PD LL O v n) {T : LocLat G Qp LL O} {i : ZMod n} {a : LetA O n}
    (ha : a ∈ W.AΔ) {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) : Formalism.MainNotions.LiftingTheory.InNΔi W T i (a • x) := by
  exact ⟨Formalism.MainNotions.LiftingTheory.invariant_smul_mem_invariants' W T a ha x hx.1, (W.Nl T i).smul_mem a hx.2⟩

theorem smulO_mem (W : LocWach PD LL O v n) {T : LocLat G Qp LL O} {i : ZMod n} (a : O)
    {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) : Formalism.MainNotions.LiftingTheory.InNΔi W T i (a • x) := by
  exact ⟨(W.NΔ T).smul_mem a hx.1, ((W.Nl T i).restrictScalars O).smul_mem a hx.2⟩

theorem sum_mem' (W : LocWach PD LL O v n) {T : LocLat G Qp LL O} {i : ZMod n} {ι : Type*} (s : Finset ι)
    (f : ι → W.DD T) (hf : ∀ j ∈ s, Formalism.MainNotions.LiftingTheory.InNΔi W T i (f j)) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T i (∑ j ∈ s, f j) := by
  exact ⟨(W.NΔ T).sum_mem fun j hj => (hf j hj).1, (W.Nl T i).sum_mem fun j hj => (hf j hj).2⟩

theorem build [IsDomain O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    {T : LocLat G Qp LL O} (hT : IsCrys PD T.ρ) (i : ZMod n) {d : ℕ} (b₁ : Fin d → W.DD T)
    (sol₁ : Fin d → ℕ → Fin d → LL) (hb₁ : IsHor W T i b₁ sol₁) (n₁ : W.DD T)
    (hn₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T i n₁) (Bq : ℕ) (hBq : 1 ≤ Bq) (hl5 : 5 ≤ PD.p) :
    ∃ (c₀ : Fin d → O) (z₁ : W.DD T) (R₀ σ₁ κ₁ : ℕ) (yy : ℕ → Fin d → O) (X₁ x₁ y₁ Z : W.DD T),
      Formalism.MainNotions.LiftingTheory.InNΔi W T i z₁ ∧ n₁ = Formalism.MainNotions.LiftingTheory.vecB W T b₁ c₀ + W.π₀ • z₁ ∧
      Bq ≤ (PD.p - 1) * R₀ ∧ 1 ≤ R₀ ∧ ((σ₁ : ℝ) ≤ (Bq : ℝ) / ((PD.p : ℝ) - 1) + 1) ∧
      (∀ r < R₀, ∀ m, algebraMap O LL (yy r m) = (PD.p : LL) ^ κ₁ * ∑ k, algebraMap O LL (c₀ k) * sol₁ k r m) ∧
      X₁ = ∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b₁ (yy r) ∧
      Formalism.MainNotions.LiftingTheory.InNΔi W T i X₁ ∧ Formalism.MainNotions.LiftingTheory.InNΔi W T i x₁ ∧ W.γ T X₁ - X₁ = W.π₀ ^ R₀ • x₁ ∧
      InFP W T i 1 1 y₁ ∧ InFP W T i 1 1 Z ∧
      lA W ^ κ₁ • y₁ + (W.π₀ * qA W ^ Bq) • Z = lA W ^ σ₁ • W.φD T X₁ := by
  classical
  obtain ⟨c₀, z₁, hz₁, hn₁eq⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.DYAa.coord_mod hR hb₁.1 hn₁
  obtain ⟨-, -, -, hH4, hH5⟩ := hH hcase T hT i
  have hBd : ∀ k r m, Formalism.MainNotions.LiftingTheory.Bd W r (sol₁ k r m) := (hH5 d b₁ hb₁.1 sol₁ hb₁.2).1
  have hp5 : (5 : ℝ) ≤ PD.p := by exact_mod_cast hl5
  have hp5q : (5 : ℚ) ≤ PD.p := by exact_mod_cast hl5

  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℕ, R₀ = ⌈(Bq : ℝ) / ((PD.p : ℝ) - 1)⌉₊ := ⟨_, rfl⟩
  have hR₀le : (Bq : ℝ) / ((PD.p : ℝ) - 1) ≤ R₀ := hR₀ ▸ Nat.le_ceil _
  have hR₀lt : (R₀ : ℝ) < (Bq : ℝ) / ((PD.p : ℝ) - 1) + 1 := hR₀ ▸ Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg _) (by linarith))
  have hBqR : (1 : ℝ) ≤ Bq := by exact_mod_cast hBq
  have hBR' : (Bq : ℝ) ≤ ((PD.p : ℝ) - 1) * R₀ := by
    rw [div_le_iff₀ (by linarith)] at hR₀le; linarith
  have hBR : Bq ≤ (PD.p - 1) * R₀ := by
    have h2 : ((PD.p - 1 : ℕ) : ℝ) = (PD.p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have : (Bq : ℝ) ≤ ((PD.p - 1 : ℕ) : ℝ) * (R₀ : ℝ) := by rw [h2]; exact hBR'
    exact_mod_cast this
  have hR1 : 1 ≤ R₀ := by
    rcases Nat.eq_zero_or_pos R₀ with h0 | h0
    · rw [h0] at hBR'; simp at hBR'; linarith
    · exact h0

  have hys : ∀ k r m, r < R₀ → ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ (2 * R₀) * sol₁ k r m := by
    intro k r m hr
    apply int_of_bd W hH4 hOv (hBd k r m)
    have hr' : (r : ℚ) + 1 ≤ R₀ := by exact_mod_cast hr
    rw [div_le_iff₀ (by linarith)]
    push_cast
    have h1 : (r : ℚ) * PD.p ≤ R₀ * PD.p := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : (0 : ℚ) ≤ R₀ * (PD.p - 2) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  choose! ys hys' using hys
  set yy : ℕ → Fin d → O := fun r m => ∑ k, c₀ k * ys k r m with hyydef
  have hyy : ∀ r < R₀, ∀ m, algebraMap O LL (yy r m) =
      (PD.p : LL) ^ (2 * R₀) * ∑ k, algebraMap O LL (c₀ k) * sol₁ k r m := by
    intro r hr m
    simp only [hyydef, map_sum, map_mul, hys' _ _ _ hr, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hyy0 : ∀ m, yy 0 m = (PD.p : O) ^ (2 * R₀) * c₀ m := by
    intro m
    apply hinj
    rw [hyy 0 (by omega) m, map_mul, map_pow, map_natCast]
    congr 1
    simp [(hb₁.2 _).2, Pi.single_apply]

  have hX : ∀ k, ∃ x, Formalism.MainNotions.LiftingTheory.InNΔi W T i x ∧
      W.γ T (∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b₁ (ys k r)) -
        (∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b₁ (ys k r)) = W.π₀ ^ R₀ • x := by
    intro k
    obtain ⟨x, hx, hxe⟩ := (hb₁.2 k).1 R₀ (2 * R₀) (ys k) (fun r hr m => hys' k r m hr)
    exact ⟨x, hx, by rw [← hxe, smul_zero, sub_zero]⟩
  choose xk hxk hxke using hX
  have hvec : ∀ y, Formalism.MainNotions.LiftingTheory.InNΔi W T i (Formalism.MainNotions.LiftingTheory.vecB W T b₁ y) := fun y =>
    sum_mem' W _ _ fun m _ => smulO_mem W _ (hb₁.1.1 m)
  have hπ₀ := Formalism.MainNotions.N.FrobeniusPowerSeries.GS.π₀_mem W
  have hq := Formalism.MainNotions.N.FrobeniusPowerSeries.GS.qA_mem W
  have hXeq : ∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b₁ (yy r) =
      ∑ k, c₀ k • ∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b₁ (ys k r) := by
    simp only [Formalism.MainNotions.LiftingTheory.vecB, hyydef, Finset.smul_sum, Finset.sum_smul]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul]
    exact smul_comm _ _ _
  obtain ⟨wv, hwA, -, hw⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.DYAa.w_mem hR
  have hLA : lA W ∈ W.AΔ := by
    show ((PD.p : ℕ) : LetA O n) ∈ W.AΔ
    exact Subalgebra.natCast_mem _ _
  have hLc : ∀ j : ℕ, algebraMap O (LetA O n) ((PD.p : O) ^ j) = lA W ^ j := by
    intro j; rw [map_pow, map_natCast]; rfl

  have hos : ∀ r' k m, r' + 1 < R₀ → k ≤ r' → k + (PD.p - 1) * (r' + 1) < Bq →
      ∃ o : O, o * (PD.p : O) ^ (2 * R₀) = (PD.p : O) ^ (R₀ + (r' - k)) * yy (r' + 1) m := by
    intro r' k m hr hk hkB
    have hint : ∀ k', ∃ o' : O, algebraMap O LL o' = (PD.p : LL) ^ (R₀ + (r' - k)) * sol₁ k' (r' + 1) m := by
      intro k'
      apply int_of_bd W hH4 hOv (hBd k' (r' + 1) m)
      have he : ((PD.p - 1 : ℕ) : ℚ) = (PD.p : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      have hkB' : (k : ℚ) + ((PD.p : ℚ) - 1) * (r' + 1) + 1 ≤ Bq := by
        have : (k + (PD.p - 1) * (r' + 1) + 1 : ℕ) ≤ Bq := hkB
        have := (Nat.cast_le (α := ℚ)).2 this
        push_cast [he] at this
        linarith
      have hBRq : (Bq : ℚ) ≤ ((PD.p : ℚ) - 1) * R₀ := by exact_mod_cast hBR'
      have hkr : (k : ℚ) ≤ r' := by exact_mod_cast hk
      have hsub : (((r' - k : ℕ)) : ℚ) = r' - k := by rw [Nat.cast_sub hk]
      rw [div_le_iff₀ (by linarith)]
      push_cast [hsub]
      nlinarith [mul_nonneg (show (0:ℚ) ≤ (PD.p : ℚ) - 2 by linarith) (show (0:ℚ) ≤ r' - k by linarith)]
    choose o' ho' using hint
    refine ⟨∑ k', c₀ k' * o' k', hinj ?_⟩
    simp only [map_mul, map_pow, map_natCast, map_sum, ho', hyydef, hys' _ _ _ hr, Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun k' _ => by ring
  choose! o ho using hos

  set e := PD.p - 1 with he
  set L := lA W with hL
  set cO := algebraMap O (LetA O n) with hcO
  obtain ⟨Y, hYdef⟩ : ∃ Y : Fin d → LetA O n, Y = fun m => cO ((PD.p : O) ^ R₀ * c₀ m) +
    ∑ r' ∈ Finset.range (R₀ - 1), wv ^ (r' + 1) *
      ∑ k ∈ (Finset.range (r' + 1)).filter (fun k => k + e * (r' + 1) < Bq),
        (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * W.π₀ * qA W ^ (k + e * (r' + 1)) *
          cO (o r' k m) := ⟨_, rfl⟩
  obtain ⟨Zc, hZdef⟩ : ∃ Zc : Fin d → LetA O n, Zc = fun m =>
    ∑ r' ∈ Finset.range (R₀ - 1), wv ^ (r' + 1) * cO ((PD.p : O) ^ R₀ * yy (r' + 1) m) *
      ∑ k ∈ (Finset.range (r' + 1)).filter (fun k => ¬ k + e * (r' + 1) < Bq),
        (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * L ^ (r' - k) *
          qA W ^ (k + e * (r' + 1) - Bq) := ⟨_, rfl⟩
  have hY : ∀ m, Y m ∈ W.AΔ := by
    intro m
    rw [hYdef]
    refine add_mem (Subalgebra.algebraMap_mem _ _) (sum_mem fun r' _ => mul_mem (pow_mem hwA _)
      (sum_mem fun k _ => mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _)
        (Subalgebra.natCast_mem _ _)) hπ₀) (pow_mem hq _)) (Subalgebra.algebraMap_mem _ _)))
  have hZ : ∀ m, Zc m ∈ W.AΔ := by
    intro m
    rw [hZdef]
    refine sum_mem fun r' _ => mul_mem (mul_mem (pow_mem hwA _) (Subalgebra.algebraMap_mem _ _))
      (sum_mem fun k _ => mul_mem (mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _)
        (Subalgebra.natCast_mem _ _)) (pow_mem hLA _)) (pow_mem hq _))

  have hterm : ∀ r' ∈ Finset.range (R₀ - 1), ∀ m,
      L ^ R₀ * ((W.φA W.π₀) ^ (r' + 1) * cO (yy (r' + 1) m)) =
        L ^ (2 * R₀) * (wv ^ (r' + 1) *
          ∑ k ∈ (Finset.range (r' + 1)).filter (fun k => k + e * (r' + 1) < Bq),
            (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * W.π₀ * qA W ^ (k + e * (r' + 1)) *
              cO (o r' k m)) +
        (W.π₀ * qA W ^ Bq) * (wv ^ (r' + 1) * cO ((PD.p : O) ^ R₀ * yy (r' + 1) m) *
          ∑ k ∈ (Finset.range (r' + 1)).filter (fun k => ¬ k + e * (r' + 1) < Bq),
            (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * L ^ (r' - k) *
              qA W ^ (k + e * (r' + 1) - Bq)) := by
    intro r' hr' m
    have hr'' : r' + 1 < R₀ := by simp only [Finset.mem_range] at hr'; omega
    have e1 : (wv * W.π₀ * qA W ^ e) ^ (r' + 1) =
        wv ^ (r' + 1) * (W.π₀ ^ (r' + 1) * qA W ^ (e * (r' + 1))) := by
      rw [mul_pow, mul_pow, ← pow_mul]; ring
    have hsplit := Formalism.MainNotions.N.FrobeniusPowerSeries.DYAb.split W.π₀ (qA W) L rfl e Bq r'
    have hlow : L ^ R₀ * wv ^ (r' + 1) * cO (yy (r' + 1) m) *
        (∑ k ∈ (Finset.range (r' + 1)).filter (fun k => k + e * (r' + 1) < Bq),
          (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * L ^ (r' - k) * W.π₀ *
            qA W ^ (k + e * (r' + 1))) =
        L ^ (2 * R₀) * (wv ^ (r' + 1) *
          ∑ k ∈ (Finset.range (r' + 1)).filter (fun k => k + e * (r' + 1) < Bq),
            (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * W.π₀ * qA W ^ (k + e * (r' + 1)) *
              cO (o r' k m)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      have hoL := congrArg cO (ho r' k m hr'' (by omega) hk.2)
      simp only [map_mul, map_pow, map_natCast] at hoL
      have hLp : ((PD.p : ℕ) : LetA O n) = L := rfl
      rw [hLp] at hoL
      linear_combination (-(wv ^ (r' + 1) * (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) *
        W.π₀ * qA W ^ (k + e * (r' + 1)))) * hoL
    calc L ^ R₀ * ((W.φA W.π₀) ^ (r' + 1) * cO (yy (r' + 1) m))
        = L ^ R₀ * wv ^ (r' + 1) * cO (yy (r' + 1) m) *
            (∑ k ∈ (Finset.range (r' + 1)).filter (fun k => k + e * (r' + 1) < Bq),
              (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * L ^ (r' - k) * W.π₀ *
                qA W ^ (k + e * (r' + 1))) +
          (W.π₀ * qA W ^ Bq) * (L ^ R₀ * wv ^ (r' + 1) * cO (yy (r' + 1) m) *
            ∑ k ∈ (Finset.range (r' + 1)).filter (fun k => ¬ k + e * (r' + 1) < Bq),
              (-1 : LetA O n) ^ (r' - k) * (r'.choose k : LetA O n) * L ^ (r' - k) *
                qA W ^ (k + e * (r' + 1) - Bq)) := by
          rw [hw, e1, hsplit]; ring
      _ = _ := by
          rw [hlow, map_mul, hLc]
          ring
  have hid : ∀ m, L ^ (2 * R₀) * Y m + (W.π₀ * qA W ^ Bq) * Zc m =
      L ^ R₀ * ∑ r ∈ Finset.range R₀, (W.φA W.π₀) ^ r * cO (yy r m) := by
    intro m
    rw [show Finset.range R₀ = Finset.range ((R₀ - 1) + 1) by rw [Nat.sub_add_cancel hR1],
      Finset.sum_range_succ', pow_zero, one_mul, hyy0, mul_add, Finset.mul_sum,
      Finset.sum_congr rfl fun r' hr' => hterm r' hr' m, Finset.sum_add_distrib, hYdef, hZdef]
    simp only [mul_add, Finset.mul_sum, map_mul, hLc]
    ring

  refine ⟨c₀, z₁, R₀, R₀, 2 * R₀, yy,
    ∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b₁ (yy r), ∑ k, c₀ k • xk k,
    ∑ m, Y m • W.φD T (b₁ m), ∑ m, Zc m • W.φD T (b₁ m),
    hz₁, hn₁eq, hBR, hR1, hR₀lt.le, hyy, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sum_mem' W _ _ fun r _ => smulA_mem W (pow_mem hπ₀ r) (hvec _)
  · exact sum_mem' W _ _ fun k _ => smulO_mem W _ (hxk k)
  · rw [hXeq, map_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, ← smul_sub, hxke k]
    exact smul_comm _ _ _
  · refine ⟨_, AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure
      ⟨Y m, hY m, b₁ m, hb₁.1.1 m, by rw [pow_one]⟩, by rw [one_smul]⟩
  · refine ⟨_, AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure
      ⟨Zc m, hZ m, b₁ m, hb₁.1.1 m, by rw [pow_one]⟩, by rw [one_smul]⟩
  · have hφX : W.φD T (∑ r ∈ Finset.range R₀, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b₁ (yy r)) =
        ∑ m, (∑ r ∈ Finset.range R₀, (W.φA W.π₀) ^ r * cO (yy r m)) • W.φD T (b₁ m) := by
      simp only [map_sum, Formalism.MainNotions.N.FrobeniusPowerSeries.DYAa.phi_smul, Formalism.MainNotions.LiftingTheory.vecB, map_pow, map_smul,
        Finset.smul_sum, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_
      rw [← algebraMap_smul (LetA O n) (yy r m), smul_smul]
    rw [hφX, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul, smul_smul, smul_smul, ← add_smul, hid m]

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYAc
