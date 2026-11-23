import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoversOfLifts
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CovTop.WtRun
open GlobalTheory.FlagTan (dimFlag)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem abs_ofGaps_le {N : ℕ} (a : ℕ) (g : ℕ → ℤ) (i : Fin N) :
    |(ofGaps a g : Fin N → ℤ) i| ≤ ∑ k ∈ Finset.range a, |g k| + ∑ k ∈ Finset.range (i : ℕ), |g k| := by
  unfold ofGaps
  exact (abs_sub _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _))

theorem abs_kap_le (τ : Psi H) (i : Fin (Dw.p + Dw.q)) : |FlagTan.kap Dw τ i| ≤ ((Dw.p + Dw.q : ℕ) : ℤ) := by
  have := i.2
  simp only [FlagTan.kap]
  split_ifs with h <;> rw [abs_le] <;> constructor <;> push_cast <;> omega

theorem abs_hodgeWt_le (τ : Psi H) (i : Fin (Dw.p + Dw.q)) : |hodgeWt Dw τ i| ≤ 1 := by
  simp only [hodgeWt, CompHt.barWt]
  split_ifs <;> simp

variable (P : WtPar Dw)

theorem T₁_pos : 0 < P.T₁ := by unfold WtPar.T₁; positivity

theorem abs_rem_le (ha : P.a ≤ Dw.p + Dw.q) (τ : Psi H) (i : Fin (Dw.p + Dw.q)) :
    |P.rem τ i| ≤ 2 * ((Dw.p + Dw.q : ℕ) : ℤ) * P.T₁ := by
  have hT := T₁_pos P
  have hg : ∀ k, |gap ((P.uMinus - FlagTan.kap Dw) τ) k - P.T₁ * (gap ((P.uMinus - FlagTan.kap Dw) τ) k / P.T₁)| ≤ P.T₁ := by
    intro k
    rw [← Int.emod_def, abs_of_nonneg (Int.emod_nonneg _ hT.ne')]
    exact (Int.emod_lt_of_pos _ hT).le
  have h := abs_ofGaps_le (N := Dw.p + Dw.q) P.a
    (fun k => gap ((P.uMinus - FlagTan.kap Dw) τ) k - P.T₁ * (gap ((P.uMinus - FlagTan.kap Dw) τ) k / P.T₁)) i
  have h1 := Finset.sum_le_card_nsmul (Finset.range P.a) _ _ (fun k _ => hg k)
  have h2 := Finset.sum_le_card_nsmul (Finset.range (i : ℕ)) _ _ (fun k _ => hg k)
  simp only [Finset.card_range, nsmul_eq_mul] at h1 h2
  have hi := i.2
  have h3 : ((P.a : ℕ) : ℤ) * P.T₁ + ((i : ℕ) : ℤ) * P.T₁ ≤ 2 * ((Dw.p + Dw.q : ℕ) : ℤ) * P.T₁ := by
    have : ((P.a : ℕ) : ℤ) + ((i : ℕ) : ℤ) ≤ 2 * ((Dw.p + Dw.q : ℕ) : ℤ) := by push_cast; omega
    nlinarith
  exact (h.trans (add_le_add h1 h2)).trans h3

theorem T₁_mul_u₁_add_rem (ha : P.a < Dw.p + Dw.q) (τ : Psi H) (i : Fin (Dw.p + Dw.q)) :
    P.T₁ * P.u₁ τ i + P.rem τ i = (P.uMinus - FlagTan.kap Dw) τ i - (P.uMinus - FlagTan.kap Dw) τ ⟨P.a, ha⟩ :=
  floorGaps_add_remGaps P.T₁ _ ⟨P.a, ha⟩ i

theorem wt_apply (j : ℕ) (τ : Psi H) (i : Fin (Dw.p + Dw.q)) :
    P.wt j τ i = FlagTan.kap Dw τ i + P.rem τ i + ((dimFlag Dw : ℤ) + j + 1) * P.u₁ τ i := by
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  ring

end GlobalTheory.CovTop.WtRun

namespace GlobalTheory.CovTop.WtRun
open GlobalTheory.FlagTan (dimFlag)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
variable (P : WtPar Dw)

theorem abs_wt_le (ha : P.a < Dw.p + Dw.q) {j : ℕ} (hj : j ≤ P.T) (la : AllWt.Weight Dw) (w : Psi H → ℤ)
    (hu : P.u = la - GlobalTheory.FlatLine.parWt Dw w) (τ : Psi H) (i : Fin (Dw.p + Dw.q)) :
    |P.wt j τ i| ≤ |la τ i| + |w τ| + |la τ ⟨P.a, ha⟩ - w τ| + 2 * |P.c₀| + 3 * ((Dw.p + Dw.q : ℕ) : ℤ) +
      4 * ((Dw.p + Dw.q : ℕ) : ℤ) * P.T₁ := by
  have e1 := wt_apply P j τ i
  have e2 := T₁_mul_u₁_add_rem P ha τ i
  have hr := abs_rem_le P ha.le τ i
  have hk := abs_kap_le τ i
  have hka := abs_kap_le τ ⟨P.a, ha⟩
  have hc : ∀ i', |P.c₀ * hodgeWt Dw τ i'| ≤ |P.c₀| := fun i' => by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_hodgeWt_le _ _)
  have hvi : (P.uMinus - FlagTan.kap Dw) τ i = la τ i - w τ - P.c₀ * hodgeWt Dw τ i - FlagTan.kap Dw τ i := by
    simp [WtPar.uMinus, hu, GlobalTheory.FlatLine.parWt]
  have hva : (P.uMinus - FlagTan.kap Dw) τ ⟨P.a, ha⟩ =
      (la τ ⟨P.a, ha⟩ - w τ) - P.c₀ * hodgeWt Dw τ ⟨P.a, ha⟩ - FlagTan.kap Dw τ ⟨P.a, ha⟩ := by
    simp [WtPar.uMinus, hu, GlobalTheory.FlatLine.parWt]
  have hm0 : (0 : ℤ) ≤ (dimFlag Dw : ℤ) + j + 1 := by positivity
  have hm1 : (dimFlag Dw : ℤ) + j + 1 ≤ P.T₁ := by unfold WtPar.T₁; push_cast; omega
  have h3 : |((dimFlag Dw : ℤ) + j + 1) * P.u₁ τ i| ≤ |P.T₁ * P.u₁ τ i| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (by rw [abs_of_nonneg hm0, abs_of_pos (T₁_pos P)]; exact hm1) (abs_nonneg _)
  have h4 : P.T₁ * P.u₁ τ i = (P.uMinus - FlagTan.kap Dw) τ i - (P.uMinus - FlagTan.kap Dw) τ ⟨P.a, ha⟩ - P.rem τ i := by
    linarith
  rw [h4, hvi, hva] at h3
  rw [e1]
  have a1 := abs_le.1 h3
  have a2 := abs_le.1 hr
  have a3 := abs_le.1 hk
  have a4 := abs_le.1 hka
  have a5 := abs_le.1 (hc i)
  have a6 := abs_le.1 (hc ⟨P.a, ha⟩)
  set X := ((dimFlag Dw : ℤ) + j + 1) * P.u₁ τ i
  have b1 : |la τ i - w τ - P.c₀ * hodgeWt Dw τ i - FlagTan.kap Dw τ i -
      (la τ ⟨P.a, ha⟩ - w τ - P.c₀ * hodgeWt Dw τ ⟨P.a, ha⟩ - FlagTan.kap Dw τ ⟨P.a, ha⟩) - P.rem τ i| ≤
      |la τ i| + |w τ| + |la τ ⟨P.a, ha⟩ - w τ| + 2 * |P.c₀| + 2 * ((Dw.p + Dw.q : ℕ) : ℤ) +
        2 * ((Dw.p + Dw.q : ℕ) : ℤ) * P.T₁ := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self (la τ i), neg_abs_le (la τ i), le_abs_self (w τ), neg_abs_le (w τ),
      le_abs_self (la τ ⟨P.a, ha⟩ - w τ), neg_abs_le (la τ ⟨P.a, ha⟩ - w τ)]
  have a7 := abs_le.1 (h3.trans b1)
  rw [abs_le]
  constructor <;> nlinarith [le_abs_self (la τ i), neg_abs_le (la τ i), le_abs_self (w τ), neg_abs_le (w τ),
      le_abs_self (la τ ⟨P.a, ha⟩ - w τ), neg_abs_le (la τ ⟨P.a, ha⟩ - w τ), T₁_pos P]

end GlobalTheory.CovTop.WtRun

namespace GlobalTheory.CovTop.WtRun
open GlobalTheory.FlagTan (dimFlag)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
variable (P : WtPar Dw)

theorem sum_abs_wt_le (ha : P.a < Dw.p + Dw.q) {j : ℕ} (hj : j ≤ P.T) (la : AllWt.Weight Dw) (w : Psi H → ℤ)
    (hu : P.u = la - GlobalTheory.FlatLine.parWt Dw w) (hw : ∀ τ, w τ = la τ ⟨P.a, ha⟩) :
    ∑ τ, ∑ i, |(P.wt j τ i : ℝ)| ≤ (((Dw.p + Dw.q : ℕ) : ℝ) + 1) * ∑ τ, ∑ i, |(la τ i : ℝ)| +
      (Fintype.card (Psi H) : ℝ) * (((Dw.p + Dw.q : ℕ) : ℝ) * (2 * |(P.c₀ : ℝ)| + 3 * ((Dw.p + Dw.q : ℕ) : ℝ) +
        4 * ((Dw.p + Dw.q : ℕ) : ℝ) * (P.T₁ : ℝ))) := by
  set K : ℝ := 2 * |(P.c₀ : ℝ)| + 3 * ((Dw.p + Dw.q : ℕ) : ℝ) + 4 * ((Dw.p + Dw.q : ℕ) : ℝ) * (P.T₁ : ℝ) with hK
  have hτ : ∀ τ, ∑ i, |(P.wt j τ i : ℝ)| ≤
      (((Dw.p + Dw.q : ℕ) : ℝ) + 1) * ∑ i, |(la τ i : ℝ)| + ((Dw.p + Dw.q : ℕ) : ℝ) * K := by
    intro τ
    have e : ∀ i, |(P.wt j τ i : ℝ)| ≤ |(la τ i : ℝ)| + |(la τ ⟨P.a, ha⟩ : ℝ)| + K := fun i => by
      have h := abs_wt_le P ha hj la w hu τ i
      rw [hw τ, sub_self, abs_zero, add_zero] at h
      have h' : ((|P.wt j τ i| : ℤ) : ℝ) ≤ ((|la τ i| + |la τ ⟨P.a, ha⟩| + 2 * |P.c₀| + 3 * ((Dw.p + Dw.q : ℕ) : ℤ) +
          4 * ((Dw.p + Dw.q : ℕ) : ℤ) * P.T₁ : ℤ) : ℝ) := by exact_mod_cast h
      rw [hK]; push_cast at h' ⊢; linarith
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => e i
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul] at hs
    have hl : |(la τ ⟨P.a, ha⟩ : ℝ)| ≤ ∑ i, |(la τ i : ℝ)| :=
      Finset.single_le_sum (f := fun i => |(la τ i : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    have hN : (0 : ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast at hs hl ⊢
    nlinarith
  calc ∑ τ, ∑ i, |(P.wt j τ i : ℝ)|
      ≤ ∑ τ, ((((Dw.p + Dw.q : ℕ) : ℝ) + 1) * ∑ i, |(la τ i : ℝ)| + ((Dw.p + Dw.q : ℕ) : ℝ) * K) :=
        Finset.sum_le_sum fun τ _ => hτ τ
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end GlobalTheory.CovTop.WtRun

namespace GlobalTheory.CovTop.WtRun

theorem numbers {f r Lr PP T Dd c0 kp b : ℝ} (hf : 8 ≤ f) (hr : 2 ≤ r) (hL : 10 ≤ Lr) (hPP : (f * r * Lr) ^ 12 ≤ PP)
    (hT : PP ^ 2 ≤ T) (hDd1 : 1 ≤ Dd) (hDd : Dd ≤ f * r ^ 2) (hc0 : 0 ≤ c0) (hc0' : c0 ≤ 22 * f ^ 2 * r ^ 4)
    (hb : b ≤ PP * kp) (hrows : PP * T * Dd ^ 2 * Lr ≤ b) :
    (r + 1) * kp + f * (r * (2 * |c0| + 3 * r + 4 * r * (T + Dd + 1))) ≤ (f * r * Lr) ^ 2 * kp := by
  have hf1 : 1 ≤ f := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hL1 : 1 ≤ Lr := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hL0 : 0 ≤ Lr := by linarith
  have hfL : 80 ≤ f * Lr := by nlinarith
  have hfL1 : 1 ≤ f * Lr := by linarith
  have hrZ : r ≤ f * r * Lr := by
    calc r = r * 1 := (mul_one r).symm
      _ ≤ r * (f * Lr) := mul_le_mul_of_nonneg_left hfL1 hr0
      _ = f * r * Lr := by ring
  have hZ2 : 160 ≤ f * r * Lr := by
    have : 2 * (f * Lr) ≤ r * (f * Lr) := mul_le_mul_of_nonneg_right hr (by linarith)
    have e : r * (f * Lr) = f * r * Lr := by ring
    linarith
  set Z := f * r * Lr with hZ
  have hZ1 : 1 ≤ Z := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have hZ4 : 22 * Z ^ 4 ≤ Z ^ 12 := by
    have h8 : (22 : ℝ) ≤ Z ^ 8 := by
      have : (160 : ℝ) ^ 8 ≤ Z ^ 8 := pow_le_pow_left₀ (by norm_num) hZ2 8
      have : (22 : ℝ) ≤ 160 ^ 8 := by norm_num
      linarith
    have e : Z ^ 12 = Z ^ 4 * Z ^ 8 := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h8 (pow_nonneg hZ0 4)
    linarith
  have hfr4 : f ^ 2 * r ^ 4 ≤ Z ^ 4 := by
    have h1 : f ^ 2 ≤ f ^ 4 * Lr ^ 4 := by
      have a : f ^ 2 ≤ f ^ 4 := pow_le_pow_right₀ hf1 (by norm_num)
      have b' : f ^ 4 ≤ f ^ 4 * Lr ^ 4 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1)
      linarith
    calc f ^ 2 * r ^ 4 ≤ (f ^ 4 * Lr ^ 4) * r ^ 4 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = Z ^ 4 := by rw [hZ]; ring
  have hPP1 : 1 ≤ PP := le_trans (one_le_pow₀ hZ1) hPP
  have hPPT : PP ≤ T := le_trans (le_self_pow₀ hPP1 (by norm_num)) hT
  have hT1 : 1 ≤ T := hPP1.trans hPPT
  have hT0 : 0 ≤ T := by linarith
  have hc0T : c0 ≤ T := by linarith
  have hDdT : Dd ≤ T := by
    have h1 : f * r ^ 2 ≤ Z ^ 2 := by
      have hfl : 1 ≤ f * Lr ^ 2 := by
        have : 1 ≤ Lr ^ 2 := one_le_pow₀ hL1
        calc (1 : ℝ) = 1 * 1 := by norm_num
          _ ≤ f * Lr ^ 2 := mul_le_mul hf1 this (by norm_num) hf0
      have : f ≤ f ^ 2 * Lr ^ 2 := by
        calc f = f * 1 := (mul_one f).symm
          _ ≤ f * (f * Lr ^ 2) := mul_le_mul_of_nonneg_left hfl hf0
          _ = f ^ 2 * Lr ^ 2 := by ring
      calc f * r ^ 2 ≤ (f ^ 2 * Lr ^ 2) * r ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
        _ = Z ^ 2 := by rw [hZ]; ring
    have : Z ^ 2 ≤ Z ^ 12 := pow_le_pow_right₀ hZ1 (by norm_num)
    linarith
  have hrT : r ≤ T := by
    have : Z ≤ Z ^ 12 := le_self_pow₀ hZ1 (by norm_num)
    linarith
  have hK : 2 * |c0| + 3 * r + 4 * r * (T + Dd + 1) ≤ 17 * r * T := by
    rw [abs_of_nonneg hc0]
    have q1 : r * Dd ≤ r * T := mul_le_mul_of_nonneg_left hDdT hr0
    have q2 : r * 1 ≤ r * T := mul_le_mul_of_nonneg_left hT1 hr0
    have q3 : 1 * T ≤ r * T := mul_le_mul_of_nonneg_right hr1 hT0
    have e1 : 4 * r * (T + Dd + 1) = 4 * (r * T) + 4 * (r * Dd) + 4 * (r * 1) := by ring
    have e2 : 17 * r * T = 17 * (r * T) := by ring
    rw [e1, e2]
    linarith
  have hTk : T * Lr ≤ kp := by
    have hPP0 : 0 < PP := by linarith
    have h1 : PP * (T * Dd ^ 2 * Lr) ≤ PP * kp := by
      have e : PP * (T * Dd ^ 2 * Lr) = PP * T * Dd ^ 2 * Lr := by ring
      linarith
    have h2 : T * Dd ^ 2 * Lr ≤ kp := le_of_mul_le_mul_left h1 hPP0
    have h3 : T * Lr ≤ T * Dd ^ 2 * Lr := by
      have : 1 ≤ Dd ^ 2 := one_le_pow₀ hDd1
      have := mul_le_mul_of_nonneg_left this (mul_nonneg hT0 hL0)
      have e : T * Lr * Dd ^ 2 = T * Dd ^ 2 * Lr := by ring
      linarith
    linarith
  have hkp : 0 ≤ kp := le_trans (mul_nonneg hT0 hL0) hTk
  have hA : (r + 1) * kp ≤ Z ^ 2 / 2 * kp := by
    apply mul_le_mul_of_nonneg_right _ hkp
    have : 160 * Z ≤ Z * Z := mul_le_mul_of_nonneg_right hZ2 hZ0
    have e : Z ^ 2 = Z * Z := sq Z
    linarith
  have hB : f * (r * (2 * |c0| + 3 * r + 4 * r * (T + Dd + 1))) ≤ Z ^ 2 / 2 * kp := by
    have h1 : f * (r * (2 * |c0| + 3 * r + 4 * r * (T + Dd + 1))) ≤ f * (r * (17 * r * T)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK hr0) hf0
    have h2 : f * (r * (17 * r * T)) ≤ Z ^ 2 / 2 * kp := by
      have e : Z ^ 2 / 2 * kp = f * (r * (r * (f * Lr * Lr * kp / 2))) := by rw [hZ]; ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ hf0
      apply mul_le_mul_of_nonneg_left _ hr0
      have : 17 * T ≤ f * Lr * Lr * kp / 2 := by
        have hfl : 800 ≤ f * Lr * Lr := by
          have := mul_le_mul hfL hL (by norm_num) (by linarith)
          linarith
        have hk10 : 10 * T ≤ kp := by
          have := mul_le_mul_of_nonneg_left hL hT0
          linarith
        have h3 : 800 * kp ≤ f * Lr * Lr * kp := mul_le_mul_of_nonneg_right hfl hkp
        linarith
      calc 17 * r * T = r * (17 * T) := by ring
        _ ≤ r * (f * Lr * Lr * kp / 2) := mul_le_mul_of_nonneg_left this hr0
    exact h1.trans h2
  have : Z ^ 2 / 2 * kp + Z ^ 2 / 2 * kp = Z ^ 2 * kp := by ring
  linarith

end GlobalTheory.CovTop.WtRun

namespace GlobalTheory.CovTop.WtRun
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem sum_abs_wt_le_point {PP C A M : ℝ} (hS : SizeAt p i PP C) (hH : HostNum D L PP A M) (hW : WtNum p i PP) {j : ℕ}
    (hj : j ≤ lenT p i PP) :
    ∑ τ, ∑ k, |((⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j τ k : ℝ)| ≤
      zBase L ^ 2 * kap p i := by
  set P : WtPar (dat p i) := ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ with hP
  obtain ⟨-, -, hN⟩ := hW.sig
  have h2m := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have ha : P.a < (dat p i).p + (dat p i).q := by
    show D.R.k - 2 < _
    rw [hN, hr]; omega
  have hw : ∀ τ, anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ =
      laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ ⟨P.a, ha⟩ := by
    intro τ
    have h1 : D.R.k - 1 - 1 < (dat p i).p + (dat p i).q := by rw [hN, hr]; omega
    rw [anchor, dif_pos h1]
    exact congrArg _ (Fin.ext (by show D.R.k - 1 - 1 = D.R.k - 2; omega))
  have hs := sum_abs_wt_le P ha hj (laOf (dat p i) (wtA (p.κ i)) (p.κ i).n) _ rfl hw
  refine hs.trans ?_
  have hk : ∑ τ, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)| = kap p i := rfl
  have eN : (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r := by exact_mod_cast hN
  have eC : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f := by
    rw [← Nat.card_eq_fintype_card, hW.card]
  have eT : (P.T₁ : ℝ) = (lenT p i PP : ℝ) + (CompHt.dimFlag (dat p i) : ℝ) + 1 := by
    simp only [WtPar.T₁, hP, ← GlobalTheory.CompHS.dimFlag_eq]
    push_cast; ring
  have ec : (P.c₀ : ℝ) = (cZero D ((i : ℕ) + 1) : ℝ) := rfl
  rw [hk, eN, eC, eT, ec]
  obtain ⟨-, hc0, hc0'⟩ := cZero_spec D ((i : ℕ) + 1)
  have hc0R : (0 : ℝ) ≤ (cZero D ((i : ℕ) + 1) : ℝ) := by exact_mod_cast hc0
  have hc0R' : (cZero D ((i : ℕ) + 1) : ℝ) ≤ 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4 := by exact_mod_cast hc0'
  have hb1 := hS.1
  have hbk := hS.2.2.2.2.2.1
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hr2 : (2 : ℝ) ≤ D.R.r := by
    have : 2 ≤ D.R.r := by rw [hr]; omega
    exact_mod_cast this
  have hL := hH.big.2.1
  have hPP := hH.ppLow
  have hrows := hW.what₂.2
  have hdim := hW.dim
  have hDd1 : (1 : ℝ) ≤ (CompHt.dimFlag (dat p i) : ℝ) := by
    rw [hdim]
    have h1 : 1 ≤ D.R.f := by have := hH.f8; omega
    have h2 : 1 ≤ D.R.r.choose 2 := by
      have : 2 ≤ D.R.r := by rw [hr]; omega
      exact Nat.one_le_iff_ne_zero.2 (Nat.choose_pos this).ne'
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_pos h1 h2).ne'
  have hDd : (CompHt.dimFlag (dat p i) : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by
    rw [hdim]
    have : D.R.r.choose 2 ≤ D.R.r ^ 2 := by
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ _).trans (by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    exact_mod_cast Nat.mul_le_mul_left _ this
  have hPP1 : 1 ≤ PP := by
    have : (1 : ℝ) ≤ zBase L := by
      unfold zBase
      have := mul_le_mul (mul_le_mul hf8 hr2 (by norm_num) (by linarith)) (by linarith : (1 : ℝ) ≤ L.sc.L) (by norm_num)
        (by positivity)
      linarith
    exact le_trans (one_le_pow₀ this) hPP
  have hTle : PP ^ 2 ≤ (lenT p i PP : ℝ) := by
    refine le_trans ?_ (Nat.le_ceil _)
    have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
    have hkm : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
    rw [le_div_iff₀ hm0]
    have h1 : (1 : ℝ) ≤ (CompHt.dimFlag (dat p i) : ℝ) ^ 2 := one_le_pow₀ hDd1
    have h2 : PP ^ 2 * 1 ≤ PP ^ 2 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 := mul_le_mul h2 hkm hm0.le (by positivity)
    linarith
  have := numbers (f := D.R.f) (r := D.R.r) (Lr := L.sc.L) (PP := PP) (T := lenT p i PP)
    (Dd := CompHt.dimFlag (dat p i)) (c0 := cZero D ((i : ℕ) + 1)) (kp := kap p i) (b := L.sc.b) hf8 hr2 hL
    (by unfold zBase at hPP; exact hPP) hTle hDd1 hDd hc0R hc0R' hbk hrows
  unfold zBase
  exact this

end GlobalTheory.CovTop.WtRun

namespace GlobalTheory.CovTop.WtRun

theorem wt_size : Size → Covers fun Fm x _ ι p i Y PP _ => ∀ j ≤ lenT p i PP, ∑ τ, ∑ k, |((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * kap p i := by
  intro hS
  have hL : Lifts fun Fm x _ ι p i PP C => SizeAt p i PP C ∧ (∃ A, HostNum (Fm.D x ι) (Fm.L x ι) PP A 0) ∧ WtNum p i PP := by
    refine (Formalism.MainNotions.Closed.and hS (Formalism.MainNotions.Closed.and (GlobalTheory.CovTop.Sizes.hostN 0) GlobalTheory.CovTop.WtShape.wtN)).imp
      fun Fm CH _ hh => ?_
    obtain ⟨⟨C, hC, a, ha⟩, ⟨C', -, b, hb⟩, ⟨C'', -, c, hc⟩⟩ := hh
    exact ⟨C, hC, max a (max b c), fun x hx hle ι p hp i =>
      ⟨ha x hx ((le_max_left _ _).trans hle) ι p hp i,
       ⟨C', hb x hx (((le_max_left _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩,
       hc x hx (((le_max_right _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩⟩
  exact CovSz.covers_of_lifts hL fun Fm x hx ι p i C _ h _ Y _ => by
    obtain ⟨h1, ⟨A, h2⟩, h3⟩ := h
    exact fun j hj => sum_abs_wt_le_point p i h1 h2 h3 hj

end GlobalTheory.CovTop.WtRun
