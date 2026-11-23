import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedCurveLogarithmsClosedUnderTadicLimitsStatement

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.CvDiv

variable {C : Type} [Field C]

theorem coeff_alongCv_le {σ : Type} [Fintype σ] {γ : σ → PowerSeries C} {n : ℕ}
    (h0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (hγ : ∀ i, ∀ m < n, PowerSeries.coeff m (γ i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff n (alongCv γ f) =
      ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * PowerSeries.coeff n (γ i) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, mul_zero, Finset.sum_const_zero]
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero h0) h0 hf
  · exact coeff_alongCv_low hn hγ hf

theorem coeff_alongCv_smul {σ : Type} [Fintype σ] {γ : σ → PowerSeries C} {n : ℕ} (c : C)
    (h0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (hγ : ∀ i, ∀ m < n, PowerSeries.coeff m (γ i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff n (alongCv (c • γ) f) = c * PowerSeries.coeff n (alongCv γ f) := by
  rw [coeff_alongCv_le h0 hγ hf, coeff_alongCv_le (fun i => by simp [h0 i])
    (fun i m hm => by simp [hγ i m hm]) hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, PowerSeries.coeff_smul, smul_eq_mul]
  ring

theorem isCv_smul {V : VF C} {σ : Type} {γ : σ → PowerSeries C} {c : C} (hc : V.Ge 0 c)
    (h : IsCv V γ) : IsCv V (c • γ) := fun i =>
  ⟨by simp [(h i).1], fun n => by
    simpa only [Pi.smul_apply, PowerSeries.coeff_smul, smul_eq_mul] using hc.mul_int ((h i).2 n)⟩

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem step {X : RawChart C d I κ} {V : VF C} (hX : RLaw X V) (g : Fin 2) {c : C} (hc : V.Ge 0 c)
    (m : ℕ) {a : (κ → PowerSeries C) × (JJ I g → PowerSeries C)} (ha : a ∈ Cv X V g)
    (hv : ∀ i, ∀ k < m, PowerSeries.coeff k (a.1 i) = 0) :
    ∃ b ∈ Cv X V g, ∀ k ≤ m, (∀ i, PowerSeries.coeff k (b.1 i) = c * PowerSeries.coeff k (a.1 i)) ∧
      ∀ q, PowerSeries.coeff k (b.2 q) = c * PowerSeries.coeff k (a.2 q) := by
  classical
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := ha
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hX.lin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hlg1 : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (X.lg i) = if j = i then 1 else 0 := fun i j => by
    rw [hX.lin i _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, if_pos rfl]
    · rw [if_neg hji, if_neg]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
  have h0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  have hord : ∀ k, k < m → ∀ i, PowerSeries.coeff k (γ i) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk i
      have e1 := coeff_alongCv_le h0 (fun i m' hm' => ih m' hm' (by omega) i) (hlg0 i)
      rw [h1 i, hv i k hk] at e1
      simp only [hlg1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e1
      exact e1.symm
  refine ⟨(fun i => alongCv (c • γ) (X.lg i), fun q => (c • lam) q - alongCv (c • γ) (X.sg (X.u (1 - g) q))),
    ⟨c • γ, c • lam, isCv_smul hc hγ, isCv_smul hc hlam, fun _ => rfl, fun _ => rfl⟩, fun k hk => ⟨fun i => ?_, fun q => ?_⟩⟩
  · rw [← h1 i]
    exact coeff_alongCv_smul c h0 (fun i m' hm' => hord m' (by omega) i) (hlg0 i)
  · rw [h2 q]
    simp only [map_sub, Pi.smul_apply, PowerSeries.coeff_smul, smul_eq_mul]
    rw [coeff_alongCv_smul c h0 (fun i m' hm' => hord m' (by omega) i) (X.constantCoeff_sg (hX.axes 0) _)]
    ring

end GlobalTheory.RowLaw.CvDiv

namespace GlobalTheory.RowLaw

open CvDiv in

theorem cv_inv_natCast_smul_mem : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (N : ℕ), V.v (N : C) = 0 → ∀ a ∈ Cv X V g, (N : C)⁻¹ • a ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X hX g N hN a ha
  obtain ⟨hzero, hadd, hneg, -⟩ := GlobalTheory.T.gaugedFormalGroupCurveLogarithms_addSubgroup_rescale C V d I κ X hX g
  have hN0 : (N : C) ≠ 0 := by
    intro h
    rw [h, V.v.map_zero] at hN
    exact WithTop.top_ne_zero hN
  have hc : V.Ge 0 (N : C)⁻¹ := by
    have h := V.v.map_mul (N : C) (N : C)⁻¹
    rw [mul_inv_cancel₀ hN0, V.v.map_one, hN, zero_add] at h
    unfold VF.Ge
    rw [← h]
    exact le_rfl
  have hns : ∀ s ∈ Cv X V g, ∀ n : ℕ, (n : C) • s ∈ Cv X V g := by
    intro s hs n
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
      rw [Nat.cast_succ, add_smul, one_smul]
      exact hadd _ ih _ hs
  have key : ∀ m : ℕ, ∃ s ∈ Cv X V g, ∀ k < m,
      (∀ i, PowerSeries.coeff k (s.1 i) = (N : C)⁻¹ * PowerSeries.coeff k (a.1 i)) ∧
      ∀ q, PowerSeries.coeff k (s.2 q) = (N : C)⁻¹ * PowerSeries.coeff k (a.2 q) := by
    intro m
    induction m with
    | zero => exact ⟨0, hzero, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ m ih =>
      obtain ⟨s, hs, hsa⟩ := ih
      have hr : a + -((N : C) • s) ∈ Cv X V g := hadd _ ha _ (hneg _ (hns s hs N))
      obtain ⟨b, hb, hba⟩ := step hX g hc m hr (fun i k hk => by
        simp only [Prod.fst_add, Prod.fst_neg, Prod.smul_fst, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, map_add,
          map_neg, PowerSeries.coeff_smul, smul_eq_mul, (hsa k hk).1 i]
        field_simp
        ring)
      refine ⟨s + b, hadd _ hs _ hb, fun k hk => ⟨fun i => ?_, fun q => ?_⟩⟩
      · simp only [Prod.fst_add, Prod.fst_neg, Prod.smul_fst, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, map_add,
          map_neg, PowerSeries.coeff_smul, smul_eq_mul, (hba k (by omega)).1 i]
        field_simp
        ring
      · simp only [Prod.snd_add, Prod.snd_neg, Prod.smul_snd, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, map_add,
          map_neg, PowerSeries.coeff_smul, smul_eq_mul, (hba k (by omega)).2 q]
        field_simp
        ring
  choose s hs hsa using key
  refine GlobalTheory.T.gaugedCurveLogarithms_closed_under_tadicLimits C V d I κ X hX g s _ hs fun m => ⟨m + 1, fun n hn => ⟨fun i => ?_, fun q => ?_⟩⟩
  · rw [(hsa n m (by omega)).1 i]
    simp
  · rw [(hsa n m (by omega)).2 q]
    simp

end GlobalTheory.RowLaw
