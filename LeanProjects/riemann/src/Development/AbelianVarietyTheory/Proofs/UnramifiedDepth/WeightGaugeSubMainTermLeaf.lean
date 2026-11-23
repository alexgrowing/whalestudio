import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FactorizationLeFourFifteenths
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightSubstNonneg
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffLeafGaugeSubMainTermEqZeroOnFirstAxisStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PderivLeafGaugeEqPairingAddIntegralStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HPullWUpGTwoGroupEmbeddingEqRenameStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearSubstCoordinateWeightNonnegRadiusStatement

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTermWeight

open GlobalTheory.WeightSubst

variable {C : Type} [Field C]

theorem wtNonneg_rename (v : AddValuation C (WithTop ℝ)) {σ τ : Type} [Finite σ] (f : σ ↪ τ) (ρ : τ → ℝ)
    (r : ℝ) (hr : ∀ s, ρ (f s) = r) (F : MvPowerSeries σ C)
    (hF : ∀ μ : σ →₀ ℕ, ((-((μ.degree : ℝ) * r) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff μ F)) :
    WtNonneg v ρ (MvPowerSeries.rename f F) := by
  intro α
  by_cases h : α ∈ Set.range (Finsupp.mapDomain f)
  · obtain ⟨μ, rfl⟩ := h
    rw [← Finsupp.embDomain_eq_mapDomain, MvPowerSeries.coeff_embDomain_rename, Finsupp.sum_embDomain]
    convert hF μ using 2
    simp only [hr, Finsupp.sum, Finsupp.degree_apply]
    push_cast
    rw [Finset.sum_mul, zero_sub]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · rw [MvPowerSeries.coeff_rename_eq_zero _ _ h]
    simp

theorem wtNonneg_add (v : AddValuation C (WithTop ℝ)) {τ : Type} (ρ : τ → ℝ) {F G : MvPowerSeries τ C}
    (hF : WtNonneg v ρ F) (hG : WtNonneg v ρ G) : WtNonneg v ρ (F + G) := by
  intro α
  rw [map_add]
  exact v.map_le_add (hF α) (hG α)

theorem wtNonneg_sum (v : AddValuation C (WithTop ℝ)) {τ ι : Type} (ρ : τ → ℝ) (s : Finset ι)
    {F : ι → MvPowerSeries τ C} (hF : ∀ i ∈ s, WtNonneg v ρ (F i)) : WtNonneg v ρ (∑ i ∈ s, F i) := by
  intro α
  rw [map_sum]
  exact v.map_le_sum fun i hi => hF i hi α

theorem wtNonneg_smul (V : VF C) {τ : Type} (ρ : τ → ℝ) {c : C} (hc : V.Ge 0 c) {F : MvPowerSeries τ C}
    (hF : WtNonneg V.v ρ F) : WtNonneg V.v ρ (c • F) := by
  intro α
  rw [map_smul, smul_eq_mul]
  exact VF.Ge.mul_int hc (hF α)

theorem le_add_coe_iff (x : WithTop ℝ) (w r : ℝ) :
    (w : WithTop ℝ) ≤ x + (r : WithTop ℝ) ↔ ((w - r : ℝ) : WithTop ℝ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => simp
  | coe t =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    exact sub_le_iff_le_add.symm

theorem radius_one (l i : ℕ) (hl : l ≠ 0) :
    r1 l i - del l i = 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ i) := by
  have : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  unfold r1 del rho
  have h : 1 / (2 * (l : ℝ) ^ i) - 1 / (8 * (l : ℝ) ^ i) = 3 / (8 * (l : ℝ) ^ i) := by
    field_simp
    ring
  linarith

theorem radius_two (l i : ℕ) :
    r2 l - del l i = 1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i) := by
  unfold r2 del rho
  rfl

theorem constantCoeff_linPull {σ ι : Type} [Fintype σ] [Fintype ι] (e : ι → σ → C) (F : MvPowerSeries σ C)
    (hF : MvPowerSeries.constantCoeff F = 0) : MvPowerSeries.constantCoeff (linPull e F) = 0 := by
  have h0 : ∀ x : σ, MvPowerSeries.constantCoeff
      (∑ c : ι, e c x • (MvPowerSeries.X c : MvPowerSeries ι C)) = 0 := by
    intro x
    simp [map_sum]
  exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero h0) h0 hF

theorem pderiv_mainM (V : VF C) (i : ℕ) {ι ι' : Type} [Fintype ι] [Fintype ι'] (Φ : ι' → ι → C) (b : ι') :
    MvPowerSeries.pderiv C (Sum.inr b) (mainM V i Φ) =
      ((V.l : C) ^ expE V.l i)⁻¹ • ∑ c : ι,
        Φ b c • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C) ^ (V.l ^ i) := by
  unfold mainM
  rw [Derivation.map_smul, map_sum, Finset.sum_eq_single b]
  · rw [map_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [Derivation.leibniz, Derivation.leibniz_pow, MvPowerSeries.pderiv_X]
  · intro b' _ hb
    rw [map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    simp [Derivation.leibniz, Derivation.leibniz_pow, MvPowerSeries.pderiv_X, hb]
  · simp

theorem weight_gauge_sub_main : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → 5 ≤ V.l → ∀ (g : Fin 2) (a : ZMod d) (i : ℕ), Odd i → i < d → ∀ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (N M : ℕ) (e : Fin N → I g → C) (v' : Fin M → I (1 - g) → C) (Φt : Fin N → J g → C), (∀ c x, (X.G g).ty (Sum.inl x) ≠ a → e c x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0) → (∀ c, WtGe1 V i 0 (linPull e (t g c))) → (∀ κ : J g, (X.G g).ty (Sum.inr κ) = a + (i : ZMod d) → WtGe1 V i 0 (linPull e ((S g).ze (t g) κ) - ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N, Φt δ κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i))) → WtGe2 V i (1 / ((V.l : ℝ) - 1)) (X.hM g a i e v' - mainM V i (fun b c => ∑ κ : J g, ∑ k : I (1 - g), Φt c κ * X.pair g κ k * v' b k)) := by
  intro C _ V d _ I J _ _ X hA hl g a i hi hid S t ht N M e v' Φt he hv hv' hT hZ
  haveI := X.charZero
  have hl0 : V.l ≠ 0 := V.l_prime.ne_zero
  have hpull := GlobalTheory.T.hPullW_upG_twoGroupEmbedding_eq_rename C I g (Fin N) (Fin M) e v'
  have key := GlobalTheory.weight_of_weight_pderiv C V.v V.l V.l_prime V.v_l hl i (Fin N) (Fin M)
    (X.hM g a i e v' - mainM V i (fun b c => ∑ κ : J g, ∑ k : I (1 - g), Φt c κ * X.pair g κ k * v' b k))
    hi.pos ?_ ?_
  · intro μ
    rw [le_add_coe_iff]
    convert key μ using 3
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type, radius_one _ _ hl0, radius_two]
    simp only [Sum.elim_inl, Sum.elim_inr]
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul]
    congr 1 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · intro α hα
    by_contra hn
    push Not at hn
    exact hα (GlobalTheory.T.coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis C V d I J X g a i _ _ e v' _ α hn)
  · intro b
    set ρ : Fin N ⊕ Fin M → ℝ := Sum.elim (fun _ => 1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i))
      (fun _ => 1 / ((V.l : ℝ) - 1)) with hρ
    have hinl : ∀ F : MvPowerSeries (Fin N) C, WtGe1 V i 0 F →
        WtNonneg V.v ρ (MvPowerSeries.rename (Sum.inl : Fin N → Fin N ⊕ Fin M) F) := by
      intro F hF
      refine wtNonneg_rename V.v Function.Embedding.inl ρ
        (1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i)) (fun _ => rfl) F fun μ => ?_
      have := hF μ
      rw [le_add_coe_iff, radius_one _ _ hl0, zero_sub] at this
      exact this
    obtain ⟨γ, hγ, hd⟩ := GlobalTheory.T.pderiv_leafGauge_eq_pairing_add_integral C V d I J X hA g a i hi hid S t ht (Fin N) (Fin M) e v' he hv hv' b
    have hE : MvPowerSeries.pderiv C (Sum.inr b)
        (X.hM g a i e v' - mainM V i (fun b c => ∑ κ : J g, ∑ k : I (1 - g), Φt c κ * X.pair g κ k * v' b k)) =
        MvPowerSeries.subst (fun w : WV I => hPullW (upG w.1 (t w.1 w.2)) (fun c => toW g (e c))
          (fun b => toW (1 - g) (v' b))) γ + ∑ κ : J g, (∑ k, X.pair g κ k * v' b k) •
          MvPowerSeries.rename (Sum.inl : Fin N → Fin N ⊕ Fin M) (linPull e ((S g).ze (t g) κ) -
            ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N,
              Φt δ κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i)) := by
      rw [map_sub, hd, pderiv_mainM, add_sub_assoc]
      congr 1
      simp only [hpull.1, map_sub, smul_sub, Finset.sum_sub_distrib, map_smul, map_sum, map_pow,
        MvPowerSeries.rename_X]
      congr 1
      simp only [Finset.smul_sum, smul_smul]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_smul, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    change WtNonneg V.v ρ _
    rw [hE]
    have hw : ∀ g' : Fin 2, g' = g ∨ g' = 1 - g := by
      have : ∀ g g' : Fin 2, g' = g ∨ g' = 1 - g := by decide
      exact this g
    refine wtNonneg_add _ _ ?_ (wtNonneg_sum _ _ _ fun κ _ => ?_)
    · refine weight_subst_nonneg C V.v _ _ ρ γ _ hγ ?_ ?_
      · rintro ⟨g', x⟩
        rcases hw g' with rfl | rfl
        · simp only [hpull.1, MvPowerSeries.constantCoeff_rename]
          exact constantCoeff_linPull _ _ ((ht _).1 x)
        · simp only [hpull.2, MvPowerSeries.constantCoeff_rename]
          exact constantCoeff_linPull _ _ ((ht _).1 x)
      · rintro ⟨g', x⟩
        rcases hw g' with rfl | rfl
        · simp only [hpull.1]
          exact hinl _ (hT x)
        · simp only [hpull.2]
          refine wtNonneg_rename V.v Function.Embedding.inr ρ (1 / ((V.l : ℝ) - 1)) (fun _ => rfl) _ fun μ => ?_
          have := GlobalTheory.T.linearSubst_coordinate_weight_nonneg_radius C V d _ _ (X.G (1 - g)) (S _) (t _) (ht _) M v' hv x μ
          unfold VF.Ge at this
          rw [mul_one_div]
          exact this
    · by_cases hκ : (X.G g).ty (Sum.inr κ) = a + (i : ZMod d)
      · exact wtNonneg_smul V ρ (VF.Ge.sum fun k _ => (X.pair_int g κ k).mul_int (hv b k))
          (hinl _ (hZ κ hκ))
      · have : ∑ k, X.pair g κ k * v' b k = 0 := by
          refine Finset.sum_eq_zero fun k _ => ?_
          by_cases hk : (X.G (1 - g)).ty (Sum.inl k) = a + (i : ZMod d)
          · rw [X.pair_type g κ k (by rw [hk]; exact hκ), zero_mul]
          · rw [hv' b k hk, mul_zero]
        rw [this, zero_smul]
        intro α
        simp

end GlobalTheory.MainTermWeight
