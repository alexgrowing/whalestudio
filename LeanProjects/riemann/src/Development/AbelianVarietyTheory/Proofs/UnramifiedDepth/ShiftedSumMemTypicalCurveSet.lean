import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AddCurveStableOfIntegralGaugedFormalGroupLawStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedCurveLogarithmsClosedUnderTadicLimitsStatement

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.ShiftSum

variable {C : Type} [Field C]

theorem coeff_tyS_congr (l m : ℕ) {a b : ℕ → C} (h : ∀ s ≤ m, a s = b s) :
    PowerSeries.coeff m (tyS l a) = PowerSeries.coeff m (tyS l b) := by
  unfold tyS
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [h s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))]

theorem vpow_succ {N : Type} (s : ℕ) (x : ℕ → N → C) : Vpow (s + 1) x = Vpow 1 (Vpow s x) := by
  funext i n
  simp only [Vpow]
  by_cases h1 : i < 1
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1]
    by_cases h2 : i < s + 1
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]
      congr 1
      omega

theorem partial_eq {N : Type} (y : ℕ → ℕ → N → C) (i M : ℕ) (hM : i < M) (n : N) :
    (∑ s ∈ Finset.range M, Vpow s (y s)) i n = sumV y i n := by
  simp only [sumV, Finset.sum_apply, Vpow]
  symm
  rw [← Finset.sum_subset (s₁ := Finset.range (i + 1)) (s₂ := Finset.range M)
    (Finset.range_subset_range.2 (by omega))]
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [if_neg (by have := Finset.mem_range.1 hs; omega)]
  · intro s _ hs
    rw [if_pos (by rw [Finset.mem_range] at hs; omega)]

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem vpow_mem (X : RawChart C d I κ) (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C)
    (hx : x ∈ X.TySet V g) (s : ℕ) : Vpow s x ∈ X.TySet V g := by
  induction s with
  | zero =>
    have : Vpow 0 x = x := by
      funext i n
      simp [Vpow]
    rwa [this]
  | succ s ih =>
    rw [vpow_succ]
    exact X.V_mem V g _ ih

noncomputable def logOf (X : RawChart C d I κ) (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C) :
    (κ → PowerSeries C) × (JJ I g → PowerSeries C) :=
  (fun i => ∑ c : I g, X.u g c i • tyS V.l (fun s => x s (Sum.inl c)),
   fun q => tyS V.l (fun s => x s (Sum.inr q)) -
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0)

theorem mem_tySet_iff (X : RawChart C d I κ) (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C) :
    x ∈ X.TySet V g ↔ logOf X V g x ∈ Cv X V g := by
  constructor
  · rintro ⟨γ, lam, hγ, hlam, h1, h2⟩
    exact ⟨γ, lam, hγ, hlam, h1, fun q => sub_eq_iff_eq_add.2 (h2 q)⟩
  · rintro ⟨γ, lam, hγ, hlam, h1, h2⟩
    exact ⟨γ, lam, hγ, hlam, h1, fun q => sub_eq_iff_eq_add.1 (h2 q)⟩

theorem coeff_logOf_congr (X : RawChart C d I κ) (V : VF C) (g : Fin 2) {x x' : ℕ → I g ⊕ JJ I g → C} (m : ℕ)
    (h : ∀ s ≤ m, ∀ n, x s n = x' s n) :
    (∀ i, PowerSeries.coeff m ((logOf X V g x).1 i) = PowerSeries.coeff m ((logOf X V g x').1 i)) ∧
      ∀ q, PowerSeries.coeff m ((logOf X V g x).2 q) = PowerSeries.coeff m ((logOf X V g x').2 q) := by
  have key : ∀ n, PowerSeries.coeff m (tyS V.l (fun s => x s n)) = PowerSeries.coeff m (tyS V.l (fun s => x' s n)) :=
    fun n => coeff_tyS_congr V.l m fun s hs => h s hs n
  constructor
  · intro i
    simp only [logOf, map_sum, PowerSeries.coeff_smul, key]
  · intro q
    simp only [logOf, map_sub, map_sum, key]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · simp only [PowerSeries.coeff_smul, key]
    · rfl

theorem sumV_mem_tySet : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (y : ℕ → ℕ → I g ⊕ JJ I g → C), (∀ s, y s ∈ X.TySet V g) → sumV y ∈ X.TySet V g := by
  intro C _ V d _ I _ κ _ X hX g y hy
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hX.lin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have h0 := X.zero_mem hlg0 (hX.axes 0) V g
  have hA := GlobalTheory.T.addCurveStable_of_integralGaugedFormalGroupLaw C V d I κ X hX
  have hP : ∀ M, ∑ s ∈ Finset.range M, Vpow s (y s) ∈ X.TySet V g := fun M =>
    X.sum_mem V g h0 (X.add_mem V g hA hX.uint) _ _ fun s _ => vpow_mem X V g _ (hy s) s
  rw [mem_tySet_iff]
  refine GlobalTheory.T.gaugedCurveLogarithms_closed_under_tadicLimits C V d I κ X hX g (fun M => logOf X V g (∑ s ∈ Finset.range M, Vpow s (y s))) _
    (fun M => (mem_tySet_iff X V g _).1 (hP M)) fun m => ⟨m + 1, fun M hM => ?_⟩
  exact coeff_logOf_congr X V g m fun s hs n => partial_eq y s M (by omega) n

end GlobalTheory.RowLaw.ShiftSum
