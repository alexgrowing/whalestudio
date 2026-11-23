import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSncChartStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDivisorEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartKltCriterion

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

noncomputable def DivOver.ordHom {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) : X.functionFieldˣ →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (E.ord f)
  map_one' := by simp
  map_mul' f g := by simp [E.ord_mul]

theorem DivOver.ord_prod_zpow {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) {ι : Type} (s : Finset ι) (f : ι → X.functionFieldˣ) (e : ι → ℤ) :
    E.ord (∏ j ∈ s, f j ^ e j) = ∑ j ∈ s, e j * E.ord (f j) := by
  have h := congrArg Multiplicative.toAdd (map_prod E.ordHom (fun j => f j ^ e j) s)
  rw [toAdd_prod] at h
  calc E.ord (∏ j ∈ s, f j ^ e j) = Multiplicative.toAdd (E.ordHom (∏ j ∈ s, f j ^ e j)) := rfl
    _ = ∑ j ∈ s, Multiplicative.toAdd (E.ordHom (f j ^ e j)) := h
    _ = ∑ j ∈ s, e j * E.ord (f j) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_zpow, toAdd_zpow, smul_eq_mul]
      rfl

theorem DivOver.ord_eq_zero_of_unitAt {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {E : DivOver p} {x : X} (hE : E.Through x) (v : X.functionFieldˣ)
    (hv : UnitAt x (v : X.functionField)) : E.ord v = 0 := by
  obtain ⟨a, ha, hav⟩ := hv
  have h1 : (v : X.functionField) ∈ E.ring := hE _ ⟨a, hav⟩
  have hinv : algebraMap (X.presheaf.stalk x) X.functionField (↑(ha.unit⁻¹)) =
      ((v⁻¹ : X.functionFieldˣ) : X.functionField) := by
    rw [Units.val_inv_eq_inv_val]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hav, ← map_mul, IsUnit.mul_val_inv, map_one]
  have h2 : ((v⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring := hE _ ⟨_, hinv⟩
  have e1 := (E.ord_nonneg_iff v).mpr h1
  have e2 := (E.ord_nonneg_iff v⁻¹).mpr h2
  rw [E.ord_inv] at e2
  omega

theorem coeff_criterion_snc : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ (K G : CartierDiv Y) (m : ℕ) (B : Closeds Y), 0 < m → IsDivOfForm K η → FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → (G - m • K).supp ≤ B → ∀ (y : Y) (g : Y.functionFieldˣ), G.IsEqn y g → ∀ E : DivOver q, E.Through y → ((∀ w, w ⤳ y → (G - m • K).mult w < m) → -1 < discrep E η m g) ∧ ((∀ w, w ⤳ y → (G - m • K).mult w ≤ m) → -1 ≤ discrep E η m g) := by
  intro k _ _ Y _ _ q n _ η hη K G m B hm hK hsnc hsupp y g hG E hE
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  have hdim : topologicalKrullDim Y = n :=
    HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q n inferInstance
  obtain ⟨U, hy, z, J, w, u, hc⟩ := exists_isSncChart k Y q n B hsnc y
  have hgen : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hy⟩
  have hfg := isFreeGen_formOf hgen hc.frame
  have hω0 : formOf U hgen (dOn q z) ≠ 0 := by
    intro h0
    have := hfg.1 (a₁ := 0) (a₂ := 1) (by simp only [h0, smul_zero])
    exact zero_ne_one this
  have hr : hfg.repr η ≠ 0 := by
    intro h0
    apply hη
    rw [← hfg.repr_smul η, h0, zero_smul]
  have hηh : η = ((Units.mk0 _ hr : Y.functionFieldˣ) : Y.functionField) • formOf U hgen (dOn q z) :=
    (hfg.repr_smul η).symm
  set h : Y.functionFieldˣ := Units.mk0 _ hr with hdef
  have hKy : K.IsEqn y h := hK U (dOn q z) hc.frame y hy h hηh
  have hD1 : (G - m • K).IsEqn y (g / h ^ m) := hG.sub (hKy.nsmul m)
  have hD2 := IsSncChart.isEqn_monomial k Y q n B y U hy z J w u hc (G - m • K) hsupp
  have hunit := (hD1.iff_unitAt).mp hD2
  have hzero := DivOver.ord_eq_zero_of_unitAt hE
    ((∏ j ∈ J, u j ^ (G - m • K).mult (w j)) / (g / h ^ m)) (by simpa using hunit)
  rw [div_eq_mul_inv, E.ord_mul, E.ord_inv, div_eq_mul_inv, E.ord_mul, E.ord_inv,
    DivOver.ord_prod_zpow, E.ord_pow] at hzero
  have hform : E.formOrd η = E.ord h + E.formOrd (formOf U hgen (dOn q z)) := by
    rw [hηh]
    exact E.formOrd_smul hdim hω0 h
  have hF0 : 0 ≤ E.formOrd (formOf U hgen (dOn q z)) :=
    E.formOrd_formOf_nonneg hdim hy hE (dOn q z) hω0
  have hF1 := E.sum_ord_sub_one_le_formOrd_dOn hdim hy hE z hω0 (J := ↥J) (fun j => j.1)
    Subtype.val_injective (fun j => u j.1) (fun j => hc.val j.1 j.2)
  rw [Finset.sum_coe_sort J (fun j => E.ord (u j))] at hF1
  have hnn : ∀ j ∈ J, 0 ≤ E.ord (u j) := fun j hj =>
    (E.ord_nonneg_iff _).mpr (hE _ (by rw [hc.val j hj]; exact regAt_fnOf hy _ _))
  set F := E.formOrd (formOf U hgen (dOn q z)) with hFdef
  set S := ∑ j ∈ J, E.ord (u j) with hSdef
  set T := ∑ j ∈ J, (G - m • K).mult (w j) * E.ord (u j) with hTdef
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hdisc : discrep E η m g = ((m * F - T : ℤ) : ℚ) / m := by
    have hg' : E.ord g = m * E.ord h + T := by linarith
    unfold discrep
    rw [hform, hg']
    push_cast
    field_simp
    ring
  rw [hdisc]
  constructor
  · intro hlt
    have hT : T ≤ (m - 1) * S := by
      rw [hSdef, hTdef, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j hj => ?_)
      have := hlt (w j) (hc.spec j hj)
      exact mul_le_mul_of_nonneg_right (by omega) (hnn j hj)
    have hS0 : 0 ≤ S := Finset.sum_nonneg hnn
    have key : -(m : ℤ) < m * F - T := by
      rcases eq_or_lt_of_le hS0 with hS | hS
      · rw [← hS] at hT
        have : (m : ℤ) * F ≥ 0 := mul_nonneg (by exact_mod_cast hm.le) hF0
        have hm0 : (0 : ℤ) < m := by exact_mod_cast hm
        linarith
      · have : (m : ℤ) * (S - 1) ≤ m * F :=
          mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast hm.le)
        nlinarith
    rw [lt_div_iff₀ hm']
    have : ((-(m : ℤ) : ℤ) : ℚ) < ((m * F - T : ℤ) : ℚ) := by exact_mod_cast key
    push_cast at this ⊢
    linarith
  · intro hle
    have hT : T ≤ m * S := by
      rw [hSdef, hTdef, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j hj => ?_)
      exact mul_le_mul_of_nonneg_right (hle (w j) (hc.spec j hj)) (hnn j hj)
    have key : -(m : ℤ) ≤ m * F - T := by
      have : (m : ℤ) * (S - 1) ≤ m * F :=
        mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast hm.le)
      nlinarith
    rw [le_div_iff₀ hm']
    have : ((-(m : ℤ) : ℤ) : ℚ) ≤ ((m * F - T : ℤ) : ℚ) := by exact_mod_cast key
    push_cast at this ⊢
    linarith

end GlobalTheory.Discrepancy
