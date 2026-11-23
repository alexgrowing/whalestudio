import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.MovedField

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.FunObj Formalism.L2.Host ValuativeRel

variable {D : D7}

theorem exists_zpow_unit (w : Pl D.host.E) (x : (Kw w)ˣ) :
    ∃ n : ℤ, Valued.v (((x * unifAt w ^ n : (Kw w)ˣ)) : Kw w) = 1 := by
  have h0 : Valued.v (x : Kw w) ≠ 0 := by simp
  have hu : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  have hx : Valued.v (x : Kw w) = WithZero.exp (WithZero.log (Valued.v (x : Kw w))) := (WithZero.exp_log h0).symm
  refine ⟨WithZero.log (Valued.v (x : Kw w)), ?_⟩
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, hu, ← WithZero.exp_zsmul, ← WithZero.exp_add]
  simp

theorem natCast_cpow_half (N : ℕ) (m : ℤ) :
    (N : ℂ) ^ ((((m : ℝ) / 2 : ℝ)) : ℂ) = ((Real.sqrt N : ℝ) : ℂ) ^ m := by
  rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.ofReal_zpow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

theorem sqrt_absNorm_ne_zero (w : Pl D.host.E) : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ≠ 0 := by
  have h : (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot)
  exact_mod_cast (Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h)))

theorem apow_half_mem {w : Pl D.host.E} {K : Subfield ℂ}
    (hs : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ K) (x : (Kw w)ˣ) (z : ℤ) : apow x ((z : ℂ) / 2) ∈ K := by
  obtain ⟨n, hn⟩ := exists_zpow_unit w x
  have h1 : valuation (Kw w) (((x * unifAt w ^ n : (Kw w)ˣ)) : Kw w) = 1 := (Good.isEquiv_Kw w).eq_one_iff_eq_one.2 hn
  have hx : x = (x * unifAt w ^ n) * unifAt w ^ (-n) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx, apow_mul, apow_of_valuation_eq_one h1, one_mul, apow_zpow, (isUnif_unifAt w).apow_eq,
    GlobalTheory.LFun.SatBoundGL.resCard_completion]
  have e1 : -(((-n : ℤ) : ℂ) * ((z : ℂ) / 2)) = ((((n * z : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, natCast_cpow_half]
  exact zpow_mem hs _

theorem loc_mem_of_unrAt {w : Pl D.host.E} {K : Subfield ℂ} {χ : HChar D.host.E} (hu : χ.UnrAt w)
    (hv : χ.valTw (1 / 2) w ∈ K) (hs : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ K) (x : (Kw w)ˣ) :
    ((χ.loc w x : ℂˣ) : ℂ) ∈ K := by
  obtain ⟨n, hn⟩ := exists_zpow_unit w x
  have hx : x = (x * unifAt w ^ n) * unifAt w ^ (-n) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx, map_mul, hu _ hn, one_mul, map_zpow, Units.val_zpow_eq_zpow_val]
  refine zpow_mem ?_ _
  have e1 : -(((1 / 2 : ℝ)) : ℂ) = ((((-1 : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hval : χ.valTw (1 / 2) w = ((χ.loc w (unifAt w) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ)⁻¹ := by
    rw [HChar.valTw, e1, natCast_cpow_half, zpow_neg_one]
    rfl
  have : ((χ.loc w (unifAt w) : ℂˣ) : ℂ) = χ.valTw (1 / 2) w * ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) := by
    rw [hval, inv_mul_cancel_right₀ (sqrt_absNorm_ne_zero w)]
  rw [this]
  exact mul_mem hv hs

theorem units_prod_mem {α : Type*} (K : Subfield ℂ) (f : α → ℂˣ) :
    ∀ l : List α, (∀ a ∈ l, ((f a : ℂˣ) : ℂ) ∈ K) → (((l.map f).prod : ℂˣ) : ℂ) ∈ K
  | [], _ => by simp [one_mem]
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons, Units.val_mul]
    exact mul_mem (h a List.mem_cons_self) (units_prod_mem K f l fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem list_prod_mem' {α : Type*} (K : Subfield ℂ) (f : α → ℂ) :
    ∀ l : List α, (∀ a ∈ l, f a ∈ K) → (l.map f).prod ∈ K
  | [], _ => by simp [one_mem]
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (h a List.mem_cons_self) (list_prod_mem' K f l fun b hb => h b (List.mem_cons_of_mem _ hb))

end GlobalTheory.MovedField

open GlobalTheory.MovedField GlobalTheory.SplitFlip GlobalTheory.SplitWeil Formalism.L2.Host in

theorem GlobalTheory.MovedField.moved_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) (S : (locGrid ch.G t w).Args → ℂ), (∀ z, S z ∈ Set.range D.what₂.embLL) → ∀ z, moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) S z ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b _ _ _ hF t Φ _ β _ w S hS z
  set K : Subfield ℂ := D.what₂.embLL.fieldRange with hKdef
  have hK : ∀ y : ℂ, y ∈ Set.range D.what₂.embLL ↔ y ∈ K := fun y => by
    rw [Set.mem_range, hKdef, RingHom.mem_fieldRange]
  have hsq : ((Real.sqrt (Ideal.absNorm (w : Pl D.host.E).asIdeal) : ℝ) : ℂ) ∈ K :=
    (hK _).1 (hF.sqrt w.1 (.inr ⟨t, w.2⟩))

  have hmu : ∀ j (x : (Kw w.1)ˣ), (((locGrid ch.G t w).mu j x : ℂˣ) : ℂ) ∈ K := fun j x => by
    show ((((GlobalTheory.FunObj.muBase _ j * _).loc _) x : ℂˣ) : ℂ) ∈ K
    rw [HChar.loc_mul, Units.val_mul]
    refine mul_mem ?_ ((hK _).1 (hF.chars.xi t _ x))
    rcases j with _ | j
    · simp [GlobalTheory.FunObj.muBase, one_mem]
    · rw [GlobalTheory.FunObj.muBase]
      split_ifs with hj
      · exact (hK _).1 (hF.chars.mu0 ⟨j, hj⟩ _ x)
      · simp [one_mem]
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x : (Kw w.1)ˣ, (((locGrid ch.G t w).chi i x : ℂˣ) : ℂ) ∈ K :=
    fun i h1 h2 x => (hK _).1 (hF.chars.chi i h1 h2 _ x)
  have heta : ∀ x : (Kw w.1)ˣ, (((locGrid ch.G t w).eta x : ℂˣ) : ℂ) ∈ K := fun x => by
    have hu := R.toLevCh.C.isEta.unr w.1
    obtain ⟨y, hy⟩ := hF.chars.eta w.1 hu
    exact loc_mem_of_unrAt hu (hy ▸ (hK _).1 ⟨y, rfl⟩) hsq x

  have hkap : ∀ e ∈ oppositePath D.R.m, ∀ X (x : (Kw w.1)ˣ), (((locGrid ch.G t w).kappa e X x : ℂˣ) : ℂ) ∈ K := by
    intro e he X x
    rw [Grid.kappa, MonoidHom.div_apply, MonoidHom.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    refine div_mem ?_ (pow_mem (heta x) _)
    rcases GlobalTheory.FunObj.mem_oppositePath.1 he with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
    · exact hchi _ (by show 1 ≤ D.R.m - i; omega) (by show D.R.m - i ≤ D.R.m; omega) x
    · exact hmu _ x
  have hap : ∀ (x : (Kw w.1)ˣ) (n : ℕ), apow x ((n : ℂ) / 2) ∈ K ∧ apow x (-(n : ℂ) / 2) ∈ K := fun x n =>
    ⟨by simpa using apow_half_mem hsq x n, by simpa using apow_half_mem hsq x (-n)⟩
  have hedge : ∀ g, ∀ e ∈ oppositePath D.R.m, (locGrid ch.G t w).edgeFactor .one g e ∈ K := by
    intro g e he
    rw [Grid.edgeFactor, Units.val_inv_eq_inv_val]
    exact mul_mem (mul_mem (mul_mem (hkap e he _ _) (inv_mem (hkap e he _ _))) (hap _ _).1) (hap _ _).2
  have hchar : ∀ g, ((((charFactor (locGrid ch.G t w) g)⁻¹ : ℂˣ)) : ℂ) ∈ K := by
    intro g
    rw [Units.val_inv_eq_inv_val]
    refine inv_mem (units_prod_mem K _ _ fun e he => ?_)
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    exact mul_mem (hkap e he _ _) (inv_mem (hkap e he _ _))
  rw [hK]
  simp only [moved, Grid.pathAct]
  refine mul_mem ?_ (mul_mem (list_prod_mem' K _ _ (hedge _)) ((hK _).1 (hS _)))
  split
  · exact one_mem K
  · exact hchar _
