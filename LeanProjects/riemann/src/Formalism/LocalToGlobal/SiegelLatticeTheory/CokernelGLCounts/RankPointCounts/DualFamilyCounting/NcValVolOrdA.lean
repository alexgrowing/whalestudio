import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiffProd

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  NumberField IsDedekindDomain
open scoped TensorProduct Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def BoxScaleL : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (ι : Type) [Fintype ι], Module.finrank F E = 2 →
    ∀ (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure] (x : ι → Fv F v), (∀ i, x i ≠ 0) →
      (μ (Set.univ.pi fun i => {c | sc (E := E) v (x i) * c ∈ OEv (E := E) v})).toReal =
        (μ (Set.univ.pi fun _ : ι => OEv (E := E) v)).toReal * ∏ i, (absV v (x i) ^ 2)⁻¹

def SdFromAnn : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (d : Fv F v), IsCharAF F ψ →
    Module.finrank F E = 2 → d ≠ 0 →
    (∀ y : Fv F v ⊗[F] E,
      (∀ x ∈ OEv (E := E) v, psiV F ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y)) = 1) ↔
        sc (E := E) v d * y ∈ OEv (E := E) v) →
    ∀ (ι : Type) [Fintype ι], (sdE (E := E) ψ v ι).IsAddHaarMeasure ∧ SFinite (sdE (E := E) ψ v ι) ∧
      (sdE (E := E) ψ v ι (Set.univ.pi fun _ : ι => OEv (E := E) v)).toReal = absV v d ^ Fintype.card ι

section Loc

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def SdNormDV : Prop :=
  ∀ v : PlX X, ¬ TypAt X v → ∀ (ι : Type) [Fintype ι],
    (sdE (E := X.B.I.E) ψ v ι).IsAddHaarMeasure ∧ SFinite (sdE (E := X.B.I.E) ψ v ι) ∧
      (sdE (E := X.B.I.E) ψ v ι (Set.univ.pi fun _ : ι => OEv (E := X.B.I.E) v)).toReal =
        absV v (dV v) ^ Fintype.card ι

end Loc

namespace VolOrdW

section AbsV

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem absNorm_pos : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero h

theorem absV_mul (x y : Fv F v) : absV v (x * y) = absV v x * absV v y := by
  by_cases hx : x = 0
  · subst hx
    simp [absV]
  by_cases hy : y = 0
  · subst hy
    simp [absV]
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  have key : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero, map_mul]
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := (absNorm_pos v).ne'
  simp only [absV, dif_neg hx', dif_neg hy', dif_neg hxy', key, toAdd_mul, zpow_add₀ hN]

theorem absV_one : absV v (1 : Fv F v) = 1 := by
  have h1 : Valued.v (1 : Fv F v) ≠ 0 := by simp
  have key : WithZero.unzero h1 = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, map_one, WithZero.coe_one]
  simp only [absV, dif_neg h1, key, toAdd_one, zpow_zero]

theorem absV_pos {x : Fv F v} (hx : x ≠ 0) : 0 < absV v x := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  simp only [absV, dif_neg hx']
  exact zpow_pos (absNorm_pos v) _

theorem absV_inv {x : Fv F v} (hx : x ≠ 0) : absV v x⁻¹ = (absV v x)⁻¹ := by
  have h := absV_mul v x⁻¹ x
  rw [inv_mul_cancel₀ hx, absV_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem absV_pow (x : Fv F v) (n : ℕ) : absV v (x ^ n) = absV v x ^ n := by
  induction n with
  | zero => simp [absV_one]
  | succ n ih => rw [pow_succ, absV_mul, ih, pow_succ]

theorem dV_ne_zero : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem alp_ne_zero (r : ℕ) (i : Fin (r + 1)) : alp v r i ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))
  · exact one_ne_zero

theorem absV_alp (r : ℕ) (i : Fin (r + 1)) :
    absV v (alp v r i) = absV v (dV v) ^ (-((r : ℝ) - ((i : ℕ) : ℝ))) := by
  have hd := absV_pos v (dV_ne_zero v)
  have hi : (i : ℕ) ≤ r := Nat.lt_succ_iff.mp i.2
  unfold alp
  split_ifs with h
  · rw [absV_pow, absV_inv v (dV_ne_zero v), ← Nat.cast_sub hi, Real.rpow_neg hd.le, Real.rpow_natCast,
      inv_pow]
  · have : (i : ℕ) = r := le_antisymm hi (not_lt.mp h)
    rw [absV_one, this, sub_self, neg_zero, Real.rpow_zero]

end AbsV

section Real

theorem fac (a x y : ℝ) (ha : 0 < a) : a * ((a ^ x * a ^ y) ^ 2)⁻¹ = a ^ (1 - 2 * (x + y)) := by
  have h1 : (a ^ x * a ^ y) ^ 2 = a ^ (2 * (x + y)) := by
    rw [← Real.rpow_add ha, sq, ← Real.rpow_add ha]
    congr 1
    ring
  rw [h1, ← Real.rpow_neg ha.le, mul_comm, ← Real.rpow_add_one ha.ne']
  congr 1
  ring

theorem sum_range_cast (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℝ) = ((n : ℝ) ^ 2 - n) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem tri (g : ℕ → ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), (if i < j then g i j else 0) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (if i < j then g i j else 0) +
        ∑ i ∈ Finset.range n, g i n := by
  rw [Finset.sum_range_succ]
  have h0 : ∑ j ∈ Finset.range (n + 1), (if n < j then g n j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : ¬ n < j := by
      rw [Finset.mem_range] at hj
      omega
    simp [hj']
  rw [h0, add_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  rw [Finset.sum_range_succ, if_pos hin]

theorem triU (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (if i < j then (1 - 2 * ((j : ℝ) - (i : ℝ))) else 0) =
      ((n : ℝ) ^ 2 - n) / 2 - ((n : ℝ) ^ 3 - n) / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [tri (fun i j => (1 - 2 * ((j : ℝ) - (i : ℝ)))) n, ih]
    have e : ∀ i ∈ Finset.range n, (1 - 2 * ((n : ℝ) - (i : ℝ))) = (1 - 2 * (n : ℝ)) + 2 * (i : ℝ) := by
      intros
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, sum_range_cast, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast
    ring

theorem finSum2 (n : ℕ) (h : ℕ → ℕ → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, h i j = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, h i j := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin n, h i j) n]
  apply Finset.sum_congr rfl
  intro i _
  exact Fin.sum_univ_eq_sum_range (fun j => h i j) n

theorem sumZ (r : ℕ) :
    ∑ p : Fin (r + 1) × Fin (r + 1),
        (1 - 2 * (-((r : ℝ) - ((p.1 : ℕ) : ℝ)) + -((r : ℝ) - ((p.2 : ℕ) : ℝ)))) =
      ((r : ℝ) + 1) ^ 2 * (2 * r + 1) := by
  rw [Fintype.sum_prod_type]
  try dsimp only
  rw [finSum2 (r + 1) (fun i j => (1 - 2 * (-((r : ℝ) - (i : ℝ)) + -((r : ℝ) - (j : ℝ)))))]
  have e : ∀ i j : ℕ, (1 - 2 * (-((r : ℝ) - (i : ℝ)) + -((r : ℝ) - (j : ℝ)))) =
      (1 + 4 * (r : ℝ)) - 2 * (i : ℝ) - 2 * (j : ℝ) := by
    intros
    ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum,
    sum_range_cast]
  push_cast
  ring

theorem sumU (r : ℕ) :
    ∑ q : UIdx r, (1 - 2 * (((q.1.2 : ℕ) : ℝ) - ((q.1.1 : ℕ) : ℝ))) =
      ((r : ℝ) ^ 2 + r) / 2 - (r : ℝ) * (r + 1) * (r + 2) / 3 := by
  have e1 : ∑ q : UIdx r, (1 - 2 * (((q.1.2 : ℕ) : ℝ) - ((q.1.1 : ℕ) : ℝ))) =
      ∑ p : Fin (r + 1) × Fin (r + 1),
        (if p.1 < p.2 then (1 - 2 * (((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ))) else 0) := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (fun p => by simp)
      (fun p : Fin (r + 1) × Fin (r + 1) => (1 - 2 * (((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ))))).symm
  rw [e1, Fintype.sum_prod_type]
  simp only [Fin.lt_iff_val_lt_val]
  rw [finSum2 (r + 1) (fun i j => if i < j then (1 - 2 * ((j : ℝ) - (i : ℝ))) else 0), triU (r + 1)]
  push_cast
  ring

end Real

end VolOrdW

open VolOrdW in

theorem volOrd_body {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)
    (hN : SdNormDV X ψ) (hB : BoxScaleL) :
    ∀ v : PlX X, ¬ TypAt X v →
      localVolumeUnit X ψ v / ZZX X u u' ψ v =
        absV v (dV v) ^ (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3)) := by
  intro v hv
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have ha : 0 < absV v (dV v) := absV_pos v (dV_ne_zero v)
  obtain ⟨hH1, -, hO1⟩ := hN v hv (Fin (D.R.rS + 1) × Fin (D.R.rS + 1))
  obtain ⟨hH2, hS2, hO2⟩ := hN v hv (UIdx D.R.rS)
  have := hH1
  have := hH2
  have := hS2

  have hsetZ : ZZOrd (E := X.B.I.E) v D.R.rS =
      Set.univ.pi fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) =>
        {c | sc (E := X.B.I.E) v (alp v D.R.rS p.1 * alp v D.R.rS p.2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [ZZOrd, locZ, Set.mem_pi, Prod.forall]
  have eZ : ZZX X u u' ψ v = absV v (dV v) ^ (((D.R.rS : ℝ) + 1) ^ 2 * (2 * D.R.rS + 1)) := by
    unfold ZZX volS
    rw [if_neg hv, hsetZ, hB v (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) hfin
      (sdE (E := X.B.I.E) ψ v (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
      (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => alp v D.R.rS p.1 * alp v D.R.rS p.2)
      (fun p => mul_ne_zero (alp_ne_zero v D.R.rS p.1) (alp_ne_zero v D.R.rS p.2)), hO1,
      ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib, ← sumZ D.R.rS,
      Real.rpow_sum_of_pos ha]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [absV_mul, absV_alp, absV_alp, fac _ _ _ ha]

  have hsetU : UO (E := X.B.I.E) v D.R.rS =
      Set.univ.pi fun q : UIdx D.R.rS =>
        {c | sc (E := X.B.I.E) v ((alp v D.R.rS q.1.1)⁻¹ * alp v D.R.rS q.1.2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [UO, Set.mem_pi]
  have eUO : (sdE (E := X.B.I.E) ψ v (UIdx D.R.rS) (UO (E := X.B.I.E) v D.R.rS)).toReal =
      absV v (dV v) ^ (((D.R.rS : ℝ) ^ 2 + D.R.rS) / 2 - (D.R.rS : ℝ) * (D.R.rS + 1) * (D.R.rS + 2) / 3) := by
    rw [hsetU, hB v (UIdx D.R.rS) hfin (sdE (E := X.B.I.E) ψ v (UIdx D.R.rS))
      (fun q : UIdx D.R.rS => (alp v D.R.rS q.1.1)⁻¹ * alp v D.R.rS q.1.2)
      (fun q => mul_ne_zero (inv_ne_zero (alp_ne_zero v D.R.rS q.1.1)) (alp_ne_zero v D.R.rS q.1.2)), hO2,
      ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib, ← sumU D.R.rS,
      Real.rpow_sum_of_pos ha]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [absV_mul, absV_inv v (alp_ne_zero v D.R.rS q.1.1), absV_alp, absV_alp, ← Real.rpow_neg ha.le,
      neg_neg, fac _ _ _ ha]
    congr 1
    ring
  have eU : localVolumeUnit X ψ v =
      absV v (dV v) ^ (((D.R.rS : ℝ) ^ 2 + D.R.rS) / 2 - (D.R.rS : ℝ) * (D.R.rS + 1) * (D.R.rS + 2) / 3) *
      absV v (dV v) ^ (((D.R.rS : ℝ) ^ 2 + D.R.rS) / 2 - (D.R.rS : ℝ) * (D.R.rS + 1) * (D.R.rS + 2) / 3) := by
    unfold localVolumeUnit volU
    rw [if_neg hv, localVolumeOrdinary, Measure.prod_prod, ENNReal.toReal_mul, eUO]
  rw [eU, eZ, ← Real.rpow_add ha, ← Real.rpow_sub ha]
  congr 1
  ring

end Formalism.L2.SG.Pf.NcVal
