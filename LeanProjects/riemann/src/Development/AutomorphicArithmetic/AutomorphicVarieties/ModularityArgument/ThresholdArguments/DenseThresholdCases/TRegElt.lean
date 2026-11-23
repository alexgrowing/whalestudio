import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.RegElt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymUse

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem regElt_place {Ω : Type} [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  have hI : Ideal.span {((p : ℕ) : (Int.castRingHom Ω).range)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_exists_inv]
    rintro ⟨⟨_, c, rfl⟩, hc⟩
    have h1 : ((p : ℕ) : Ω) * ((c : ℤ) : Ω) = 1 := congrArg Subtype.val hc
    have h2 : ((p : ℕ) : ℤ) * c = 1 := by exact_mod_cast h1
    have h3 : ((p : ℕ) : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) h2
    exact hp.one_lt.ne' (by exact_mod_cast h3)
  obtain ⟨A, -, hA⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨A, A.mem_nonunits_iff.1 (hA ⟨((p : ℕ) : (Int.castRingHom Ω).range), Ideal.mem_span_singleton_self _, by simp⟩)⟩
private theorem regElt_zpow_ne {G : Type} [Group G] (e : G) (he : ¬ IsOfFinOrder e) (n : ℤ) (hn : 0 < n) : e ^ n ≠ 1 := by
  intro h
  refine he (isOfFinOrder_iff_pow_eq_one.2 ⟨n.toNat, by omega, ?_⟩)
  rw [← zpow_natCast, Int.toNat_of_nonneg hn.le, h]
private theorem regElt_key {K : Type} [Field K] (e x : Kˣ) (m k : ℕ) (hm : 2 ≤ m) (hk : 0 < k)
    (hx : x ^ k = (e ^ (m : ℤ)) ^ k) (he : ¬ IsOfFinOrder e) :
    ¬ IsOfFinOrder x ∧ ∀ i : ℤ, |i| ≤ 2 →
      ((x : K) + ((x⁻¹ : Kˣ) : K)) ^ 2 - 2 ≠ (e : K) ^ i + (e : K) ^ (-i) := by
  have hsq : ∀ j : ℤ, |j| ≤ 2 → x ^ 2 ≠ e ^ j := by
    intro j hj h
    have hj' := (abs_le.1 hj).2
    have hpos : 0 < (2 * (m : ℤ) - j) * (k : ℤ) := by
      have : (0 : ℤ) < k := by exact_mod_cast hk
      have : (2 : ℤ) ≤ m := by exact_mod_cast hm
      apply mul_pos <;> omega
    refine regElt_zpow_ne e he _ hpos ?_
    have h1 : (e ^ (m : ℤ)) ^ k * (e ^ (m : ℤ)) ^ k = (e ^ j) ^ k := by
      rw [← hx, ← h, ← pow_add, ← pow_mul, two_mul]
    have h2 : e ^ ((2 * (m : ℤ) - j) * (k : ℤ)) = (e ^ (m : ℤ)) ^ k * (e ^ (m : ℤ)) ^ k * ((e ^ j) ^ k)⁻¹ := by
      simp only [← zpow_natCast, ← zpow_mul, ← zpow_neg, ← zpow_add]
      congr 1
      ring
    rw [h2, h1, mul_inv_cancel]
  refine ⟨fun hf => ?_, fun i hi h => ?_⟩
  · obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    have hpos : 0 < (m : ℤ) * k * n := by
      have a : (0 : ℤ) < m := by exact_mod_cast (by omega : 0 < m)
      have b : (0 : ℤ) < k := by exact_mod_cast hk
      have c : (0 : ℤ) < n := by exact_mod_cast hn
      positivity
    refine regElt_zpow_ne e he _ hpos ?_
    rw [zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ← hx, ← pow_mul, mul_comm, pow_mul, h, one_pow]
  · have hx0 : (x : K) ≠ 0 := x.ne_zero
    have hE0 : ((e : K) ^ i) ≠ 0 := zpow_ne_zero _ e.ne_zero
    have hz : ((x : K) ^ 2 - (e : K) ^ i) * ((x : K) ^ 2 - ((e : K) ^ i)⁻¹) = 0 := by
      rw [Units.val_inv_eq_inv_val, zpow_neg] at h
      field_simp at h ⊢
      linear_combination (exp := 1) h
    rcases mul_eq_zero.1 hz with h0 | h0
    · refine hsq i hi (Units.ext ?_)
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]
      exact sub_eq_zero.1 h0
    · refine hsq (-i) (by rwa [abs_neg]) (Units.ext ?_)
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, zpow_neg]
      exact sub_eq_zero.1 h0
theorem UpperTheory.V.Z.Sym.Ga.exists_regular_elt_in_open_subgroup_infinite_order :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (M m : ℕ) (r : G L Ω →* GL (Fin 2) (Qbar l)), _root_.UpperTheory.V.Z.Sym.AdInAlt ι M m r → ∀ H : Subgroup (G L Ω), IsOpen (H : Set (G L Ω)) → ∃ s ∈ H, s ∉ Ga.Bad r ∧ ∃ a b : (Qbar l)ˣ, ¬ IsOfFinOrder (a / b) ∧ (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C (a : Qbar l)) * (X - C (b : Qbar l)) := by
  intro L Ω _ _ _ _ _ _ l _ ι M m r hr H hH
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  obtain ⟨A, hA⟩ := regElt_place (Ω := Ω) l (Fact.out)
  obtain ⟨b0, k, κ, hk, ⟨g, hg⟩, hκ⟩ := hr.above A hA
  obtain ⟨s, hsH, hsI, hinf⟩ := UpperTheory.V.Z.Sym.Ga.ineInf L Ω l A hA H hH
  let t : ↥(Dec (F := L) A) := ⟨s, Ine_le_Dec A hsI⟩
  obtain ⟨h0, h1⟩ := hκ t hsI
  have hcp : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C ((κ 0 t : (Qbar l)ˣ) : Qbar l)) * (X - C ((κ 1 t : (Qbar l)ˣ) : Qbar l)) := by
    have e : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
        (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
      exact Matrix.charpoly_units_conj g _
    rw [← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => (hg t).1 i j hij), Fin.prod_univ_two]
    have e0 : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((κ 0 t : (Qbar l)ˣ) : Qbar l) := (hg t).2 0
    have e1 : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = ((κ 1 t : (Qbar l)ˣ) : Qbar l) := (hg t).2 1
    rw [e0, e1]
  have hx : (κ 0 t / κ 1 t) ^ k = (cycBar L Ω l s ^ (m : ℤ)) ^ k := by
    rw [div_pow, h0, h1, zpow_add, mul_pow]
    exact mul_div_cancel_left _ _
  have key := regElt_key (cycBar L Ω l s) (κ 0 t / κ 1 t) m k hr.gap hk hx hinf
  refine ⟨s, hsH, ?_, κ 0 t, κ 1 t, key.1, hcp⟩
  rintro ⟨i, hi, hb⟩
  have huf := (UpperTheory.V.Z.Sym.Ga.ufFacts _ (r s)).1 _ _ hcp
  rw [huf] at hb
  exact key.2 i hi hb
end
end
