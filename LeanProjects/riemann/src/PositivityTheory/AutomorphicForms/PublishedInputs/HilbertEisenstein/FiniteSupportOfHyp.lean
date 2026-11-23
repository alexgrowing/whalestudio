import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix nonZeroDivisors
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem finite_support_of_hyp {χ : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp χ c) :
    {w | c w ≠ 0}.Finite := by
  obtain ⟨m, hm, h⟩ := (isOfFinOrder_iff_pow_eq_one).mp H.fin
  have ho := GlobalTheory.HeckeGal.isOpen_ker_of_pow χ.1 χ.2.1 hm fun x => congrArg (fun ξ : HChar F => ξ.1 x) h
  obtain ⟨S, M, hS, key⟩ := GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen χ.1.ker ho
  refine hS.subset fun w hw => ?_
  by_contra hwS
  apply hw
  have h0 : (0 : ℕ) ∈ {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
      Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ.loc w x = 1} := by
    intro x hx _
    exact key w x hx fun h => absurd h hwS
  exact Nat.le_zero.mp ((H.cond w).2 h0)

omit [IsTotallyReal F] in
theorem exists_int_of_val (x : F)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v (pLoc F w (algebraMap F (Af F) x)) ≤ 1) :
    ∃ s : 𝓞 F, x = (s : F) := by
  have h' : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ 1 := by
    intro w
    have := h w
    rwa [show pLoc F w (algebraMap F (Af F) x) = (x : w.adicCompletion F) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  obtain ⟨s, hs⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F x h'
  exact ⟨s, hs.symm⟩

omit [IsTotallyReal F] in

theorem exists_den_compact {ι : Type} [Finite ι] {C : Set (Ideles F)} (hC : IsCompact C)
    (f : ι → Ideles F → Af F) (hf : ∀ i, Continuous (f i)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ C, ∀ i, ∀ w : HeightOneSpectrum (𝓞 F),
      Valued.v (pLoc F w (algebraMap F (Af F) (d : F) * f i a)) ≤ 1 := by
  have hS : IsCompact (⋃ i, f i '' C) := isCompact_iUnion fun i => hC.image (hf i)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  exact ⟨d, hd0, fun a ha i w => hd _ (Set.mem_iUnion.mpr ⟨i, a, ha, rfl⟩) w⟩

omit [IsTotallyReal F] in
theorem val_sum_two_le {w : HeightOneSpectrum (𝓞 F)} (x : Fin 2 → w.adicCompletion F)
    (h : ∀ j, Valued.v (x j) ≤ 1) : Valued.v (∑ j, x j) ≤ 1 := by
  rw [Fin.sum_univ_two]
  exact le_trans (Valuation.map_add _ _ _) (max_le (h 0) (h 1))

omit [IsTotallyReal F] in
theorem coe_Mcol_apply' (g : GA F 2) (a : Ideles F) (j i : Fin 2) :
    ((g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) j i =
      ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) j i * ((a⁻¹ : Ideles F) : Ad F) := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal]

omit [IsTotallyReal F] in
theorem coe_Mrow_apply' (g : GA F 2) (a : Ideles F) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) i j =
      ((a : Ideles F) : Ad F) * ((g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) i j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal]

omit [IsTotallyReal F] in
theorem scalar_mul_mul_inv (g : GA F 2) (a : Ideles F) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *
      ((g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) = 1 := by
  rw [← Units.val_mul]
  simp [mul_assoc]

omit [IsTotallyReal F] in
theorem pFin_algebraMap (x : F) : pFin F (algebraMap F (Ad F) x) = algebraMap F (Af F) x := rfl

omit [IsTotallyReal F] in
theorem pFin_units (a : Ideles F) :
    pFin F ((a : Ideles F) : Ad F) = ((IdeleGroup.toFinite F a : (Af F)ˣ) : Af F) := rfl

theorem exists_den_row (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) {C : Set (Ideles F)} (hC : IsCompact C) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ C, ∀ ξ : Fin 2 → F,
      (∀ w, Valued.v (pLoc F w (pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) :
          Matrix (Fin 2) (Fin 2) (Ad F))) 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) :
          Matrix (Fin 2) (Fin 2) (Ad F))) 1)) - 1) ≤ WithZero.exp (-(c w : ℤ))) →
      ∀ i, ∃ s : 𝓞 F, (d : F) * ξ i = s := by
  obtain ⟨d, hd0, hd⟩ := exists_den_compact (ι := Fin 2 × Fin 2) hC
    (fun p a => pFin F (((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) p.1 p.2) *
      ((IdeleGroup.toFinite F a⁻¹ : (Af F)ˣ) : Af F))
    (fun p => continuous_const.mul (Units.continuous_val.comp
      ((IdeleGroup.continuous_toFinite (K := F)).comp continuous_inv)))
  refine ⟨d, hd0, fun a ha ξ hξ i => ?_⟩
  set row := rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) :
    Matrix (Fin 2) (Fin 2) (Ad F)) with hrow_def
  have hle1 : ∀ w : HeightOneSpectrum (𝓞 F), WithZero.exp (-(c w : ℤ)) ≤ 1 := fun w => by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hint : ∀ j w, Valued.v (pLoc F w (pFin F (row j))) ≤ 1 := by
    intro j w
    obtain ⟨h0, h1⟩ := hξ w
    fin_cases j
    · exact h0.trans (hle1 w)
    · have e : pLoc F w (pFin F (row 1)) = (pLoc F w (pFin F (row 1)) - 1) + 1 := by ring
      change Valued.v (pLoc F w (pFin F (row 1))) ≤ 1
      rw [e]
      exact Valuation.map_add_le _ (h1.trans (hle1 w)) (by rw [Valuation.map_one])
  have hrow : rowA ξ = row ᵥ* ((g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)) := by
    rw [hrow_def, Matrix.vecMul_vecMul, scalar_mul_mul_inv, Matrix.vecMul_one]
  have hx : algebraMap F (Af F) (ξ i) = ∑ j, pFin F (row j) *
      (pFin F (((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) j i) *
        ((IdeleGroup.toFinite F a⁻¹ : (Af F)ˣ) : Af F)) := by
    have h2 := congrArg (fun v => pFin F (v i)) hrow
    simp only [Matrix.vecMul, dotProduct, coe_Mcol_apply', map_sum, map_mul] at h2
    rw [← pFin_algebraMap]
    exact h2
  apply exists_int_of_val
  intro w
  rw [map_mul, hx, Finset.mul_sum, map_sum]
  apply val_sum_two_le
  intro j
  rw [mul_left_comm, map_mul, Valuation.map_mul]
  exact mul_le_one' (hint j w) (hd a ha (j, i) w)

omit [IsTotallyReal F] in
theorem exists_elem_col (c : HeightOneSpectrum (𝓞 F) → ℕ) (hc : {w | c w ≠ 0}.Finite) :
    ∃ e : 𝓞 F, e ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      Valued.v (pLoc F w (algebraMap F (Af F) (e : F))) ≤ WithZero.exp (-((c w : ℤ) + dd w)) := by
  classical
  set Cfr : FractionalIdeal (𝓞 F)⁰ F :=
    ∏ᶠ w : HeightOneSpectrum (𝓞 F), (w.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ (c w : ℤ)
  set Dfr : FractionalIdeal (𝓞 F)⁰ F := ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  have hexp : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (c w : ℤ) = 0 := by
    rw [Filter.eventually_cofinite]
    refine hc.subset fun w hw => ?_
    simpa using hw
  have hD0 : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have hDfr0 : Dfr ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hD0
  have hCfr0 : Cfr ≠ 0 := by
    apply finprod_induction (p := fun I : FractionalIdeal (𝓞 F)⁰ F => I ≠ 0)
    · exact one_ne_zero
    · exact fun x y hx hy => mul_ne_zero hx hy
    · exact fun w => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)
  have hJ0 : Cfr * Dfr ≠ 0 := mul_ne_zero hCfr0 hDfr0
  have hcount : ∀ w : HeightOneSpectrum (𝓞 F), FractionalIdeal.count F w (Cfr * Dfr) = (c w : ℤ) + dd w := by
    intro w
    rw [FractionalIdeal.count_mul F w hCfr0 hDfr0, FractionalIdeal.count_finprod F w _ hexp,
      FractionalIdeal.count_coe F w hD0]
    rfl
  obtain ⟨k, hkJ, hk0⟩ : ∃ k ∈ Cfr * Dfr, k ≠ 0 := by
    have hne : ((Cfr * Dfr : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) ≠ ⊥ := by
      rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
      exact hJ0
    exact Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hval : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F k ≤ WithZero.exp (-((c w : ℤ) + dd w)) := fun w => by
    have h1 := valuation_le_of_mem_fractionalIdeal w hkJ
    rwa [hcount] at h1
  have hdd : ∀ w : HeightOneSpectrum (𝓞 F), 0 ≤ dd w := fun w => by unfold dd; positivity
  have hle1 : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F k ≤ 1 := fun w =>
    (hval w).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; have := hdd w; omega)
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F k hle1
  have hrk : (r : F) = k := hr
  refine ⟨r, ?_, fun w => ?_⟩
  · rintro rfl
    apply hk0
    rw [← hrk]
    rfl
  · change Valued.v ((r : F) : w.adicCompletion F) ≤ _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hrk]
    exact hval w

theorem exists_den_col (c : HeightOneSpectrum (𝓞 F) → ℕ) (hc : {w | c w ≠ 0}.Finite) (g : GA F 2)
    {C : Set (Ideles F)} (hC : IsCompact C) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ C, ∀ ξ : Fin 2 → F,
      (∀ w, Valued.v (pLoc F w (pFin F ((((g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ : GA F 2) :
          Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ) 0))) ≤ WithZero.exp ((c w : ℤ) + dd w) ∧
        Valued.v (pLoc F w (pFin F ((((g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ : GA F 2) :
          Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ) 1))) ≤ WithZero.exp ((c w : ℤ) + dd w)) →
      ∀ i, ∃ s : 𝓞 F, (d : F) * ξ i = s := by
  obtain ⟨e, he0, he⟩ := exists_elem_col c hc
  obtain ⟨d, hd0, hd⟩ := exists_den_compact (ι := Fin 2 × Fin 2) hC
    (fun p a => ((IdeleGroup.toFinite F a : (Af F)ˣ) : Af F) *
      pFin F (((g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) p.1 p.2))
    (fun p => (Units.continuous_val.comp (IdeleGroup.continuous_toFinite (K := F))).mul continuous_const)
  refine ⟨d * e, mul_ne_zero hd0 he0, fun a ha ξ hξ i => ?_⟩
  set col := ((g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ : GA F 2) :
    Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ with hcol_def
  have hint : ∀ j w, Valued.v (pLoc F w (algebraMap F (Af F) (e : F) * pFin F (col j))) ≤ 1 := by
    intro j w
    obtain ⟨h0, h1⟩ := hξ w
    have hj : Valued.v (pLoc F w (pFin F (col j))) ≤ WithZero.exp ((c w : ℤ) + dd w) := by
      fin_cases j
      · exact h0
      · exact h1
    rw [map_mul, Valuation.map_mul]
    calc Valued.v (pLoc F w (algebraMap F (Af F) (e : F))) * Valued.v (pLoc F w (pFin F (col j)))
        ≤ WithZero.exp (-((c w : ℤ) + dd w)) * WithZero.exp ((c w : ℤ) + dd w) := mul_le_mul' (he w) hj
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  have hcol : rowA ξ = ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ col := by
    rw [hcol_def, Matrix.mulVec_mulVec, scalar_mul_mul_inv, Matrix.one_mulVec]
  have hx : algebraMap F (Af F) (ξ i) = ∑ j, (((IdeleGroup.toFinite F a : (Af F)ˣ) : Af F) *
      pFin F (((g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) i j)) * pFin F (col j) := by
    have h2 := congrArg (fun v => pFin F (v i)) hcol
    simp only [Matrix.mulVec, dotProduct, coe_Mrow_apply', map_sum, map_mul] at h2
    rw [← pFin_algebraMap]
    exact h2
  apply exists_int_of_val
  intro w
  have e1 : algebraMap F (Af F) ((d : F) * (e : F) * ξ i) = ∑ j,
      (algebraMap F (Af F) (d : F) * (((IdeleGroup.toFinite F a : (Af F)ˣ) : Af F) *
        pFin F (((g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) i j))) *
      (algebraMap F (Af F) (e : F) * pFin F (col j)) := by
    rw [map_mul, map_mul, hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have e2 : (((d * e : 𝓞 F)) : F) = (d : F) * (e : F) := by push_cast; ring
  rw [e2, e1, map_sum]
  apply val_sum_two_le
  intro j
  rw [map_mul, Valuation.map_mul]
  exact mul_le_one' (hd a ha (i, j) w) (hint j w)

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
