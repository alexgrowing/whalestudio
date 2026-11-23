import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AvgZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SmCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinConstantTermUpperBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PeriodicIntegralFundamentalDomainInvariant
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
import GroundTheory.AutomorphicForms.StrongApproximationSLDense

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf Filter Topology
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Br

private theorem cm_aff_add {R : Type} [CommRing R] (x y : R) : aff 1 (x + y) = aff 1 x * aff 1 y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem cm_map_aff {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map p (aff 1 x) = aff 1 (p x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.GeneralLinearGroup.map]

private theorem cm_aff_zero {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem cm_continuous_aff {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun x : R => aff (1 : Rˣ) x := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · change Continuous fun x : R => (!![(((1 : Rˣ)⁻¹ : Rˣ) : R), -((((1 : Rˣ)⁻¹ : Rˣ) : R) * x); 0, 1] : Matrix (Fin 2) (Fin 2) R)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private noncomputable def eR (t : ℝ) : Ad ℚ := TR.sInf ℚ (algebraMap ℝ (TR.Rinf ℚ) t)

private theorem pInf_eR (t : ℝ) : TR.pInf ℚ (eR t) = algebraMap ℝ (TR.Rinf ℚ) t := (TR.infEq ℚ).symm_apply_apply _

private theorem pFin_eR (t : ℝ) : pFin ℚ (eR t) = 0 := rfl

private theorem pInf_sFin (a : Af ℚ) : TR.pInf ℚ (sFin ℚ a) = 0 := map_zero (TR.infEq ℚ).symm

private theorem pFin_sFin (a : Af ℚ) : pFin ℚ (sFin ℚ a) = a := rfl

private theorem pInf_rat (q : ℚ) : TR.pInf ℚ (algebraMap ℚ (Ad ℚ) q) = algebraMap ℝ (TR.Rinf ℚ) (q : ℝ) :=
  DFunLike.congr_fun (Subsingleton.elim ((TR.pInf ℚ).comp (algebraMap ℚ (Ad ℚ)))
    ((algebraMap ℝ (TR.Rinf ℚ)).comp (Rat.castHom ℝ))) q

private theorem pFin_rat (q : ℚ) : pFin ℚ (algebraMap ℚ (Ad ℚ) q) = algebraMap ℚ (Af ℚ) q := rfl

private theorem eR_add (s t : ℝ) : eR (s + t) = eR s + eR t := by simp only [eR, map_add]

private theorem cm_upR_aff (t : ℝ) : upR (aff 1 t) = aff 1 (eR t) :=
  TR.ga_ext (by simp [upR, cm_map_aff, pInf_eR]) (by simp [upR, cm_map_aff, pFin_eR, cm_aff_zero])

private theorem cm_finGL_aff (a : Af ℚ) : finGL ℚ 2 (aff 1 a) = aff 1 (sFin ℚ a) :=
  TR.ga_ext (by simp [cm_map_aff, pInf_sFin, cm_aff_zero]) (by simp [cm_map_aff, pFin_sFin])

private theorem cm_decomp (x : Ad ℚ) (q : ℚ) :
    ∃ s : ℝ, x = algebraMap ℚ (Ad ℚ) q + eR s + sFin ℚ (pFin ℚ x - algebraMap ℚ (Af ℚ) q) := by
  refine ⟨ev (TR.pInf ℚ x) - q, TR.ad_ext ?_ ?_⟩
  · rw [map_add, map_add, pInf_rat, pInf_eR, pInf_sFin, add_zero, ← map_add, add_sub_cancel]
    funext v
    rw [Subsingleton.elim v Rat.infinitePlace]
    rfl
  · rw [map_add, map_add, pFin_rat, pFin_eR, pFin_sFin, add_zero, add_sub_cancel]

private theorem cm_mean {ψ : Ad ℚ → ℂ} {U : Set (Af ℚ)} (hU : IsOpen U) (h0 : 0 ∈ U) {N : ℕ} (hN : (N : Af ℚ) ∈ U)
    (hq : ∀ (q : ℚ) x, ψ (algebraMap ℚ (Ad ℚ) q + x) = ψ x) (hu : ∀ a ∈ U, ∀ x, ψ (x + sFin ℚ a) = ψ x) :
    Function.Periodic (fun t : ℝ => ψ (eR t)) N ∧ ∀ x, ∫ t in (0 : ℝ)..N, ψ (eR t + x) = ∫ t in (0 : ℝ)..N, ψ (eR t) := by
  have hp : Function.Periodic (fun t : ℝ => ψ (eR t)) N := fun t => by
    have e : eR (t + N) + sFin ℚ (N : Af ℚ) = algebraMap ℚ (Ad ℚ) (N : ℚ) + eR t := by
      refine TR.ad_ext ?_ ?_
      · rw [map_add, map_add, pInf_rat, pInf_eR, pInf_eR, pInf_sFin, add_zero, Rat.cast_natCast, map_add, add_comm]
      · rw [map_add, map_add, pFin_rat, pFin_eR, pFin_eR, pFin_sFin, zero_add, add_zero, map_natCast]
    beta_reduce
    rw [← hu _ hN, e, hq]
  refine ⟨hp, fun x => ?_⟩
  obtain ⟨q, hq'⟩ := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing ℚ).exists_mem_open
    (hU.preimage (continuous_const.sub continuous_id : Continuous fun z : Af ℚ => pFin ℚ x - z)) ⟨pFin ℚ x, by simpa using h0⟩
  obtain ⟨s, hs⟩ := cm_decomp x q
  have e : ∀ t, ψ (eR t + x) = ψ (eR (t + s)) := fun t => by
    rw [hs, ← add_assoc, hu (pFin ℚ x - algebraMap ℚ (Af ℚ) q) hq', add_left_comm, hq, eR_add]
  simp only [e]
  rw [intervalIntegral.integral_comp_add_right (fun t => ψ (eR t)) s, zero_add, add_comm,
    hp.intervalIntegral_add_eq s 0, zero_add]

open GroundTheory.Automorphic.AutomorphicForm in
private theorem cm_fund : ∃ (_ : MeasurableSpace (BlockIx 2 1 → Ad ℚ)) (_ : BorelSpace (BlockIx 2 1 → Ad ℚ))
    (μ : Measure (BlockIx 2 1 → Ad ℚ)) (D : Set (BlockIx 2 1 → Ad ℚ)), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratN ℚ 2 1) D μ := by
  have hμ : (unipMeasure ℚ 2 1).IsAddHaarMeasure := inferInstance
  have hB : BorelSpace (UPos 2 1 → AdeleRing (𝓞 ℚ) ℚ) := inferInstance
  have hL : ratN ℚ 2 1 = unipLattice ℚ 2 1 := AddSubgroup.ext fun x =>
    ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
  exact ⟨_, hB, unipMeasure ℚ 2 1, unipFundamentalDomain ℚ 2 1, hμ, by
    rw [hL]; exact isAddFundamentalDomain_unipFundamentalDomain⟩

end UpperTheory.V.Br

open UpperTheory.V.Br in
theorem UpperTheory.V.Br.cuspMean :
    UpperTheory.V.Br.CuspMean := by
  intro φ hφ g
  have hl := hφ.1.left
  have ho := hφ.1.level
  set u : GL (Fin 2) (Af ℚ) := Matrix.GeneralLinearGroup.map (pFin ℚ) g with hu
  have hc : Continuous fun x : Af ℚ => u⁻¹ * aff 1 x * u := (continuous_const.mul cm_continuous_aff).mul continuous_const
  have hU := ho.preimage hc
  have h0 : (0 : Af ℚ) ∈ (fun x : Af ℚ => u⁻¹ * aff 1 x * u) ⁻¹' {k | TR.finRep ℚ 2 k φ = φ} := by
    simp [cm_aff_zero]
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele ℚ).eventually (hU.mem_nhds h0)).exists
  refine ⟨n.factorial, n.factorial_pos, fun y => ?_⟩
  set N : ℕ := n.factorial
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 n.factorial_pos
  have hq : ∀ (q : ℚ) x, φ.1 (aff 1 (algebraMap ℚ (Ad ℚ) q + x) * (g * upR y)) = φ.1 (aff 1 x * (g * upR y)) := fun q x => by
    rw [cm_aff_add, ← cm_map_aff, mul_assoc]
    exact hl _ _
  obtain ⟨hp, hm⟩ := cm_mean (ψ := fun x => φ.1 (aff 1 x * (g * upR y))) hU h0 hn hq fun a ha x => by
    have h1 : ∀ g, φ.1 (g * finGL ℚ 2 (u⁻¹ * aff 1 a * u)) = φ.1 g := fun g => congrFun (congrArg Subtype.val ha) g
    have e1 : g * upR y * finGL ℚ 2 (u⁻¹ * aff 1 a * u) = finGL ℚ 2 (aff 1 a) * (g * upR y) :=
      TR.ga_ext (by simp) (by simp [upR, ← hu, mul_assoc])
    rw [cm_aff_add, ← cm_finGL_aff, mul_assoc, ← e1, ← mul_assoc, h1]
  simp only [cm_upR_aff]
  refine ⟨hp, ?_⟩
  set c := ∫ t in (0 : ℝ)..N, φ.1 (aff 1 (eR t) * (g * upR y))
  obtain ⟨_, _, μ, D, hμ, hD⟩ := cm_fund
  obtain ⟨i1, i2, i3, i4, hco, hcu, hx⟩ := UpperTheory.eisenstein_constantTerm_upperBlock ℚ
  have hψ : Continuous fun x : BlockIx 2 1 → Ad ℚ => φ.1 (unip x * (g * upR y)) :=
    (smCont ℚ 2 φ ho).comp (hcu.mul continuous_const)
  have hinv : ∀ γ ∈ ratN ℚ 2 1, ∀ x, φ.1 (unip (γ + x) * (g * upR y)) = φ.1 (unip x * (g * upR y)) := by
    rintro _ ⟨q, rfl⟩ x
    rw [hx, hx]
    exact hq _ _
  obtain ⟨hfin, hP⟩ := UpperTheory.periodic_integral_fundamentalDomain_invariant _ (ratN ℚ 2 1) hco μ D hD
  have hint := (hP _ hinv).1 hψ
  have he : Continuous fun (t : ℝ) (_ : BlockIx 2 1) => eR t := continuous_pi fun _ =>
    (((TR.continuous_infEq ℚ).comp (continuous_algebraMap ℝ (TR.Rinf ℚ))).prodMk continuous_const :
      Continuous fun t : ℝ => ((TR.infEq ℚ (algebraMap ℝ (TR.Rinf ℚ) t), 0) :
        InfiniteAdeleRing ℚ × Af ℚ))
  have key := avgZero _ (ratN ℚ 2 1) μ D hμ hD (fun x => φ.1 (unip x * (g * upR y)) - c / N) (hψ.sub continuous_const)
    (fun γ hγ x => by rw [hinv γ hγ]) _ he N hN fun x => by
      have h2 : Continuous fun t : ℝ => φ.1 (unip ((fun _ => eR t) + x) * (g * upR y)) := hψ.comp (he.add continuous_const)
      rw [intervalIntegral.integral_sub (h2.intervalIntegrable _ _) (by simp)]
      simp only [hx]
      rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul, Complex.ofReal_natCast,
        mul_div_cancel₀ _ (Nat.cast_ne_zero.2 n.factorial_pos.ne'), sub_eq_zero]
      exact hm _
  rw [integral_sub hint (integrableOn_const hfin), hφ.2 1 one_pos one_lt_two μ D hμ hD, setIntegral_const, zero_sub, neg_eq_zero,
    smul_eq_zero, div_eq_zero_iff] at key
  rcases key with key | key | key
  · exact absurd key (ENNReal.toReal_ne_zero.2 ⟨hD.measure_ne_zero (NeZero.ne μ), hfin⟩)
  · exact key
  · exact absurd key (Nat.cast_ne_zero.2 n.factorial_pos.ne')
