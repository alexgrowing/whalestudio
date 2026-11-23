import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.IndAutCs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistConjugateSelfDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Base UpperTheory.V.Z.Bc UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
private theorem infOf_two (m : Fin 2 → ℤ) : infOf m = {1 / 2 + (m 0 : ℂ), 1 / 2 + (m 1 : ℂ)} := by
  have e : (((2 : ℕ) : ℂ) - 1) / 2 = 1 / 2 := by norm_num
  rw [infOf, e]
  rfl
private theorem infOf_add {m m' : Fin 2 → ℤ} (h : Function.Injective ![m 0, m 1, m' 0, m' 1]) :
    (infOf m + infOf m').Nodup ∧ ∀ z ∈ infOf m + infOf m', ∃ n : ℤ, z = (n : ℂ) + (((4 : ℕ) : ℂ) - 1) / 2 := by
  have e : infOf m + infOf m' = Finset.univ.val.map fun i => 1 / 2 + ((![m 0, m 1, m' 0, m' 1] i : ℤ) : ℂ) := by
    rw [infOf_two, infOf_two]
    rfl
  rw [e]
  refine ⟨Finset.univ.nodup.map fun i j hij => h (Int.cast_injective (add_left_cancel hij)), fun z hz => ?_⟩
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
  exact ⟨![m 0, m 1, m' 0, m' 1] i - 1, by push_cast; ring⟩
private theorem tw_back {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    (R : G F Ω →* GL (Fin 4) (Qbar l)) : R = tw (tw R (cycBar F Ω l)⁻¹) (cycBar F Ω l ^ (1 : ℤ) * 1) := by
  refine MonoidHom.ext fun s => Units.ext ?_
  rw [tw_val, tw_val, smul_smul, ← Units.val_mul]
  simp
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutCs_of_alt (hP : _root_.UpperTheory.V.Af.Hypotheses') (h : IndCs) : IndAutCs := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ h2 l _ ι π r hatt hm hb R hR H
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩
  obtain ⟨P, hfin, hinf⟩ := h K M h2 π hm hb
  have key : IsAutC ι (tw R (cycBar K Ω l)⁻¹) := by
    refine ⟨P, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun φ => ?_, attInd K M Ω h2 l ι r R (CG.mk π).HasSat (CG.mk P).HasSat (fun _ _ _ h h' => h.unique h') (fun _ _ _ h h' => h.unique h') hatt hfin hR H⟩
    obtain ⟨m, m', τ, τ', hne, rfl, e, hv, hv', hinj⟩ := hm φ
    rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hinf τ τ' _ _ hne e.symm hv hv')]
    exact infOf_add hinj
  rw [tw_back R]
  exact _root_.UpperTheory.V.Sd.twist_conjugate_selfDual hP K Ω l ι 4 _ _ ((_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hP K Ω l ι).1 1 1 (by simp)) key
end
