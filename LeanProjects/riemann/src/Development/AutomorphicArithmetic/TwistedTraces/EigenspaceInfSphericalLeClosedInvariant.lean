import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CompatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C

theorem UpperTheory.eigenspace_inf_spherical_le_closed_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
        (V : Submodule ℂ (LL μ)) (a : TI K n) (x : ℝ) (P : Finset (Pl K)), IsSummand μ V →
        eigIn V (Oinf μ ν a) x ⊓ sphOff μ P ≤ V ∧
        IsClosed ((eigIn V (Oinf μ ν a) x ⊓ sphOff μ P : Submodule ℂ (LL μ)) : Set (LL μ)) ∧
        ∀ w ∈ P, ∀ (g : Gw n w), ∀ u ∈ eigIn V (Oinf μ ν a) x ⊓ sphOff μ P, rhoL μ w g u ∈ eigIn V (Oinf μ ν a) x ⊓ sphOff μ P := by
  intro K _ _ n hn μ _ ν _ V a x P hV
  obtain ⟨m, hm, -⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ ν
  have hO : ∀ h, Commute (Oinf μ ν a) (rhoF μ h) := (UpperTheory.ConvolutionTheory.Tf.opAlg K n μ ν m).2.2.2.2.2.2.2.2 a
  have hmul : ∀ (h h' : AdelicGLn.FiniteAdelicGL K n) (u : LL μ), rhoF μ h (rhoF μ h' u) = rhoF μ (h * h') u := by
    intro h h' u
    simp only [rhoF, map_mul, UnitaryRep.map_mul_apply]
  have hmem : ∀ u, u ∈ eigIn V (Oinf μ ν a) x ⊓ sphOff μ P ↔ (u ∈ V ∧ Oinf μ ν a u = (x : ℂ) • u) ∧
      ∀ v ∉ P, ∀ k ∈ GLnLocal.integralGL (v.adicCompletion K) n, rhoL μ v k u = u := by
    intro u
    simp only [eigIn, sphOff, fixL, fixF, rhoL, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff,
      LinearMap.mem_eqLocus, Subgroup.mem_map]
    simp
  refine ⟨fun u hu => ((hmem u).1 hu).1.1, ?_, ?_⟩
  · have : ((eigIn V (Oinf μ ν a) x ⊓ sphOff μ P : Submodule ℂ (LL μ)) : Set (LL μ)) =
        ((V : Set (LL μ)) ∩ {u | Oinf μ ν a u = (x : ℂ) • u}) ∩
          ⋂ v ∈ {v : Pl K | v ∉ P}, ⋂ k ∈ {k | k ∈ GLnLocal.integralGL (v.adicCompletion K) n}, {u | rhoL μ v k u = u} := by
      ext u
      simp only [SetLike.mem_coe, hmem, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    refine (hV.closed.inter (isClosed_eq (Oinf μ ν a).continuous (continuous_const_smul _))).inter ?_
    exact isClosed_biInter fun v _ => isClosed_biInter fun k _ => isClosed_eq (rhoL μ v k).continuous continuous_id
  · intro w hw g u hu
    obtain ⟨⟨huV, huA⟩, hus⟩ := (hmem u).1 hu
    refine (hmem _).2 ⟨⟨hV.inv _ _ huV, ?_⟩, fun v hv k hk => ?_⟩
    · have := congrArg (fun T : LL μ →L[ℂ] LL μ => T u) (hO (AdelicGLn.localEmbedding w g)).eq
      simp only [ContinuousLinearMap.mul_apply] at this
      change Oinf μ ν a (rhoF μ _ u) = _
      rw [this, huA, map_smul]
      rfl
    · have hne : w ≠ v := fun e => hv (e ▸ hw)
      have hc := ((UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 v hne.symm g k)
      change rhoF μ _ (rhoF μ _ u) = rhoF μ _ u
      rw [hmul, ← hc, ← hmul]
      have := hus v hv k hk
      rw [rhoL] at this
      rw [this]
