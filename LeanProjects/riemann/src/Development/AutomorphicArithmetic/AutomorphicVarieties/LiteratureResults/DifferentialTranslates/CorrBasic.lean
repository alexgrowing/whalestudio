import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.EvFacts

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Dr.corrBasic :
    CorrBasic := by
  intro E _ _ _ a U Ξ q α w hc
  have two : ∀ (s : GL (Fin a) (Af E) ⧸ U) (p : HV E a) (v : Fin q → HV E a),
      w s p (fun i => (2 : ℝ) • v i) = (∏ _i : Fin q, (2 : ℝ)) • w s p v := fun s p v =>
    (w s p).toContinuousMultilinearMap.map_smul_univ (fun _ => (2 : ℝ)) v
  have hs : ∀ (g : GL (Fin a) (Cinf E)) (p : HV E a), sand g (sand g⁻¹ p) = p := fun g p => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hs' : ∀ (g : GL (Fin a) (Cinf E)) (p : HV E a), sand g⁻¹ (sand g p) = p := fun g p => by
    simpa using hs g⁻¹ p
  constructor
  · intro h s p hp v i hi
    obtain ⟨g, rfl⟩ := hp
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    have h0 : α (fun j => hv.symm (sand g⁻¹ (v j))) = 0 := by
      refine h _ i ?_
      rw [hi, hs']
      rfl
    have h1 := hc g x (fun j => hv.symm (sand g⁻¹ (v j)))
    simp only [LinearEquiv.apply_symm_apply, hs] at h1
    rw [h0, map_zero, two, Pi.zero_apply, Matrix.mulVec_zero] at h1
    exact (smul_eq_zero.1 h1).resolve_left (Finset.prod_ne_zero_iff.2 fun _ _ => two_ne_zero)
  · intro h X i hi
    apply (evFacts E a Ξ.d).1
    rw [map_zero]
    funext y
    set g := GeneralLinearGroup.map (pInf E) y
    set x := GeneralLinearGroup.map (pFin E) y
    have hy : infGL E a g * finGL E a x = y := infGL_mul_finGL y
    have h1 := hc g x X
    have hX : hv (X i) = hOne E a := congrArg hv (Subtype.ext hi)
    rw [two, h _ _ ⟨g, rfl⟩ (fun j => sand g (hv (X j))) i (by rw [hX]), smul_zero, hy] at h1
    have h2 := congrArg (fun v => Ξ.mat g⁻¹ *ᵥ v) h1
    simp only [Matrix.mulVec_zero, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] at h2
    exact h2.symm
