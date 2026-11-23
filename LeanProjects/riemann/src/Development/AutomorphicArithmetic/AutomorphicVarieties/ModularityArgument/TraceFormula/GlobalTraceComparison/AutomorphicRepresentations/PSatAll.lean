import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFlipGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem twist_loc (w : Pl E) (g : GLw n (GlobalTheory.EulerTw.cPl E w)) :
    thF E n (locGL E n (GlobalTheory.EulerTw.cPl E w) g) = locGL E n w (thetaGL n (RingHom.id _)
      (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g)) := by
  refine GlobalTheory.EulerTwU.gl_ext fun v => ?_
  rw [GlobalTheory.EulerTwU.pc_thF]
  by_cases h : v = w
  · subst h
    rw [pLoc_locGL, pLoc_locGL]
  · have h' : GlobalTheory.EulerTw.cPl E v ≠ GlobalTheory.EulerTw.cPl E w := fun e =>
      h (by rw [← GlobalTheory.EulerTwU.cPl_cPl v, e, GlobalTheory.EulerTwU.cPl_cPl])
    rw [pLoc_locGL_of_ne h', pLoc_locGL_of_ne h]
    exact (congrArg (thetaGL n (RingHom.id _)) (map_one _)).trans (map_one _)

private theorem twist_conj (w : Pl E) (g : GLw n (GlobalTheory.ThetaSatake.cw w)) :
    thF E n (locGL E n w (PhiU n (w.adicCompletion E) * GlobalTheory.CompanionTheory.ConjSat.flipGL w g * (PhiU n (w.adicCompletion E))⁻¹)) =
      locGL E n (GlobalTheory.ThetaSatake.cw w) g := by
  have e : thetaGL n (RingHom.id _) (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g) =
      PhiU n (w.adicCompletion E) * GlobalTheory.CompanionTheory.ConjSat.flipGL w g * (PhiU n (w.adicCompletion E))⁻¹ := by
    rw [GlobalTheory.CompanionTheory.ConjSat.flipGL_eq]
    rfl
  rw [← e, ← twist_loc w g, GlobalTheory.EulerTwU.thF_thF]
  rfl

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.satAll_pf :
    SatAll := by
  intro E _ _ _ n π w B y hy h0
  have hne : (⟨y, hy⟩ : π.V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  refine ⟨fun hB hf => ?_, fun hB hf => ?_⟩
  · rw [CG.hasSat_mk] at hB
    have hx : (⟨y, hy⟩ : π.V) ∈ fixed (π.locRep w) (KGL w n) :=
      GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hf k hk)
    exact (hB.2 _ hx hne).map (ρ' := rw' n w false) π.V.subtype (fun _ _ => rfl) h0
  · rw [CG.hasSat_mk] at hB
    let σ : Representation ℂ (GLw n w) π.V := π.finPart.comp (jw n w true)
    let k := PhiU n (w.adicCompletion E)
    let T : π.V ≃ₗ[ℂ] π.V := LinearEquiv.ofLinear (σ k⁻¹) (σ k)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    have hs : HasSatGL w σ (B.map (·⁻¹)) :=
      GlobalTheory.ThetaSatake.hasSatGL_of_invT (GlobalTheory.ThetaSatake.cloc w) (conjLoc_spec _ w).2.2
        (GlobalTheory.ThetaSatake.absNorm_cw w).symm T (fun g x => ?_) hB
    · have hx : (⟨y, hy⟩ : π.V) ∈ fixed σ (KGL w n) :=
        GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hf k hk)
      exact (hs.2 _ hx hne).map (ρ' := rw' n w true) π.V.subtype (fun _ _ => rfl) h0
    · have e : π.locRep (GlobalTheory.ThetaSatake.cw w) g = σ (k * GlobalTheory.CompanionTheory.ConjSat.flipGL w g * k⁻¹) := by
        change π.finPart (locGL E n (GlobalTheory.ThetaSatake.cw w) g) = π.finPart (thF E n (locGL E n w _))
        rw [twist_conj]
      change σ (GlobalTheory.CompanionTheory.ConjSat.flipGL w g) (σ k⁻¹ x) = σ k⁻¹ (π.locRep (GlobalTheory.ThetaSatake.cw w) g x)
      rw [e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group

end
