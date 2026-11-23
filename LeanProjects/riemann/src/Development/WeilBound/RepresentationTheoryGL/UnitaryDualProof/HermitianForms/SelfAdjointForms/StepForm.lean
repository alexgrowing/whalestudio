import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.SelfAdjointBounds.ReLeOfSelfadj
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.ColumnAlgebra.PiColElAdd
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.BlockContinuity.ContinuousBlkAt
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.TwistedKernels.TwKerColElStable
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.MirabolicVectors.ContinuousMulVec
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.BesselEstimates.ValLtOneOfNabs
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.Stab

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.LeviSmoothness.Final

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

theorem stepForm (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : StepForm k := by
  intro ψ hψ hψ1 m N hN V _ _ π hπ s B hpsd hk hmir
  have hB : Lv ψ hN π s B := ⟨hψ, hψ1, hπ, hpsd, hk, hmir⟩
  obtain ⟨A₀, hA₀⟩ := Ex.exists_lat (k := k) m
  obtain ⟨B', hD, hU⟩ := Ex.dens_exists_of hB (fun ξ A hA v w => alg.avg_selfadj hB ξ hA v w)
    (fun K hK _ hA₀ => stab.stab' hB K hK hA₀) hA₀
  refine ⟨B', props.dens_psd hB hA₀ hD, props.dens_kills hB hA₀ hD, props.dens_rad hB hA₀ hD, mir.dens_mir hB hA₀ hD,
    fun K hK => ?_, fun z hz v => besselOf.dens_bessel_of hB (fun K hK _ hA₀ => stab.stab' hB K hK hA₀) hA₀ hD z hz v⟩
  obtain ⟨A₁, hA₁, h01, hA⟩ := hU K hK
  refine ⟨(A₀.relIndex A₁ : ℝ), fun v hv => ?_⟩
  have e := hA v v hv hv A₁ hA₁ le_rfl
  rw [e]
  have hsa := alg.avg_selfadj hB (xi0 k m) hA₁ v v
  have key := asm.re_le_of_selfadj hpsd (avg ψ hN π (xi0 k m) A₁ v) v hsa
  have hc : ((A₀.relIndex A₁ : ℕ) : ℂ) = ((A₀.relIndex A₁ : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.re_ofReal_mul, hsa]
  exact mul_le_mul_of_nonneg_left key (Nat.cast_nonneg _)

end PositivityTheory.RgUd.Form.LeviSmoothness.Final
