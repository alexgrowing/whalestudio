import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.StepForm
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerKer

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Dens

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

theorem uDens (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : UDens k := by
  intro ψ hψ hψ1 m N hN V _ _ π hπ s B hB A₀ hA₀
  have hL : Lv ψ hN π s B := ⟨hψ, hψ1, hπ, hB.1, hB.2.1, hB.2.2⟩
  obtain ⟨B', hD, -⟩ := Ex.dens_exists_of hL (fun ξ A hA v w => alg.avg_selfadj hL ξ hA v w)
    (fun K hK _ hA₀ => stab.stab' hL K hK hA₀) hA₀
  exact ⟨B', hD, props.dens_psd hL hA₀ hD, props.dens_kills hL hA₀ hD, mir.dens_mir hL hA₀ hD,
    fun v hv => props.dens_rad hL hA₀ hD v hv⟩

end PositivityTheory.RgUd.Form.U.Dens
