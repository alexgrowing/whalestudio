import Formalism.LocalToGlobal.Columns.WordFin
import Formalism.LocalToGlobal.Columns.TiedPer

noncomputable section

namespace Formalism.L2.Col

theorem per_onto_dat (d : ColDat) (a : ColArgs d) :
    (∀ z ∈ (ptEv (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx).Fi, ∃ F, jMCL (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx a.rowOk F = z) ∧
      ∀ F, jMCL (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx a.rowOk F ∈ (ptEv (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx).Fi :=
  ⟨fun z hz => per_jMC_onto (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx a.rowOk d.hX z hz,
    fun F => per_jMC_mem_Fi (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx a.rowOk d.hX F⟩

end Formalism.L2.Col
