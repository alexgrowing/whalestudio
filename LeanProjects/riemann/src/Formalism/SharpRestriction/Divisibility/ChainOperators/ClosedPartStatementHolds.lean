import Formalism.PeriodIntegrals.ExplicitFormulaCounts.DvConv
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvProjA
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvProjB
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvProjC
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvGLatProj
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvGLatHerm
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvProjGram
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvProjRows
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvRatKer
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvFormEq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvTransferIdx
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvTransfer
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GTLower
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GTScale
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GTCoefTop
import Formalism.LocalRingCardinality.FactDelDualNabla

namespace Formalism.MainNotions.DIV

theorem closed_statements_hold : Formalism.MainNotions.PrimeDegreeVariant.ConclusionC := by
  obtain ⟨C, hC⟩ := division_transfer_indices
  exact ⟨ChkDv.c2a projection_sandwich g_lattice_projection, ChkDv.c2b projection_degree_bound g_lattice_projection,
    ChkDv.c2c projection_kernel_index g_lattice_projection, ChkDv.c2d projection_gram_det g_lattice_projection g_lattice_hermitian,
    ChkDv.c2E' projection_sandwich projection_degree_bound projection_kernel_index, ChkDv.c2dE.1 projection_gram_det,
    ⟨C, ChkDv.c4a division_transfer_ranks, ChkDv.c4b C hC⟩, gTLower_of Formalism.BasicNotions.factDelDualNabla, gelfand_tsetlin_scaling, gelfand_tsetlin_top_coeff,
    ChkDv.c7 projection_rows_bound g_lattice_projection g_lattice_hermitian, ChkDv.c7E.1 projection_rows_bound,
    ChkDv.c8 rational_kernel_division, ChkDv.c8b division_form_eq⟩

theorem closed_part_statement_holds : Formalism.MainNotions.PrimeDegreeVariant.PropositionCStatement := fun _ => closed_statements_hold

end Formalism.MainNotions.DIV
