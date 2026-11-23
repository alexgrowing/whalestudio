import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCharSurjectiveAndMapRangeAl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCobOneOfIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelReductionHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosureBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialisingOpenExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatesIntoHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianCubeFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValuesIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIntegralLocalToFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationTorsionTowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupTateLieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivGroupTateLieCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichPointPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAnnihilatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEqDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTorusLeLieSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFinrankOfCokernelStatement

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.HTKernel

theorem hodgeTateKernelAtPoint_of_dieudonne (h : GlobalTheory.Published.PrismaticDieudonneHodge) :
    GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  have hv := P.integers
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  obtain ⟨ε, hε₁⟩ := ReciprocityTheory.PGsh.exists_eps (p := p) C _ O hv
  have hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε := GlobalTheory.PrismModel.isPrimitiveSystem_of_one hε₁
  have hS := GlobalTheory.DieudonneSandwich.hodgeTateSandwich_of_prismaticDieudonne₂ h p C v O hv ε hε
  obtain ⟨G, e, l, c, ζ, tw, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_pdiv_group_tate_lie p C v O Λ P
  obtain ⟨hf, hfr, hb⟩ := GlobalTheory.T.pDivGroup_omega_finite_free_and_p_sq_mem_dlog_span p C v O ε hε hv hS G
  have hcok : CokernelBound P := GlobalTheory.T.pdiv_group_tate_lie_compat p C v O Λ P G e l c ζ h1 h2 h3 hf hfr hb
  have hint : WeilIntegralFinite P := GlobalTheory.T.weil_integral_local_to_finite p C v O Λ P (GlobalTheory.T.weil_pairing_integral p C v O Λ P (GlobalTheory.T.polarized_abelian_cube_function C P.A)
    (GlobalTheory.T.trivialising_open_exists p C v O Λ P (GlobalTheory.T.special_fibre_not_in_closure p C v O hv)) (GlobalTheory.T.translates_into_holds p C v O Λ P)
    (GlobalTheory.T.cube_values_integral p C v O Λ P (GlobalTheory.T.local_units_holds p C v O hv)))
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_polarization_torsion_tower p C v O Λ P hint G tw
  have hiso := GlobalTheory.T.hodge_tate_sandwich_point_property p C v O Λ P ε hε hS G e l c ζ φ h1 h2 h3 fun s s' => muRoot_ext fun n =>
    hv.hom_inj (by
      rw [hφ, muRoot_smul, map_pow, h5, ← h4, ← h4, ← pow_pairT P.A P.eps, Units.val_pow_eq_pow_val])
  obtain ⟨horth, hrank⟩ := GlobalTheory.T.hodge_tate_kernel_annihilator p C v O Λ P
  have hdim := GlobalTheory.T.finrank_W_eq_dimension p C v O Λ P hcok
  have hle : Submodule.span C (Set.range P.bLie) ≤ P.W :=
    Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact (hiso x).1)
  have hW : P.W = Submodule.span C (Set.range P.bLie) :=
    (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  refine ⟨GlobalTheory.T.level_reduction_holds p C v O Λ P, (weilChar_surjective_and_map_range_al p C v O Λ P).1, hcok, hdim,
    fun a x hx => ?_, hW ▸ GlobalTheory.T.tate_torus_le_lie_span p C v O Λ P, ?_, fun x => ?_, GlobalTheory.T.eigen_finrank_of_cokernel p C v O Λ P hcok hW, hW⟩
  · change P.alC _ = 0
    rw [P.isEquivariant_alC a x, show P.alC x = 0 from hx, map_zero]
  · rw [hW]
    exact Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact (hiso x).2)
  · rw [horth, ← hW]

theorem hodgeTateKernelAtPoint : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint :=
  fun h => hodgeTateKernelAtPoint_of_dieudonne h.q4

end GlobalTheory.HTKernel
