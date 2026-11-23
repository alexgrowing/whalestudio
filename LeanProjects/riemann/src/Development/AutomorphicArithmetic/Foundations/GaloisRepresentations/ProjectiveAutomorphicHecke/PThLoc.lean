import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.InvTMemSim

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pThLoc_of :
    UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.OfUBij → UpperTheory.Gal.CertificateRingHomMap.ThLoc := by
  intro _ hB E _ _ _ n
  obtain ⟨-, hsurj⟩ := hB E n
  refine ⟨fun w hw y => ?_, fun hn x w z hz => ?_⟩
  · have hs : sim (th (loc hw y)) = 1 := by
      rw [sim_th, sim_loc, inv_one]
    obtain ⟨u, hu⟩ := hsurj _ hs
    have hmem : u.1 ∈ locU n w := by
      refine Subgroup.mem_inf.2 ⟨u.2, Subgroup.mem_iInf.2 fun u' => Subgroup.mem_iInf.2 fun h => MonoidHom.mem_ker.2 ?_⟩
      have h1 : comp u' (ofU u) = 1 := by
        rw [hu, comp_th, comp_loc_of_apart hw h, map_one]
      exact h1
    have hw' : cLoc w u.1 = invT n _ y := by
      have h1 : comp w (ofU u) = invT n _ y := by
        rw [hu, comp_th, comp_loc]
      exact h1
    have hu' : u = locF hw (invT n _ y) := by
      have h2 : (⟨u.1, hmem⟩ : locU n w) = (locE hw).symm (invT n _ y) := by
        apply (locE hw).injective
        rw [locE_apply, (locE hw).apply_symm_apply]
        exact hw'
      exact Subtype.ext (congrArg (fun t : locU n w => t.1) h2)
    show _ = ofU (locF hw _)
    rw [← hu, hu']
  · refine guf_ext (by rw [sim_th, map_inv]) fun u => ?_
    have hsym : (comp u z).valᵀ = (comp u z).val := by
      by_cases h : SameK x (cj u) w
      · rw [((hz u).1 h), transpose_smul, transpose_one]
      · rw [((hz u).2 h), Units.val_one, transpose_one]
    rw [comp_th, map_inv]
    apply Units.ext
    rw [invT_val, Matrix.coe_units_inv, Matrix.transpose_nonsing_inv, hsym]
