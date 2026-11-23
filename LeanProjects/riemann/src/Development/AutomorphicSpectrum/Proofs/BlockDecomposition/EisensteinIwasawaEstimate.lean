import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr PositivityTheory.Rg.SwEis
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SwEisIwa

theorem iwa_of_rank (hC : Chart) (D : D7) (χ : (AE D)ˣ →* Circle) (V : HSp D) :
    Iwa ((adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin V.rank))) ((adCM D.sp.cm.sig χ).uK (-1) (Fin V.rank)) := by
  obtain ⟨a, ha⟩ := GlobalTheory.Doubling.exists_isMaj V
  obtain ⟨Φ, p, -, hQ, hK, -, -⟩ := hC D χ V a ha
  intro g
  obtain ⟨q, k, hk, hqk⟩ := (GlobalTheory.Eis.isIwasawa_Khat (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha)).1
    (Φ.symm g * (p : GA D (dblSp V))⁻¹)
  refine ⟨Φ ((q : GA D (dblSp V)) * p), (hQ _).1 (Subgroup.mul_mem _ q.2 p.2),
    Φ ((p : GA D (dblSp V))⁻¹ * k * p), (hK k).1 hk, ?_⟩
  have h1 : Φ.symm g = (q : GA D (dblSp V)) * k * p := by
    rw [← hqk, inv_mul_cancel_right]
  have h2 : (q : GA D (dblSp V)) * p * ((p : GA D (dblSp V))⁻¹ * k * p) = (q : GA D (dblSp V)) * k * p := by
    group
  rw [← map_mul, h2, ← h1]
  exact (Φ.apply_symm_apply g).symm

theorem eIwa : EIwa := fun hC D χ n =>
  iwa_of_rank hC D χ (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n)

end GlobalTheory.CompanionTheory.SwEisIwa

end
