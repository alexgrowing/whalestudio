import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.DualCusp

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

theorem isSupercuspidal_contra
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : Representation ℂ G V} (hπ : IsAdmissible π) (hs : IsSupercuspidal π) :
    IsSupercuspidal (contra π) := by
  refine ⟨isSmooth_contra π, fun l Λ hΛ => ?_⟩
  obtain ⟨u, hu⟩ := (GlobalTheory.ContraRefl.evMap_bijective hG hπ).2 ⟨Λ, hΛ⟩
  have hev : ∀ m : smoothPart π.dual, Λ m = (m : Module.Dual ℂ V) u := fun m =>
    (LinearMap.congr_fun (congrArg Subtype.val hu) m).symm
  obtain ⟨C, hC, hsupp⟩ := hs.2 u l l.2
  refine ⟨C⁻¹, hC.inv, fun g hg => ?_⟩
  rw [hev, contra_apply] at hg
  obtain ⟨z, hz, c, hc, e⟩ := hsupp g⁻¹ hg
  refine ⟨z⁻¹, inv_mem hz, c⁻¹, Set.inv_mem_inv.2 hc, ?_⟩
  have h1 : g = (z * c)⁻¹ := by rw [← e, inv_inv]
  rw [h1, mul_inv_rev]
  exact (Subgroup.mem_center_iff.1 (inv_mem hz) c⁻¹)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dualCl_isCusp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k) (hx : x.IsCusp) :
    (dualCl x).IsCusp ∧ (dualCl x).1 = x.1 := by
  have hadm : IsAdmissible x.rep := hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k x.1
  have hirr : (contra x.rep).IsIrreducible := GlobalTheory.ContraRefl.contra_isIrreducible hG hadm x.2.rep.irr
  have hd : dualCl x = IrrGL.of (contra x.rep) (isSmooth_smoothRep _) hirr := dif_pos hirr
  rw [hd]
  refine ⟨IrrGL.isCusp_of.2 ⟨hx.1, ?_⟩, rfl⟩
  exact GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal k x.1 _ _
    (isSupercuspidal_contra hG hadm (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k x.1 _ _ hx.2))

end GlobalTheory.CompanionTheory.DualCusp

end
