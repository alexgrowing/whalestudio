import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.SchurPairingInvariant

theorem left_inv_of_mem_Minf {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {n : ℕ}
    {P : principalLevelFrame.RowPsi V n} {x : MMap M} (hx : x ∈ principalLevelFrame.Minf θ P M) (v : M.Vec) :
    ∀ γ ∈ GQ V, ∀ g, x v (γ * g) = x v g := by
  unfold principalLevelFrame.Minf at hx
  refine Submodule.iSup_induction _ (motive := fun z : MMap M => ∀ γ ∈ GQ V, ∀ g, z v (γ * g) = z v g) hx ?_ ?_ ?_
  · intro N z hz
    exact (PeterssonHilbertSpace.mult_cont_left M θ _ _ hz v).2
  · intro γ _ g
    rfl
  · intro z w hz hw γ hγ g
    simp only [MultilinearMap.add_apply, Pi.add_apply, hz γ hγ g, hw γ hγ g]

theorem ipM_congr_of_iff {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} {T T' U U' : MMap M} (h : ∀ c, IsMultIP M μ 𝓕 T T' c ↔ IsMultIP M μ 𝓕 U U' c) :
    ipM M μ 𝓕 T T' = ipM M μ 𝓕 U U' := by
  have e : IsMultIP M μ 𝓕 T T' = IsMultIP M μ 𝓕 U U' := funext fun c => propext (h c)
  unfold ipM
  rw [e]

theorem ipM_actM : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (n : ℕ) (P : principalLevelFrame.RowPsi V n) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurAll D → V.SigOK → IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (h : Formalism.AUTREP.GAf D.host.E n), ∀ x ∈ principalLevelFrame.Minf θ P M, ∀ y ∈ principalLevelFrame.Minf θ P M, ipM M μ 𝓕 (principalLevelFrame.actM P M h x) (principalLevelFrame.actM P M h y) = ipM M μ 𝓕 x y := by
  intro D V S θ M n P μ 𝓕 _ _ _ hμ h𝓕 h x hx y hy
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  apply ipM_congr_of_iff
  intro c
  have key : ∀ v v' : M.Vec, _ := fun v v' =>
    GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun g => star (x v g) * y v' g) (P.ψ h) h𝓕
      (fun γ hγ g => by simp only [left_inv_of_mem_Minf hx v γ hγ g, left_inv_of_mem_Minf hy v' γ hγ g])
  unfold IsMultIP
  simp only [principalLevelFrame.actM_apply]
  constructor
  · intro H v v'
    obtain ⟨k1, k2⟩ := key v v'
    exact ⟨k1.2 (H v v').1, k2 ▸ (H v v').2⟩
  · intro H v v'
    obtain ⟨k1, k2⟩ := key v v'
    exact ⟨k1.1 (H v v').1, k2.trans (H v v').2⟩

end GlobalTheory.SchurPairingInvariant
