import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanDesc

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def iotaR (R : RealDat3 D A3 Ks) (i : Fin D.R.m) :
    (Fin (R.nW i) → D.what₂.LL) →ₛₗ[sg0 D A3.A] Formalism.IndefR.Mult.MMap (R.MW i (sg0 D A3.A)) :=
  (R.HW i (sg0 D A3.A)).e.comp ((R.FW i).j (sg0 D A3.A))

theorem iotaR_apply (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (v : Fin (R.nW i) → D.what₂.LL) :
    iotaR R i v = (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) v) := rfl

variable {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

theorem readW_mem_goodW (Y : Read (A3 := A3) R F X0) (i : Fin D.R.m) (y : D.what₂.Mj ((i : ℕ) + 1)) :
    GlobalTheory.EigRows.readW Y i y ∈ GlobalTheory.EigRows.goodW R F i := by
  obtain ⟨a, ha, e⟩ := Submodule.mem_map.1 (Y.IL.jMj i y).2
  have h' : a = GlobalTheory.EigRows.readW Y i y :=
    (PiTensorProduct.lift : Formalism.IndefR.Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).injective
      (e.trans (GlobalTheory.EigRows.lift_readW Y i y).symm)
  exact h' ▸ ha

theorem goodW_le_parts (Y : Read (A3 := A3) R F X0) (hI : Rows.IsotInternal D.what₂) (hG : GlobalTheory.EigRows.OccGood D)
    (i : Fin D.R.m) (n : ℕ) (hn : (i : ℕ) + 1 = n) :
    GlobalTheory.EigRows.goodW R F i ≤ ⨆ σ ∈ {σ | D.what₂.isot n σ ≠ ⊥ ∧ D.nd.goodRow σ},
      (D.what₂.isot ((i : ℕ) + 1) σ).map (GlobalTheory.EigRows.readW Y i) := by
  subst hn
  intro z hz
  obtain ⟨y, rfl⟩ := GlobalTheory.EigRows.exists_readW Y i hz
  have hy : y ∈ ⨆ σ, D.what₂.isot ((i : ℕ) + 1) σ := by
    rw [(hI _ (Nat.le_add_left 1 i) i.2).submodule_iSup_eq_top]; trivial
  have key : (⨆ σ, D.what₂.isot ((i : ℕ) + 1) σ) ≤ (⨆ σ ∈ {σ | D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ ∧ D.nd.goodRow σ},
      (D.what₂.isot ((i : ℕ) + 1) σ).map (GlobalTheory.EigRows.readW Y i)).comap (GlobalTheory.EigRows.readW Y i) := by
    refine iSup_le fun σ => ?_
    by_cases h0 : D.what₂.isot ((i : ℕ) + 1) σ = ⊥
    · rw [h0]; exact bot_le
    · intro u hu
      exact Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem
        (show σ ∈ {σ | D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ ∧ D.nd.goodRow σ} from ⟨h0, hG _ (Nat.le_add_left 1 i) i.2 σ h0⟩)
        (Submodule.mem_map_of_mem hu)))
  exact key hy

end Real

end GlobalTheory.EigSpanDesc
