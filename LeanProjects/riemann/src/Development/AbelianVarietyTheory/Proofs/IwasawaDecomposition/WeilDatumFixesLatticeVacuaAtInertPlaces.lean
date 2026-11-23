import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertAll

theorem nonSplitAt_of_forall (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε)
    (hns : ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0) : GlobalTheory.WeilParts.NonSplitAt D v ε := by
  refine ⟨hε, fun ⟨e, he, heq⟩ => ?_⟩
  have k := hns e he
  have e0 : e = 0 := by
    rw [← heq, mul_add, he.1, he.2.1, add_zero] at k
    exact k
  rw [e0, map_zero, zero_add] at heq
  obtain ⟨α, rfl, h1, -⟩ := hε
  have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  have : pairA D.host.F 0 α = 0 := hinj (by rw [map_zero]; exact heq.symm)
  have : α = 0 := congrArg Prod.snd this
  rw [this, map_zero] at h1
  exact zero_ne_one h1

theorem unramAt_of_unrAtV (D : D7) (ε : AF D.host.F) (χ : (AE D)ˣ →* Circle) (hχ : Formalism.IndefR.WeilFull.UnrAtV ε χ) : GlobalTheory.WeilParts.UnramAt ε χ :=
  fun x hx i1 i2 => hχ x (by linear_combination (-1 : AE D) * hx) i1 i2

theorem inertAllO_of_eta (D : D7) (hη : ∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) : Formalism.IndefR.WeilFull.InertAllO D := by
  intro ψ S T χS χT om H _ _ ΛS ΛT hS hT βS βT hβS hβT v ε hε _ hns uS uT g h sg sh hg hh f hf hvac
  have hv : GlobalTheory.WeilParts.NonSplitAt D v ε := nonSplitAt_of_forall D v ε hε hns
  have hst : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) ↔
      actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) :=
    fun u => GlobalTheory.LatStab.mem_latO_iff_actO_mem D S T ΛS ΛT βS βT hS.1 hT.1 hβS hβT g h hg hh _ u
  have hfix : ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v),
      heisO ψ S T u f = f := by
    intro u hu
    obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hv
    have h1 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε hu]
    have h2 := hvac.1 (a • u) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu)
    rwa [h1] at h2
  exact GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ H.std S T ΛS ΛT hS hT χS χT om hη H v ε hv (unramAt_of_unrAtV D ε χS uS) (unramAt_of_unrAtV D ε χT uT) g h sg sh hst f hf hfix

theorem inertAllO : ∀ D : D7, Formalism.IndefR.WeilFull.InertAllO D :=
  fun D => inertAllO_of_eta D (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D)

end GlobalTheory.InertAll
