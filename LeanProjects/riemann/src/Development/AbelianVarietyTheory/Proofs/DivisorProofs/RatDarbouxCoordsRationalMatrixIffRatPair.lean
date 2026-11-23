import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainTheta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.RatDarbouxPointsD

set_option maxHeartbeats 1000000 in

theorem ratL_iff_ratPair : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ := by
  intro D S T κ _ e hrat w
  haveI : FiniteDimensional D.host.F D.host.E :=
    Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  · intro hp

    let bA := Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)
    haveI : Module.Free (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := Module.Free.of_basis bA
    haveI : Module.Finite (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := Module.Finite.of_basis bA
    have hAE : Module.finrank (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) =
        Module.finrank D.host.F D.host.E := by
      rw [Module.finrank_eq_card_basis bA, Fintype.card_fin]
    have hκ : 2 * Fintype.card κ = T.rank * S.rank * Module.finrank D.host.F D.host.E := by
      have h := e.finrank_eq
      have ha : Module.finrank (AF D.host.F)
          (Matrix (Fin T.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) =
          T.rank * S.rank * Module.finrank D.host.F D.host.E := by
        show Module.finrank (AF D.host.F) (Fin T.rank → Fin S.rank → AF D.host.F ⊗[D.host.F] D.host.E) = _
        simp [Module.finrank_pi_fintype, hAE, mul_assoc]
      have hb : Module.finrank (AF D.host.F) ((κ → AF D.host.F) × (κ → AF D.host.F)) = 2 * Fintype.card κ := by
        rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
        ring
      rw [← hb, ← h, ha]

    let J1 : (κ → D.host.F) →ₗ[D.host.F] (κ → AF D.host.F) :=
      LinearMap.compLeft (Algebra.linearMap D.host.F (AF D.host.F)) κ
    let J : ((κ → D.host.F) × (κ → D.host.F)) →ₗ[D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F) :=
      J1.prodMap J1
    let I : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[D.host.F]
        Matrix (Fin T.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E) :=
      (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toLinearMap.mapMatrix
    let L := (e.toLinearMap.restrictScalars D.host.F).comp I
    have hJinj : Function.Injective J := by
      rintro ⟨y, z⟩ ⟨y', z'⟩ h
      have hi := AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F
      simp only [J, J1, LinearMap.prodMap_apply, Prod.mk.injEq] at h
      refine Prod.ext (funext fun i => hi ?_) (funext fun i => hi ?_)
      · exact congrFun h.1 i
      · exact congrFun h.2 i
    have hLinj : Function.Injective L := by
      have hr : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) := RingHom.injective _
      intro x x' h
      have := e.injective h
      exact Matrix.ext fun i j => hr (congrFun (congrFun this i) j)
    have hle : LinearMap.range L ≤ LinearMap.range J := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, z, h⟩ := hrat x
      exact ⟨(y, z), by rw [show L x = e (incM D.host.F x) from rfl, h]; rfl⟩
    have heq : LinearMap.range L = LinearMap.range J := by
      refine Submodule.eq_of_le_of_finrank_eq hle ?_
      rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hJinj]
      have hm : Module.finrank D.host.F (Matrix (Fin T.rank) (Fin S.rank) D.host.E) =
          T.rank * S.rank * Module.finrank D.host.F D.host.E := by
        show Module.finrank D.host.F (Fin T.rank → Fin S.rank → D.host.E) = _
        simp [Module.finrank_pi_fintype, mul_assoc]
      have hp2 : Module.finrank D.host.F ((κ → D.host.F) × (κ → D.host.F)) = 2 * Fintype.card κ := by
        rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
        ring
      rw [hm, hp2, hκ]
    obtain ⟨y, z, hw⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
    have hm : J (y, z) ∈ LinearMap.range L := heq ▸ LinearMap.mem_range_self J (y, z)
    obtain ⟨x, hx⟩ := hm
    refine ⟨x, ?_⟩
    have hx' : e (incM D.host.F x) = e w := by rw [hw]; exact hx
    exact e.injective hx'

end GlobalTheory.RatDarbouxPointsD

end
