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

namespace GlobalTheory.DiagThetaRatInv

theorem dot_elim {R : Type} [CommRing R] {κ : Type} [Fintype κ] (x : κ ⊕ κ → R) (v : κ → R) :
    x ⬝ᵥ Sum.elim v (-v) = ∑ i, (x (Sum.inl i) - x (Sum.inr i)) * v i := by
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg, sub_mul,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]
  simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem schr_diag {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (u v : κ → R) (Φ : (κ ⊕ κ → R) → ℂ) (x : κ ⊕ κ → R) :
    GlobalTheory.WeilM.schr ψ (Sum.elim u u, Sum.elim v (-v)) Φ x =
      ψ (∑ i, (x (Sum.inl i) - x (Sum.inr i)) * v i) * Φ (x + Sum.elim u u) := by
  simp only [GlobalTheory.WeilM.schr]
  rw [dot_elim, dot_elim]
  simp

theorem diag_theta_rat_inv : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ]
    (Φ : (κ ⊕ κ → AF F) → ℂ), ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim (γ + w).1 (γ + w).1, Sum.elim (γ + w).2 (-(γ + w).2)) Φ) =
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ) := by
  intro F _ _ ψ hψ κ _ Φ γ hγ w
  obtain ⟨a, b, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff γ).1 hγ
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [← (Equiv.subRight (Sum.elim a a)).tsum_eq]
  congr 1
  funext η
  rw [schr_diag, schr_diag]
  simp only [Equiv.subRight_apply, Prod.fst_add, Prod.snd_add]
  have h1 : (∑ i, (algebraMap F (AF F) ((η - Sum.elim a a) (Sum.inl i)) -
        algebraMap F (AF F) ((η - Sum.elim a a) (Sum.inr i))) * ((fun i => algebraMap F (AF F) (b i)) + w.2) i) =
      algebraMap F (AF F) (∑ i, (η (Sum.inl i) - η (Sum.inr i)) * b i) +
        ∑ i, (algebraMap F (AF F) (η (Sum.inl i)) - algebraMap F (AF F) (η (Sum.inr i))) * w.2 i := by
    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, map_sub, map_mul]
    ring
  have h2 : (fun i => algebraMap F (AF F) ((η - Sum.elim a a) i)) +
        Sum.elim ((fun i => algebraMap F (AF F) (a i)) + w.1) ((fun i => algebraMap F (AF F) (a i)) + w.1) =
      (fun i => algebraMap F (AF F) (η i)) + Sum.elim w.1 w.1 := by
    funext j
    cases j <;> simp <;> abel
  rw [h1, h2, AddChar.map_add_eq_mul, hψ.2.2.1, one_mul]

end GlobalTheory.DiagThetaRatInv
