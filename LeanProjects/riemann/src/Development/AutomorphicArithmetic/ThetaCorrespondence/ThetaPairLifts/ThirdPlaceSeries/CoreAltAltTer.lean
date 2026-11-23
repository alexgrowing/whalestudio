import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InfinityTypeOfLift
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.LiftInfRef
open Matrix Formalism.L2.NG GlobalTheory.AlgWtHW NumberField
section Conj
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Conj
end GlobalTheory.LiftInfRef
namespace GlobalTheory.LiftInfRef
open Matrix Formalism.L2.NG GlobalTheory.AlgWtHW NumberField
section Conj2
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Conj2
end GlobalTheory.LiftInfRef
namespace GlobalTheory.LiftInfRef
open GlobalTheory.LiftRef
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem core_data_of_point (D : D7) (cf : CharFrame D) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt D) (chr : CharSide D cf) (M : MtFam D)
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (hIn : MtInput D M tup Q) (k : ℕ) (h1 : 1 ≤ k + 1) (h2 : k + 1 ≤ D.R.m)
    (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 (k + 1) h1 h2).wt.W))
    (hS : NG.IsIrrRep (M D.what₂.mu0 (k + 1) h1 h2).wt.ρ S) (μ : D.naut.CG 1)
    (hμ : (chr.e1 μ).1 = cf.mu0 ⟨k, by omega⟩) (τ : D.what₂.Tau) :
    D.nbc.infW (k + 1) (D.nbc.wtAU (k + 1) (A.cls (k + 1) h1 h2 (autOf (M D.what₂.mu0 (k + 1) h1 h2) S hS))) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) =
        (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (· - 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) ∧
      D.nbc.infW (k + 1) (D.nbc.wtAU (k + 1) (A.cls (k + 1) h1 h2 (autOf (M D.what₂.mu0 (k + 1) h1 h2) S hS))) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) =
        (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (fun y => -y + 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) := by
  set π := autOf (M D.what₂.mu0 (k + 1) h1 h2) S hS with hπ
  obtain ⟨b, hd, -, -⟩ := GlobalTheory.algWt_contragredient D.host.E D.R.nV π.toAlgWt
  have hw := A.wt (k + 1) h1 h2 π b hd
  obtain ⟨lam, hlam⟩ := (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone D.host.E D.R.nV b (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).1.exists
  obtain ⟨lam', hlam'⟩ := (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone D.host.E D.R.nV b (ComplexEmbedding.conjugate (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ))).1.exists
  have hbar : GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ = ComplexEmbedding.conjugate (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) := by
    ext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar, ComplexEmbedding.conjugate_coe_eq]
  have hpar : NG.infOf lam = NG.paramV D.R (D.hc τ) ⟨k, by omega⟩ (1 / 2) := hIn.wt D.what₂.mu0 ⟨k, by omega⟩ τ b lam hd hlam
  have hinf1 := A.infW (k + 1) h1 h2 b _ lam hlam
  have hinf2 := A.infW (k + 1) h1 h2 b _ lam' hlam'
  have hconj := infOf_conj hlam hlam'
  have he : (chr.e1 (D.naut.tw μ D.naut.etaTinv)).1 = cf.mu0 ⟨k, by omega⟩ * cf.eta⁻¹ := by
    rw [chr.tw, hμ, chr.etaTinv]
  have hI : (chr.e1 (D.naut.tw μ D.naut.etaTinv)).1.HasInfQ (embPsi D.host)
      (fun g => -eExp D ⟨k, by omega⟩ g - 1 / 2) := by
    rw [he]
    have h1' := (cf.isMu0 ⟨k, by omega⟩).inf
    have h2' : (cf.eta⁻¹).HasInfQ (embPsi D.host) (-(fun _ => 1 / 2)) :=
      GlobalTheory.BlockCharInf.hasInfQ_inv' ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩
    convert GlobalTheory.BlockCharInf.hasInfQ_mul' h1' h2' using 1
    funext g
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  obtain ⟨hg1, hg2⟩ := chr.infG _ _ hI (D.eTau τ)
  have hval : eExp D ⟨k, by omega⟩ (D.eTau τ) = (D.hc τ).e ⟨k, by omega⟩ := by simp [eExp]
  have hG1 : D.naut.infG (D.naut.tw μ D.naut.etaTinv) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {(-((D.hc τ).e ⟨k, by omega⟩ : ℂ) - 1 / 2)} := by
    rw [show GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ = embPsi D.host (D.eTau τ) from rfl, hg1, hval]; push_cast; ring_nf
  have hG2 : D.naut.infG (D.naut.tw μ D.naut.etaTinv) (ComplexEmbedding.conjugate (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)) =
      {(((D.hc τ).e ⟨k, by omega⟩ : ℂ) + 1 / 2)} := by
    rw [← hbar, show GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ = (starRingEnd ℂ).comp (embPsi D.host (D.eTau τ)) from rfl, hg2, hval]; push_cast; ring_nf
  rw [hw, hinf1, hbar, hinf2, hconj, hpar]
  constructor
  · unfold isoInf
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hG1, Multiset.map_singleton, bindCast, List.map_map, Function.comp_def, sum_singletons]
    unfold NG.paramV GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma
    rw [Multiset.map_add, Multiset.map_map, Multiset.map_map, ← Multiset.map_coe, Multiset.coe_range]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]
    · refine Multiset.map_congr rfl fun c _ => ?_
      push_cast; ring
  · unfold isoInf
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hG2, Multiset.map_singleton, bindCast, List.map_map, Function.comp_def, sum_singletons]
    unfold NG.paramV GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma
    rw [Multiset.map_add, Multiset.map_add, Multiset.map_add, Multiset.map_map, Multiset.map_map, Multiset.map_map,
      Multiset.map_map, Multiset.map_map, ← Multiset.map_coe, Multiset.coe_range]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]; ring
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]; ring
    · have hf := range_rev D.R.t (fun c : ℕ => ((D.hc τ).e ⟨k, by omega⟩ : ℂ) + 1 / 2 - ((D.R.t : ℂ) - 1) / 2 + c)
      refine (Multiset.map_congr rfl fun c _ => ?_).trans (hf.symm.trans (Multiset.map_congr rfl fun c hc => ?_))
      · simp only [Function.comp_apply]; push_cast; ring
      · have hc' := Multiset.mem_range.1 hc
        rw [Nat.cast_sub (show c ≤ D.R.t - 1 by omega), Nat.cast_sub (show 1 ≤ D.R.t by omega)]
        push_cast; ring
end GlobalTheory.LiftInfRef
namespace GlobalTheory.LiftInfRef
end GlobalTheory.LiftInfRef
end
end
