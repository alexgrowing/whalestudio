import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipVacuumEqMultipleOfTranslateMean
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlipVacB

open GlobalTheory.RouteSeesaw GlobalTheory.SquareDict.AlgSmall GlobalTheory.PairLift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem heis_rd (hψ : IsStdChar D ψ (-1)) (S V : HSp D) (w : WO S V) (g : WO (negSp V) S → ℂ) :
    heisO ψ S V w (rd S V g) = rd S V (heisO ψ (negSp V) S (adjO (negSp V) S w) g) := by
  rw [rd_eq, GlobalTheory.CjNeg.heis_negT' hψ, GlobalTheory.AdjLawPf.adj_heis ψ hψ.1.2.1, ← rd_eq]

theorem heisenbergOperator_externalProductOnHermitianSum (S A B : HSp D) (u : WO S (GlobalTheory.Doubling.hsum A B)) (f : WO S A → ℂ) (g : WO S B → ℂ) :
    heisO ψ S (GlobalTheory.Doubling.hsum A B) u (box2 f g) =
      box2 (heisO ψ S A (topR (A := A) (B := B) u) f) (heisO ψ S B (botR (A := A) (B := B) u) g) := by
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec, GlobalTheory.MixModel.OrthDec.heisO_boxT, GlobalTheory.SeesawSumTarget.boxT_sumDec,
    GlobalTheory.MixModel.OrthDec.resT_apply, GlobalTheory.SeesawSumTarget.pA_sumDec, GlobalTheory.SeesawSumTarget.pB_sumDec]

theorem externalProduct_latticeVacua_adjoint_isLatticeVacuum (hψ : IsStdChar D ψ (-1)) {S A B : HSp D} {Λ : AddSubgroup (WO S (GlobalTheory.Doubling.hsum A B))}
    {ΛA : AddSubgroup (WO S A)} {ΛB : AddSubgroup (WO (negSp B) S)}
    (h : ∀ u ∈ Λ, topR (A := A) (B := B) u ∈ ΛA ∧ adjO (negSp B) S (botR (A := A) (B := B) u) ∈ ΛB)
    {f : WO S A → ℂ} {g : WO (negSp B) S → ℂ} (hf : IsLatVac (heisO ψ S A) ΛA f)
    (hg : IsLatVac (heisO ψ (negSp B) S) ΛB g) :
    IsLatVac (heisO ψ S (GlobalTheory.Doubling.hsum A B)) Λ (box2 f (rd S B g)) := by
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have e1 : topR (A := A) (B := B) (2 • u) = 2 • topR (A := A) (B := B) u := rfl
    have e2 : adjO (negSp B) S (botR (A := A) (B := B) (2 • u)) = 2 • adjO (negSp B) S (botR (A := A) (B := B) u) := by
      have e3 : botR (A := A) (B := B) (2 • u) = botR (A := A) (B := B) u + botR (A := A) (B := B) u := by
        rw [two_nsmul]; rfl
      rw [e3, two_nsmul]
      exact GlobalTheory.AdjLawPf.adj_add (negSp B) S _ _
    rw [heisenbergOperator_externalProductOnHermitianSum, heis_rd hψ, e1, e2, hf.1 _ (h u hu).1, hg.1 _ (h u hu).2]
  · have h1 : IsHalf e (topR (A := A) (B := B) u) := fun a b => hh _ _
    have h2 : IsHalf e (botR (A := A) (B := B) u) := fun a b => hh _ _
    have he' : IsSplitIdem D (cA D e) := GlobalTheory.SplitScalar.isSplitIdem_conj he
    rw [heisenbergOperator_externalProductOnHermitianSum, heis_rd hψ, hf.2 e he _ (h u hu).1 h1,
      hg.2 _ he' _ (h u hu).2 (GlobalTheory.AdjLawPf.adj_half (negSp B) S e _ h2)]

theorem vac_ne_zero {θ : InfFam D} {S T : HSp D} {sS sT LS LT} {f : WO S T → ℂ} (hf : IsVacO ψ θ S T sS sT LS LT f) :
    f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 (0 : WO S T → ℂ) = 1 := hn p hp
  simp [nrm2] at n1

theorem externalProduct_readThroughAdjoint_ne_zero {S A B : HSp D} {f : WO S A → ℂ} {g : WO (negSp B) S → ℂ} (hf : f ≠ 0) (hg : g ≠ 0) :
    box2 f (rd S B g) ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hf
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hg
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec]
  intro h0
  have := congrFun h0 (((GlobalTheory.BiTransfer.sumDec A B).resT S).symm (x, adjO S (negSp B) y))
  simp only [GlobalTheory.MixModel.OrthDec.boxT, AddEquiv.apply_symm_apply, Pi.zero_apply, rd] at this
  erw [GlobalTheory.AdjLawPf.adj_invol] at this
  exact mul_ne_zero hx hy this

theorem vac_eq_smul_vacB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ (fun _ => True) : Set _) = orderingsOnSpWOne G i j →
      ∀ f, IsVacO W.ψ W.θ (spW₁ G i j) (spX G i j) (W.cart (.grid i j)) (frSum AV AV₁).cart
        (G.Λ (.grid i j)) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacB ρ i j := by
  intro D T L sc G μ₀ hL W ρ i j AV AV₁ hV hV₁ Λ hΛ hlat f hf
  obtain ⟨A₁, h₁⟩ := exists_isGridFr W (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩
  have v1 := ρ.vT_is μ₀ i j i.2.le j.2
  have v2 := ρ.vX_is i j i.2 j.2.le
  have c₁ : A₁.cart = W.cart _ := funext fun s => (h₁ s).2
  have cV : AV.cart = W.cart _ := funext fun s => (hV s).2
  have cV₁ : (negFr AV₁).cart = fun s => -W.cart (.grid (i + 1) j) s := funext fun s => by rw [negFr_cart, (hV₁ s).2]
  have w1 : IsVacF W.ψ W.θ A₁ AV (ρ.vT i j) := ⟨v1.2.theta, fun s => by rw [c₁, cV]; exact v1.2.fock s⟩
  have w2 : IsVacF W.ψ W.θ (negFr AV₁) A₁ (ρ.vX i j) := ⟨v2.2.theta, fun s => by rw [c₁, cV₁]; exact v2.2.fock s⟩
  have key := fockVacuum_externalProductOnHermitianSum AV AV₁ W.ψ_std W.θ_is A₁ w1 (rd_vac W.ψ_std W.θ_is A₁ AV₁ w2)
  have e : vacB ρ i j = box2 (ρ.vT i j) (rd (spW₁ G i j) (spV₁ G i j) (ρ.vX i j)) := rfl
  have s0 := (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have hl : IsLatVac (heisO W.ψ (spW₁ G i j) (spX G i j))
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ fun _ => True) (vacB ρ i j) := by
    rw [e]
    refine externalProduct_latticeVacua_adjoint_isLatticeVacuum W.ψ_std (fun u hu => ?_) v1.2.lat v2.2.lat
    have hu' : u ∈ orderingsOnSpWOne G i j := by rw [← hlat]; exact hu
    exact hu'
  obtain ⟨a, ha⟩ := GlobalTheory.LevelSeries.eq_smul_vacuum W.ψ_std W.θ_is (W.cart_is (.grid i j) ⟨i.2.le, j.2.le⟩)
    (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv (frSum AV AV₁)) s0 hΛ hf (f' := vacB ρ i j) key.1 hl
    (fun s => by have := key.2 s; rw [c₁] at this; exact this)
  have hne : vacB ρ i j ≠ 0 := by rw [e]; exact externalProduct_readThroughAdjoint_ne_zero (vac_ne_zero v1) (vac_ne_zero v2)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hne (by rw [ha, zero_smul])
  exact ⟨a⁻¹, inv_ne_zero ha0, by rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

end GlobalTheory.TopFlipVacB

end
