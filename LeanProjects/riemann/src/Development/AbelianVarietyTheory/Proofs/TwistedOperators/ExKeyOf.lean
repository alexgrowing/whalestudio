import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.Mem GlobalTheory.Mem.Top
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowEx

set_option maxHeartbeats 1600000 in

theorem exKey_of (h1 : GridEx) (h2 : IsEx) (h3 : NFAll) (cG : CarryG) (cW : CarryW) (cS : CarryS)
    (t1 : TrEasy) (t2 : TrPhase) (t3 : TrJet) (t4 : TrBot) : ExKey := by
  classical
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  obtain ⟨a3, h3⟩ := h3
  refine ⟨max a1 (max a2 a3), fun ε CF hC => ?_⟩
  obtain ⟨x1, h1⟩ := h1 ε CF (le_of_max_le_left hC)
  obtain ⟨x2, h2⟩ := h2 ε CF (le_of_max_le_left (le_of_max_le_right hC))
  obtain ⟨x3, h3⟩ := h3 ε CF (le_of_max_le_right (le_of_max_le_right hC))
  refine ⟨max x1 (max x2 x3), fun s he hx P f κ => ?_⟩
  have hx1 := le_of_max_le_left hx
  have hx2 := le_of_max_le_left (le_of_max_le_right hx)
  have hx3 := le_of_max_le_right (le_of_max_le_right hx)
  by_cases H : ∃ (X : Stages) (f' : Fr X.B.toPre) (_ : X.B.toPre = P) (_ : HEq f' f) (large₂ : SizeData₂ X.toD7) (_ : large₂.sc = s)
      (Γ : Type) (_ : Group Γ) (_ : Fintype Γ) (Pl0 T : Type)
      (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks) (_ : Algebra Ks X.toD7.what₂.LL)
      (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A), HidaSetting large₂ R F ∧ R.C = Fr.at X f' ∧ TwistPlacesOffPrimeQZero R.toLevCh ∧ HEq (keyOf R.toLevCh) κ
  swap
  · exact ⟨∅, by simp, fun X f' a b large₂ c Γ _ _ Pl0 T A Ks _ _ _ R F d e g i _ =>
      absurd ⟨X, f', a, b, large₂, c, Γ, _, _, Pl0, T, A, Ks, _, _, _, R, F, d, e, g, i⟩ H⟩
  obtain ⟨X0, f0, a0, b0, Lg0, rfl, Γ0, _, _, Pl00, T0, A0, Ks0, _, _, _, R0, F0, d0, e0, g0, i0⟩ := H
  obtain ⟨G0, W0, hW0, ⟨S0⟩⟩ := h1 _ Lg0 he hx1 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 g0
  obtain ⟨M, ρ, ξ, cv, rm, S, rp, n, e, c, hS, hIs⟩ := h2 _ Lg0 he hx2 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 G0 W0 hW0 S0
  obtain ⟨N, hN, hAll⟩ := h3 _ Lg0 he hx3 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 _ hIs rfl
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℚ N)) ℚ N) := ⟨Module.finBasis ℚ N⟩
  refine ⟨Finset.univ.image fun i => ((b i : N) : ℂ), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic _)
  intro X f' a b' large₂ hs Γ _ _ Pl0 T A Ks _ _ _ R F d e' g i hz
  have hk : HEq (keyOf R.toLevCh) (keyOf R0.toLevCh) := i.trans i0.symm
  have hpre : X.B.toPre = X0.B.toPre := a.trans a0.symm
  have key : ∀ (P P' : Pre) (_ : P = P') (k : Key P) (k' : Key P'), HEq k k' → ∀ x ∈ k, ∃ y ∈ k', HEq x.1 y.1 ∧ HEq x.2 y.2 := by
    rintro P _ rfl k k' h x hx
    obtain rfl := eq_of_heq h
    exact ⟨x, hx, HEq.rfl, HEq.rfl⟩
  have hι : ∀ t : T, ∃ t0 : T0, HEq (R.xiH t) (R0.xiH t0) ∧ HEq (R.Q t) (R0.Q t0) := fun t => by
    obtain ⟨_, ⟨t0, rfl⟩, h⟩ := key _ _ hpre _ _ hk _ ⟨t, rfl⟩
    exact ⟨t0, h⟩
  choose ι hι using hι
  have one : ∀ (P P' : Pre) (_ : P = P'), HEq (1 : HChar P.host.E) (1 : HChar P'.host.E) := by rintro P _ rfl; rfl
  have hb : ι A.μ0 = A0.μ0 := d0.core.lev.xi_inj (by
    rw [d0.core.lev.xi_base]
    have := (hι A.μ0).1
    rw [d.core.lev.xi_base] at this
    exact eq_of_heq (this.symm.trans (one _ _ hpre)))
  have hL : LAgree R0.toLevCh R.toLevCh A0.μ0 A.μ0 ι :=
    ⟨hpre, d0.core.lev, d.core.lev, ⟨f0, f', b'.trans b0.symm, e0, e'⟩, hb, fun t => (hι t).1, fun t => (hι t).2, d0.betaX, d.betaX⟩
  obtain ⟨G, hG⟩ := cG _ _ _ _ _ _ _ _ _ hL _ G0
  obtain ⟨W, hW, hWA⟩ := cW _ _ _ _ _ Γ Pl0 A Ks R _ ι hL d.core.chain d.core.models _ G0 G hG W0
  obtain ⟨S', hS'⟩ := cS _ _ _ _ _ _ _ _ _ hL _ G0 G hG W0 W hWA S.toGridChoice
  have hA : Agree S.toGridChoice S' A0.μ0 A.μ0 ι := ⟨hL, hG, hWA, hS'⟩
  have h2' := h2 _ large₂ (hs ▸ he) (hs ▸ hx2) Γ Pl0 T A Ks R F d
  rw [hs] at h2'
  obtain ⟨M', ρ', ξ', cv', rm', S2, rp', n', e2, c', hS2, hIs'⟩ := h2' G W hW S'
  refine ⟨_, hIs', rfl, ?_⟩
  obtain ⟨u1, u2, u3⟩ := t1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N (algebraMap N ℂ)
  have hAll' : AllIn (algebraMap N ℂ) S' A.μ0 := ⟨u1 hAll.chars, u2 hAll.root, t2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.phase,
    t3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.jet, u3 hAll.ratios, t4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.bot⟩
  subst hS2
  refine hAll'.numbersIn.mono ?_
  rintro _ ⟨y, rfl⟩
  rw [← b.sum_repr y, map_sum]
  refine X.toD7.what₂.embLL.fieldRange.sum_mem fun i _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast]
  exact X.toD7.what₂.embLL.fieldRange.mul_mem (SubfieldClass.ratCast_mem _ _) (hz _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))

end GlobalTheory.RowEx
