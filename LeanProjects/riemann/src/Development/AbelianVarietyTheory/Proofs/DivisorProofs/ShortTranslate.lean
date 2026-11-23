import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeTransferRankOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.LevelMoveShort

open GlobalTheory.TraceLattice

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem isShortRule_mv {D : D7} (T : Full D) (hT : LawsFull T) {j : ℕ} (hj : InR D j) (hxi : TwistTrivialOnRational T j)
    {w : WeightFamilies.Wt D j} {n : ℕ} (hn : w.n = n) (hnV : n = D.R.nV)
    {γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l} (hγ : DetOne γ)
    {Λ : GenLat D.host.E n} {N : ℕ} {P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F} {x x' : Fin n → (T.Q.Dw j).La} {f : T.R j}
    (h1 : Λ.Unimod) (h2 : Λ.TrivAt (badN D)) (h3 : Λ.TrivAt (T.dδ j n).l₂.M) (h4 : Λ.LevOK N (T.dδ j n).l₂.M)
    (hP : P ∈ harmL (Dw := T.Q.Dw j) T.Q.c Λ (wtA w)) (hx : IsRightMul γ x' x) (ha : AdmX (l := T.Q.l) true x)
    (ha' : AdmX (l := T.Q.l) true x') (hs : f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n)
    (hf : IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x P f) :
    IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x' P (mv T.toTop j γ f) := by
  subst hn
  have hd : decide (w.n = D.R.nV) = true := decide_eq_true hnV
  have hG : GoodDatum T.toTop j w Λ N P := ⟨h1, h2, h3, h4, hP⟩
  obtain ⟨f', hf'⟩ := exists_isSeries hT.sh hj hG (x := x') (hd ▸ ha')
  have e := mv_series T hT hj hxi (hnV ▸ Nat.le_add_right _ _) hγ hG hx ⟨hd ▸ ha, hs, hf⟩ hf'
  rw [e]
  exact hf'.2.2

end GlobalTheory.LevelMoveShort

theorem GlobalTheory.LevelMoveShort.short_translate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), R.LUnif → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ), RunPin (T := T) R i (κ i).n v p → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → ∀ u : U, ∃ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P (F₀.1 : T.R ((i : ℕ) + 1)) ∧ cuspTo hT.p fw i (f u) = (R.FW i).ρ ((u : G)⁻¹) (cuspTo hT.p fw i F₀) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw hT _ i _ ℓ hℓ hAP v p hR hPg U hU Λ N x₀ P x f h1 h2 h3 h4 ha₀ hP hx u
  obtain ⟨act, hact, hρ⟩ := hAP
  have hnV : (κ i).n = D.R.nV := (fw.kap i (D.eTau.symm 1)).2.2
  have hnV' : (Vc D i).rank = D.R.nV := (GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne.rank_Vc i).1
  have hxi := GlobalTheory.TraceLattice.twistTrivial_of_runPin hT hR
  have hdet : GlobalTheory.TraceLattice.DetOne (ℓ (u : G)) := GlobalTheory.TraceLattice.detOne_of_levelPin hT hℓ hPg (hU u)
  refine ⟨act (u : G) (f u), ?_, ?_⟩
  · rw [hact]
    exact GlobalTheory.LevelMoveShort.isShortRule_mv T hT (inR_succ i) hxi (hnV.trans hnV'.symm) hnV' hdet h1 h2 h3 h4 hP
      (hx u).1 (hx u).2.1 ha₀ (cutR_le T.C _ _ (f u).2).1 (hx u).2.2
  · rw [hρ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
