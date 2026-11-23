import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeakStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsLiftsRationalSelfAdjointLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftTransferHeckePolySplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftDictionary

set_option maxHeartbeats 4000000

variable {D : D7} {G : Type} [Group G] [Fintype G] {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

section Zero

variable {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} (R : RealDat D A Ks)

theorem hk_zero (V : HSp D) (P : Pl D.host.E) : hk V P 0 = 0 := Finsupp.sum_zero_index

theorem postOn_zero (V : HSp D) {S} (M : DSModel V S) (T : MMap M) : postOn M 0 T = 0 := by
  ext v
  simp [postOn]

theorem hkF_zero (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (F : Bridge.Gf V → W) : hkF V P 0 F = 0 := by
  funext g
  exact Finsupp.sum_zero_index

theorem ops_zero (hM : R.IsModels) (j : Fin D.R.m) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H) (hh : IsOpsV R j t h) (y : (R.HV j t).H) : h P 0 y = 0 := by
  refine (hM.HV j t).1 ?_
  rw [hh P hP 0 y, map_zero]
  exact hkF_zero _ _ _

theorem match_zero (hM : R.IsModels) (j : Fin D.R.m) (t : T) (P : Pl D.host.E) : MatchW R j t P 0 0 := by
  intro y y' hy
  have h0 : y' = 0 := by
    refine (hM.HV j t).1 ?_
    rw [hy, map_zero]
    exact hkF_zero _ _ _
  have e1 : (R.thG j t) y' = 0 := by rw [h0]; exact (R.thG j t).map_zero
  have e2 : (R.HW j (sg0 D A)).e ((R.thG j t) y') = 0 := by rw [e1]; exact (R.HW j (sg0 D A)).e.map_zero
  refine e2.trans ?_
  rw [hk_zero]
  exact (postOn_zero _ _ _).symm

theorem op_zero (hM : R.IsModels) (j : Fin D.R.m) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (o : Module.End D.what₂.LL (A.MtCSD j t).Forms) (ho : o = 0)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H) (hh : IsOpsV R j t h) (x : (A.MtCSD j t).Forms) :
    R.jV j t (o x) = h P 0 (R.jV j t x) := by
  rw [ops_zero R hM j t P hP h hh, ho, LinearMap.zero_apply]
  exact (R.jV j t).map_zero

end Zero

section Cases

variable {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} (R : RealDat D A Ks)

theorem split_good (F : Face D A) (core : Core R F) (t : T) (P : A.ok t) : Good R t (R.pl P) :=
  ((GlobalTheory.GoodPrimes.good_primes R F core.lev).2.2.2 core.fam t P P.2).1

theorem split_low (F : Face D A) (core : Core R F) (hS : SchurAll R) (j : Fin D.R.m) (t : T) (P : A.ok t) (k : ℕ)
    (hk : k ≤ (Vc D j).rank) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R t pl ∧
      (∀ h, IsOpsV R j t h → ∀ x, R.jV j t (A.heckeL j t (P, k) x) = h pl cV (R.jV j t x)) ∧ MatchW R j t pl cV cW := by
  obtain ⟨z, hz, -⟩ := GlobalTheory.T.thetaLift_transfer_heckePoly_splitPrime R F core hS j t P
  exact ⟨R.pl P, Finsupp.single (splitLab (Vc D j).rank k) 1, splitC (Wc D j).rank (z k), split_good R F core t P,
    fun h hh x => (GlobalTheory.SplitHeckeLabel.split_ops R F core.lev core.fam core.models).2 j t h hh P k hk x, hz k hk⟩

theorem split_high (F : Face D A) (core : Core R F) (j : Fin D.R.m) (t : T) (P : A.ok t) (k : ℕ)
    (hk : ¬ k ≤ (Vc D j).rank) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R t pl ∧
      (∀ h, IsOpsV R j t h → ∀ x, R.jV j t (A.heckeL j t (P, k) x) = h pl cV (R.jV j t x)) ∧ MatchW R j t pl cV cW := by
  have h0 : A.heckeL j t (P, k) = 0 := (core.fam.degL j t P).2 k (not_le.1 hk)
  have hg := split_good R F core t P
  refine ⟨R.pl P, 0, 0, hg, fun h hh x => ?_, match_zero R core.models j t _⟩
  exact op_zero R core.models j t (R.pl P) hg (A.heckeL j t (P, k)) h0 h hh x

end Cases

section Inert

variable {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} (R : RealDat3 D A3 Ks) (F : Face3 D A3)

theorem inert_valid (hH : HoweUnram) (hI : GlobalTheory.Chain.LiftInteg D) (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt)
    (hS : SchurAll R.toRealDat) (j : Fin D.R.m) (t : T) (Q : A3.okI t) (s : List ℕ)
    (hs : Formalism.L2.Col.InertTypeOk (Vc D j).rank s) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R.toRealDat t pl ∧
      (∀ h, IsOpsV R.toRealDat j t h → ∀ x, R.jV j t (A3.heckeLI j t (Q, s) x) = h pl cV (R.jV j t x)) ∧
        MatchW R.toRealDat j t pl cV cW := by
  obtain ⟨hCore, -, hGoodI, -, -, -, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := hCore hEx
  obtain ⟨hg, hconj⟩ := hGoodI t Q Q.2
  have two := GlobalTheory.T.twoSidedHeckePartner_inertPrime hH R.toRealDat F.lv2 hI core hS t (R.plI Q) hg hconj (GlobalTheory.T.hyperspecialFixesAllChainVacua_at_inert_prime R F hC t _ hg hconj)
  obtain ⟨cW, hW⟩ := (two.2 j).1 (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s) 1)
  refine ⟨R.plI Q, Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s) 1, cW, hg, fun h hh x => ?_, hW⟩
  have hty : ∀ i : A3.okI t × List ℕ, Formalism.L2.Col.InertTypeOk (Vc D j).rank i.2 →
      Good R.toRealDat t (R.plI i.1) ∧ conjPl (R.plI i.1) = R.plI i.1 ∧
        (GlobalTheory.Hk3.labIn (Vc D j).rank i.2).Pairwise (fun a b => b ≤ a) := by
    intro i hi
    obtain ⟨g1, g2⟩ := hGoodI t i.1 i.1.2
    exact ⟨g1, g2, ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents (Vc D j).rank _).2 ⟨i.2, hi.2.2, hi.1, hi.2.1, rfl⟩).2.1⟩
  exact (GlobalTheory.T.inertHeckeOperators_lifts_rational_selfAdjoint_labels R.toRealDat F.lv2 core.lev core.fam core.models j t (A3.okI t × List ℕ) (fun i => R.plI i.1)
    (fun i => GlobalTheory.Hk3.labIn (Vc D j).rank i.2) (A3.heckeLI j t) (fun i => Formalism.L2.Col.InertTypeOk (Vc D j).rank i.2) hty
    (hC.inert.hL j t).some (Q, s) hs).2.2.2 h hh x

theorem inert_vanish (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (j : Fin D.R.m) (t : T) (Q : A3.okI t) (s : List ℕ)
    (h0 : A3.heckeLI j t (Q, s) = 0) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R.toRealDat t pl ∧
      (∀ h, IsOpsV R.toRealDat j t h → ∀ x, R.jV j t (A3.heckeLI j t (Q, s) x) = h pl cV (R.jV j t x)) ∧
        MatchW R.toRealDat j t pl cV cW := by
  obtain ⟨hCore, -, hGoodI, -, -, -, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := hCore hEx
  obtain ⟨hg, -⟩ := hGoodI t Q Q.2
  refine ⟨R.plI Q, 0, 0, hg, fun h hh x => ?_, match_zero R.toRealDat core.models j t _⟩
  exact op_zero R.toRealDat core.models j t (R.plI Q) hg (A3.heckeLI j t (Q, s)) h0 h hh x

end Inert

theorem every_op_label : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ j t, ∃ pl cV cW, LiftDict R j t pl cV cW := by
  intro hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hI hC hEx hS hJ j t
  have core := (GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC).1 hEx
  have key : ∀ i : (A3.liftI j t).OpIx, ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R.toRealDat t pl ∧
      (∀ h, IsOpsV R.toRealDat j t h → ∀ x, R.jV j t ((A3.liftI j t).opAll i x) = h pl cV (R.jV j t x)) ∧
      MatchW R.toRealDat j t pl cV cW := by
    rintro (⟨P, k⟩ | ⟨Q, s⟩)
    · by_cases hk : k ≤ (Vc D j).rank
      · exact split_low R.toRealDat F.lv2 core hS j t P k hk
      · exact split_high R.toRealDat F.lv2 core j t P k hk
    · rcases hJ.L j t Q s with h0 | ⟨s', hs', he⟩
      · exact inert_vanish R F hC hEx j t Q s h0
      · have hrank : A3.A.r + A3.A.t = (Vc D j).rank := (R.B.rankL j).symm
        rw [hrank] at hs'
        obtain ⟨pl, cV, cW, g, o, m⟩ := inert_valid R F hH hI hC hEx hS j t Q s' hs'
        refine ⟨pl, cV, cW, g, fun h hh x => ?_, m⟩
        have e : (A3.liftI j t).opAll (Sum.inr (Q, s)) = A3.heckeLI j t (Q, s') := he
        rw [e]
        exact o h hh x
  choose pl cV cW h1 h2 h3 using key
  exact ⟨pl, cV, cW, ⟨h1, fun h hh i x => h2 i h hh x, h3⟩⟩

end GlobalTheory.LiftDictionary

end
