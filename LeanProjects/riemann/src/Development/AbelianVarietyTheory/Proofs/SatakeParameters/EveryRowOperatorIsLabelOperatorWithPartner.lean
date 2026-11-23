import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLiftStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsRowsRationalSelfAdjointLabelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeakStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowDictR

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hk_zero (V : HSp D) (P : Pl D.host.E) : hk V P 0 = 0 := by
  unfold hk; exact Finsupp.sum_zero_index

theorem hkF_zero (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (F : Bridge.Gf V → W) :
    hkF V P 0 F = 0 := by
  funext h; unfold hkF; exact Finsupp.sum_zero_index

theorem postOn_hk_zero {V : HSp D} {S : _} (M : DSModel V S) (P : Pl D.host.E) (z : MMap M) : postOn M (hk V P 0) z = 0 := by
  rw [hk_zero]
  rfl

set_option maxHeartbeats 1000000 in

theorem entry_zero (R : RealDat3 D A3 Ks) (hM : R.toRealDat.IsModels) (t : T) (i : (A3.rowI t).OpIx) (p : Pl D.host.E)
    (hp : Good R.toRealDat t p) (h0 : ∀ x, (A3.rowI t).opAll i x = 0) :
    ∃ cX c0 : List ℤ →₀ ℂ, (∀ h, IsOpsX R.toRealDat t h → ∀ x, R.jX t ((A3.rowI t).opAll i x) = h p cX (R.jX t x)) ∧
      MatchE R.toRealDat t p cX c0 := by
  refine ⟨0, 0, fun h hh x => ?_, fun y y' hy => ?_⟩
  · have hx : (A3.rowI t).opAll i x = 0 := h0 x
    refine (congrArg (R.jX t) hx).trans ((R.jX t).map_zero.trans ?_)
    refine ((hM.HX t).1 ?_).symm
    refine (hh p hp 0 (R.jX t x)).trans ?_
    rw [hkF_zero, LinearMap.map_zero]
  · have hy0 : y' = 0 := (hM.HX t).1 (by rw [hy, LinearMap.map_zero, hkF_zero])
    subst hy0
    have e1 : R.HE.e (R.Th t 0) = 0 := by simp
    exact e1.trans (postOn_hk_zero _ _ _).symm

set_option maxHeartbeats 1000000 in

theorem entry_split (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hL : GlobalTheory.Chain.LiftInteg D) (hW : R.WeakCharacterisation F)
    (hE : R.toRealDat.ExAt) (hS : SchurAll R.toRealDat) (t : T) (P0 : A3.A.ok t) (k : ℕ) :
    ∃ (p : Pl D.host.E) (cX c0 : List ℤ →₀ ℂ), Good R.toRealDat t p ∧
      (∀ h, IsOpsX R.toRealDat t h → ∀ x, R.jX t ((A3.rowI t).opAll (Sum.inl (P0, k)) x) = h p cX (R.jX t x)) ∧
      MatchE R.toRealDat t p cX c0 := by
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hW hE).1
  have hg : Good R.toRealDat t (R.pl P0.1) :=
    ((GlobalTheory.T.theta_lift_levels_good_primes_properties R.toRealDat F.lv2 hcore.lev).2.2.2 hcore.fam t P0.1 P0.2).1
  by_cases hk : k ≤ D.sp.X'.rank
  · have hz := GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift R.toRealDat F.lv2 hL hcore hS t P0
    have hop := (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hcore.lev hcore.fam hcore.models).1 t
    have hm : MatchE R.toRealDat t (R.pl P0.1) (Finsupp.single (splitLab D.sp.X'.rank k) 1)
        (splitC (Yc D 0).rank (hz.choose k)) := hz.choose_spec.1 k hk
    refine ⟨R.pl P0.1, Finsupp.single (splitLab D.sp.X'.rank k) 1, splitC (Yc D 0).rank (hz.choose k), hg,
      fun h hh x => ?_, hm⟩
    have ex : (A3.rowI t).opAll (Sum.inl (P0, k)) x = A3.A.heckeR t (P0, k) x := rfl
    exact (congrArg (R.jX t) ex).trans (hop h hh P0 k hk x)
  · have hd := (hcore.fam.degR t P0).2 k (not_le.1 hk)
    have h0 : ∀ x, (A3.rowI t).opAll (Sum.inl (P0, k)) x = 0 := fun x =>
      (LinearMap.congr_fun hd x).trans (LinearMap.zero_apply x)
    have hz := entry_zero R hcore.models t (Sum.inl (P0, k)) (R.pl P0.1) hg h0
    exact ⟨_, hz.choose, hz.choose_spec.choose, hg, hz.choose_spec.choose_spec.1, hz.choose_spec.choose_spec.2⟩

set_option maxHeartbeats 1000000 in

theorem entry_valid (hH : HoweUnram) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hL : GlobalTheory.Chain.LiftInteg D) (hW : R.WeakCharacterisation F)
    (hE : R.toRealDat.ExAt) (hS : SchurAll R.toRealDat) (t : T) (Q : A3.okI t) (s s' : List ℕ)
    (hs' : Formalism.L2.Col.InertTypeOk D.sp.X'.rank s') (he : A3.heckeRI t (Q, s) = A3.heckeRI t (Q, s')) :
    ∃ (cX c0 : List ℤ →₀ ℂ),
      (∀ h, IsOpsX R.toRealDat t h → ∀ x, R.jX t ((A3.rowI t).opAll (Sum.inr (Q, s)) x) = h (R.plI Q.1) cX (R.jX t x)) ∧
      MatchE R.toRealDat t (R.plI Q.1) cX c0 := by
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hW hE).1
  have hQ := (GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hW).2.2.1
  have hg := (hQ t Q.1 Q.2).1
  have hc := (hQ t Q.1 Q.2).2
  have hTwo := GlobalTheory.T.twoSidedHeckePartner_inertPrime hH R.toRealDat F.lv2 hL hcore hS t _ hg hc (GlobalTheory.T.hyperspecialFixesAllChainVacua_at_inert_prime R F hW t _ hg hc)
  have hpre : ∀ j : A3.okI t × List ℕ, Formalism.L2.Col.InertTypeOk D.sp.X'.rank j.2 →
      Good R.toRealDat t (R.plI j.1.1) ∧ conjPl (R.plI j.1.1) = R.plI j.1.1 ∧
        (GlobalTheory.Hk3.labIn D.sp.X'.rank j.2).Pairwise (fun a b => b ≤ a) := fun j hj =>
    ⟨(hQ t j.1.1 j.1.2).1, (hQ t j.1.1 j.1.2).2, ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents D.sp.X'.rank (GlobalTheory.Hk3.labIn D.sp.X'.rank j.2)).2
      ⟨j.2, hj.2.2, hj.1, hj.2.1, rfl⟩).2.1⟩
  have hR := GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels R.toRealDat F.lv2 hcore.lev hcore.fam hcore.models t (A3.okI t × List ℕ)
    (fun j => R.plI j.1.1) (fun j => GlobalTheory.Hk3.labIn D.sp.X'.rank j.2) (A3.heckeRI t)
    (fun j => Formalism.L2.Col.InertTypeOk D.sp.X'.rank j.2) hpre (hW.inert.hR t).some (Q, s') hs'
  have hop := hR.2.2.2
  have hc0 := hTwo.1.1 (Finsupp.single (GlobalTheory.Hk3.labIn D.sp.X'.rank s') 1)
  refine ⟨_, hc0.choose, fun h hh x => ?_, hc0.choose_spec⟩
  have ex : (A3.rowI t).opAll (Sum.inr (Q, s)) x = A3.heckeRI t (Q, s') x := LinearMap.congr_fun he x
  exact (congrArg (R.jX t) ex).trans (hop h hh x)

set_option maxHeartbeats 4000000 in

theorem entry_inert (hH : HoweUnram) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hL : GlobalTheory.Chain.LiftInteg D) (hW : R.WeakCharacterisation F)
    (hE : R.toRealDat.ExAt) (hS : SchurAll R.toRealDat) (hJ : InertJunk A3) (t : T) (Q : A3.okI t) (s : List ℕ) :
    ∃ (p : Pl D.host.E) (cX c0 : List ℤ →₀ ℂ), Good R.toRealDat t p ∧
      (∀ h, IsOpsX R.toRealDat t h → ∀ x, R.jX t ((A3.rowI t).opAll (Sum.inr (Q, s)) x) = h p cX (R.jX t x)) ∧
      MatchE R.toRealDat t p cX c0 := by
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hW hE).1
  have hg := ((GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hW).2.2.1 t Q.1 Q.2).1
  by_cases hv : Formalism.L2.Col.InertTypeOk D.sp.X'.rank s
  · have hz := entry_valid hH R F hL hW hE hS t Q s s hv rfl
    exact ⟨_, hz.choose, hz.choose_spec.choose, hg, hz.choose_spec.choose_spec.1, hz.choose_spec.choose_spec.2⟩
  · have hj := hJ.R t Q s
    rcases hj with h0 | hs
    · have h0' : ∀ x, (A3.rowI t).opAll (Sum.inr (Q, s)) x = 0 := fun x =>
        (LinearMap.congr_fun h0 x).trans (LinearMap.zero_apply x)
      have hz := entry_zero R hcore.models t (Sum.inr (Q, s)) (R.plI Q.1) hg h0'
      exact ⟨_, hz.choose, hz.choose_spec.choose, hg, hz.choose_spec.choose_spec.1, hz.choose_spec.choose_spec.2⟩
    · have hok : Formalism.L2.Col.InertTypeOk D.sp.X'.rank hs.choose := by
        rw [R.B.rankR]; exact hs.choose_spec.1
      have hz := entry_valid hH R F hL hW hE hS t Q s hs.choose hok hs.choose_spec.2
      exact ⟨_, hz.choose, hz.choose_spec.choose, hg, hz.choose_spec.choose_spec.1, hz.choose_spec.choose_spec.2⟩

set_option maxHeartbeats 4000000 in

theorem rowDict_exists : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ t, ∃ pl cX c0, RowDict R t pl cX c0 := by
  intro hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hL hW hE hS hJ t
  have key : ∀ i : (A3.rowI t).OpIx, ∃ (p : Pl D.host.E) (cX c0 : List ℤ →₀ ℂ), Good R.toRealDat t p ∧
      (∀ h, IsOpsX R.toRealDat t h → ∀ x, R.jX t ((A3.rowI t).opAll i x) = h p cX (R.jX t x)) ∧
      MatchE R.toRealDat t p cX c0 := by
    rintro (⟨P, k⟩ | ⟨Q, s⟩)
    · exact entry_split R F hL hW hE hS t P k
    · exact entry_inert hH R F hL hW hE hS hJ t Q s
  choose pl cX c0 hg hop hm using key
  exact ⟨pl, cX, c0, ⟨hg, fun h hh i x => hop i h hh x, hm⟩⟩

end GlobalTheory.RowDictR
