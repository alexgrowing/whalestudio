import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalHeckeAtLevelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsGoodSplitHeckePlaceOfSplitNotExcludedStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState

open Formalism.BasicNotions.TH Formalism.IndefR.Mult

theorem isDC_one' {G : Type} [Group G] (J : Subgroup G) : Formalism.IndefR.Bridge.IsDC J 1 {1} := by
  refine ⟨fun a ha => ⟨1, 1, by simpa using ha⟩, ?_⟩
  rintro g ⟨k, k', rfl⟩
  exact ⟨1, ⟨Finset.mem_singleton_self _, by simpa using J.mul_mem k.2 k'.2⟩, fun a ha => Finset.mem_singleton.1 ha.1⟩

theorem isHeckeAt_zero_one' {D : D7} (V : HSp D) {P : PlE D.host} (hP : Formalism.BasicNotions.IsSplitPl D.host P) :
    IsHeckeAt V P 0 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P ((GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hP)
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  exact ⟨e, ϖ, he, h1, h2, GlobalTheory.HeckeParts.isHeckeElt_one V he.1 ϖ⟩

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem heckeScalar_eq (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (P : PlE D.host) (k : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R.toRealDat i P k = hkNorm R i k P := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar, hkNorm, zpow_neg, zpow_natCast, inv_pow]
end

theorem heckeOn_one {D : D7} {V : HSp D} {S} (M : DSModel V S) (F : MMap M) : heckeOn M {1} F = F := by
  ext v g
  simp [heckeOn, postOn, heckeLin]

end GlobalTheory.HeightCounting.RatSide.HeckeAtState

namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState

open Formalism.BasicNotions.TH Formalism.IndefR.Mult

section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in

def famOf (R : RealDat3 D A3 Ks) (hq : ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i) (j : ℕ) (k : ℕ)
    (Pl : PlE D.host) : Module.End D.what₂.LL (Fin (R.nW (idxOf D j)) → D.what₂.LL) :=
  if h : k ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat Pl ∧ k ≤ D.R.r then
    Classical.choose (hq (idxOf D j) Pl h.2.1 k h.2.2)
  else 1

theorem famOf_zero (R : RealDat3 D A3 Ks) (hq : ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i) (j : ℕ)
    (Pl : PlE D.host) : famOf R hq j 0 Pl = 1 := by
  unfold famOf
  rw [dif_neg (fun h => h.1 rfl)]

theorem exists_heckeRd (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Sb : Finset (PlE D.host))
    (hq : ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i)
    (hg : ∀ v : PlE D.host, IsSplitPl D.host v → v ∉ Sb → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat v) :
    ∃ hL' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j),
      StabC (ratDatR R cG kKs hk) hL' ∧ (∀ j Pl, hL' j 0 Pl = 1) ∧ HeckeRd R cG kKs hk Sb hL' := by
  refine ⟨famOf R hq, ?_, fun j Pl => famOf_zero R hq j Pl, ?_⟩
  · intro j _ _ k Pl y hy
    change famOf R hq j k Pl y ∈ (R.FW (idxOf D j)).WK
    unfold famOf
    split_ifs with h
    · exact (Classical.choose_spec (hq (idxOf D j) Pl h.2.1 k h.2.2)).2 y hy
    · exact hy
  · intro j k Pl α Rr _ _ hd y
    have hg' : GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat Pl := hg Pl hd.split hd.offS
    by_cases hk0 : k = 0
    · subst hk0
      have hr := (Classical.choose_spec (hq (idxOf D j) Pl hg' 0 (Nat.zero_le _))).1
      have e1 := (GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_iff _ _ _ _ _ _).1 (hr Rr ⟨α, hd.elt, hd.reps⟩) y
      have e2 := (GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_iff _ _ _ _ _ _).1
        (hr {1} ⟨1, isHeckeAt_zero_one' _ hd.split, isDC_one' _⟩) y
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar_zero, one_smul] at e1 e2
      have e4 := (e2.trans (heckeOn_one _ _)).symm.trans e1
      have hn : hkNorm R (idxOf D j) 0 Pl = 1 := by simp [hkNorm]
      rw [famOf_zero, hn, one_smul]
      exact e4
    · have h : k ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat Pl ∧ k ≤ D.R.r := ⟨hk0, hg', hd.le⟩
      have e1 := (GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_iff _ _ _ _ _ _).1
        ((Classical.choose_spec (hq (idxOf D j) Pl h.2.1 k h.2.2)).1 Rr ⟨α, hd.elt, hd.reps⟩) y
      have h1 : famOf R hq j k Pl = Classical.choose (hq (idxOf D j) Pl h.2.1 k h.2.2) := by
        unfold famOf
        rw [dif_pos h]
      rw [h1, ← heckeScalar_eq]
      exact e1
end Gen

end GlobalTheory.HeightCounting.RatSide.HeckeAtState

namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState

theorem heckeAtState : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∃ hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j), StabC (SOf x) hL' ∧ (∀ j Pl, hL' j 0 Pl = 1) ∧ HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' := by
  intro hL hD hT hR
  refine (GlobalTheory.T.rational_hecke_at_levels hL hD hT hR).trans (StepW.of_all fun K B f T w _ _ H P x l => ?_)
  exact exists_heckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) (H P x l) (GlobalTheory.T.isGoodSplitHeckePlace_of_split_not_excluded P x)

end GlobalTheory.HeightCounting.RatSide.HeckeAtState

end
