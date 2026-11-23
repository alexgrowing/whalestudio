import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section

namespace GlobalTheory.NormRatio.ChrFin

open Formalism.L2.JoinChr

theorem toFinE_inc (D : D7) (a : D.host.E) :
    GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D a) = algebraMap D.host.E _ a :=
  (GlobalTheory.LFun.toFinAd_tmul 1 a).trans (by rw [map_one, one_mul])

theorem toFinE_int (D : D7) {r : Formalism.MainNotions.StandardLatticesGL3.AE D} (hr : r ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Valued.v (GlobalTheory.BotFormula.toFinE D r P) ≤ 1 := by
  let S : Subring (Formalism.MainNotions.StandardLatticesGL3.AE D) := (Formalism.UG.intAd D.host.E).comap (GlobalTheory.BotFormula.toFinE D).toRingHom
  have hS : Formalism.MainNotions.StandardLatticesGL3.OhE D ≤ S := by
    refine Subring.closure_le.2 ?_
    rintro z (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨x', rfl⟩ := hx
      intro Q
      change GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D _) Q ∈ _
      rw [toFinE_inc, HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v ((algebraMap D.host.E (Q.adicCompletion D.host.E)) _) ≤ 1
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q _).trans_le (Q.valuation_le_one x')
    · intro Q
      have h := (GlobalTheory.LFun.mem_int_iff (F := ℚ) (E := D.host.E) (y ⊗ₜ[ℚ] ((1 : 𝓞 D.host.E) : D.host.E))).1
        (AddSubgroup.subset_closure ⟨y, fun v => hy v, 1, rfl⟩) Q
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact h
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hS hr P)

theorem adEquiv_eq (D : D7) (z : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    GlobalTheory.Mem.Col2.SplitChar.adEquiv D z = GlobalTheory.BotFormula.toFinE D z := by
  refine GlobalTheory.PlaceIdem.adele_ext fun P => ?_
  let f1 : Formalism.MainNotions.StandardLatticesGL3.AE D →+* P.adicCompletion D.host.E :=
    (RestrictedProduct.evalRingHom _ P).comp (GlobalTheory.Mem.Col2.SplitChar.adEquiv D).toRingHom
  let f2 : Formalism.MainNotions.StandardLatticesGL3.AE D →+* P.adicCompletion D.host.E :=
    (RestrictedProduct.evalRingHom _ P).comp (GlobalTheory.BotFormula.toFinE D).toRingHom
  change f1 z = f2 z
  by_contra hne
  have hd : Valued.v (f1 z - f2 z) ≠ 0 := (Valuation.ne_zero_iff _).2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn, hv⟩ := GlobalTheory.Mem.Col2.SplitChar.exists_nat_val_lt P hd
  obtain ⟨a, r, hr, hz⟩ := GlobalTheory.Mem.Col2.SplitChar.exists_approx z hn
  have ha : f1 (Formalism.MainNotions.StandardLatticesGL3.inc D a) = f2 (Formalism.MainNotions.StandardLatticesGL3.inc D a) := by
    change GlobalTheory.Mem.Col2.SplitChar.adEquiv D (Formalism.MainNotions.StandardLatticesGL3.inc D a) P = GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D a) P
    rw [GlobalTheory.Mem.Col2.SplitChar.adEquiv_inc, toFinE_inc]
  have e1 : f1 z - f2 z = (n : P.adicCompletion D.host.E) * (f1 r - f2 r) := by
    rw [hz, map_add, map_add, map_mul, map_mul, map_natCast, map_natCast, ha]
    ring
  have h1 : Valued.v (f1 r) ≤ 1 := GlobalTheory.Mem.Col2.SplitChar.vl_le hr P
  have h2 : Valued.v (f2 r) ≤ 1 := toFinE_int D hr P
  have h3 : Valued.v (f1 r - f2 r) ≤ 1 := Valuation.map_sub_le _ h1 h2
  have h4 : Valued.v ((n : P.adicCompletion D.host.E)) = P.valuation D.host.E (n : D.host.E) := by
    rw [← map_natCast (algebraMap D.host.E (P.adicCompletion D.host.E)) n]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _
  have h5 : Valued.v (f1 z - f2 z) ≤ P.valuation D.host.E (n : D.host.E) := by
    rw [e1, map_mul, h4]
    exact mul_le_of_le_one_right' h3
  exact absurd (h5.trans_lt hv) (lt_irrefl _)

theorem chrEq_of_finPart : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) {N : ℕ} (c : Formalism.MainNotions.StandardLatticesGL3.HeckeU D N) (e : ℤ)
    (ν : Formalism.L2.Host.HChar D.host.E),
    IsHeckeChar D χ → HasFinPart χ c (-e) → (∀ x, c.f x ^ e = (ν⁻¹).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x)) →
      ChrEq χ ν := by
  intro D χ N c e ν hχ hf hν
  refine ⟨hχ, fun P ε hε k x hx => ?_⟩
  have hι : ∀ x : D.host.E, GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x :=
    fun x => (GlobalTheory.LFun.toFinAd_tmul 1 x).trans (by rw [map_one, one_mul])
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.HeckeTensorRead.isPlIdem_parts D (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E) hι
    GlobalTheory.LFun.mem_int_iff hε
  have hinf : infPart D (x : AE D) = 1 := by
    rw [hx, locE, GlobalTheory.HeckeTensorRead.map_loc (infPart D), h1, zero_mul, add_zero]
  have hfin : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) =
      Neutral.B1.finiteSingle D.host.E P (algebraMap D.host.E _ (k : D.host.E)) := by
    have h4 : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (incA D (k : D.host.E))) =
        algebraMap D.host.E _ (k : D.host.E) := hι _
    have h5 : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (locE D ε (k : D.host.E))) =
        1 + GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D ε) *
          (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (incA D (k : D.host.E))) - 1) :=
      GlobalTheory.HeckeTensorRead.map_loc ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp (finPart D)) ε _
    rw [hx, h5]
    exact GlobalTheory.HeckeTensorRead.loc_eq_finSingle P _ _ _ h4 h2 h3
  let u : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    Units.map ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp (finPart D)).toMonoidHom x
  let y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ := Units.map (GlobalTheory.BotFormula.toFinE D).symm.toRingHom.toMonoidHom u
  have hy1 : GlobalTheory.BotFormula.toFinE D (y : Formalism.MainNotions.StandardLatticesGL3.AE D) =
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) :=
    (GlobalTheory.BotFormula.toFinE D).apply_symm_apply _
  have hxy : IsFinIdl x y := ⟨hinf, hy1.symm⟩
  have hval := hf x y hxy
  have hy : GlobalTheory.Mem.Col2.SplitChar.finIdl D y = Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k) := by
    refine Units.ext (Prod.ext rfl ?_)
    rw [GlobalTheory.Mem.Col2.SplitChar.finIdl_snd, adEquiv_eq, hy1, hfin]
    rfl
  have hc : c.f y ^ (-e) = ν.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) := by
    rw [zpow_neg, hν y]
    rfl
  rw [hval, hc, hy]
  rfl

end GlobalTheory.NormRatio.ChrFin
