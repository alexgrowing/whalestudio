import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LvSameZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelReadAsReference
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.RepZero

open Formalism.L2.Col GlobalTheory.Mem.Col2.StepZero

theorem chr_of_down_eq_one {X : Fields} {n : ℕ} {ST SG Q : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers X.E))}
    {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
    (pref : DecoF X.E n ST SG Q → Prop) {Λ₀ : LevFam X.E X.K n SG} (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q)
    (b : β) (g : (stepY ST y β Λ Θ pref).G b) (h : down pref hΛ b g = 1) : (stepY ST y β Λ Θ pref).chr b g = 1 := by
  show (Λ b).chr g.2.1 * (Θ b).chr g.2.2 = 1
  rw [chr_eq_one (hΘ b), mul_one, chr_congr (hΛ b)]
  have e : (⟨g.2.1.1, hΛ b ▸ g.2.1.2⟩ : Λ₀.grp) = (down pref hΛ b g).2 := rfl
  rw [e, h]
  exact map_one _

theorem exists_lift_one {X : Fields} {n : ℕ} {ST SG Q : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers X.E))}
    {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
    (pref : DecoF X.E n ST SG Q → Prop) {Λ₀ : LevFam X.E X.K n SG} (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (b : β) (p q : (stepY ST y β Λ Θ pref).D b) (h : p.1.1.deco = q.1.1.deco) :
    ∃ g : (stepY ST y β Λ Θ pref).G b, (stepY ST y β Λ Θ pref).gam b g = 1 ∧ g • p = q ∧ (stepY ST y β Λ Θ pref).chr b g = 1 := by
  obtain ⟨g, h2, h3⟩ := exists_lift pref hy hΛ hΘ b p q 1 (by rw [one_smul]; exact h)
  exact ⟨g, (congrArg (fun g => ufGL X.E n g.1) h2).trans (map_one _), h3, chr_of_down_eq_one pref hΛ hΘ b g h2⟩

end GlobalTheory.Fam.RepZero

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Fam.rep_zero_std : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ c : {c // A.chOf 0 c = β}, ∃ κ : (A.K 0 (Nat.zero_le _) β).lev.U, ((C.forms u).to0.cls0.y ((I.eCls0 l u a).symm c.1)).1 = ((A.K 0 (Nat.zero_le _) β).y c).1 * κ.1 ∧ (A.K 0 (Nat.zero_le _) β).lev.chi κ = 1 := by
  intro B X I hI _ l Z C hC u a Ch A hA β hk c
  obtain ⟨c, rfl⟩ := c
  set c' := (I.eCls0 l u a).symm c with hc'
  have hR := hA.reads 0 (Nat.zero_le _)
  have hyS : ((C.forms u).to0.cls0.y c').1 = I.yStd u 0 c' := (hC u).yE 0 (Nat.zero_le _) (Or.inl rfl) c'
  have hS := MemChart.yStd_spec I hI u 0 c'
  set yc : TC.GA B (B.R.N 0) := ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1 with hyc
  have hd : Disjoint (B.primes X).vGs (I.Q a) := (LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)
  let q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0 := extTo (I.Q a) (extTo I.SQ ((I.stp u I.mu0 0).rep c').1.1)
  have hq : TC.PtOf (yc * (yc⁻¹ * I.yStd u 0 c') * A.kb 0 (A.chOf 0 c)) q := by
    rw [mul_inv_cancel_left, hk]
    exact IsPtOf.extTo (I.Q_subset_SQ a) hd hS
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  have e : ((I.stp u a 0).rep c).1.1.deco = ((I.stp u I.mu0 0).rep c').1.1.deco := by
    have := TC.StepZero.rep_eCls0 I hI l u a c'
    rwa [hc', Equiv.apply_symm_apply] at this
  obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
  obtain ⟨g, hgam, h3, hchr⟩ := RepZero.exists_lift_one ((I.Tp a).pref u 0) hy hΛ hΘ c.1 ((I.stp u a 0).rep c) p
    (by rw [hp]; exact e)
  have hact : ((I.stp u a 0).act c.1 g ((I.stp u a 0).rep c)).1.1 = q :=
    (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp
  have hmem : yc⁻¹ * I.yStd u 0 c' ∈ (A.K 0 (Nat.zero_le _) (A.chOf 0 c)).lev.U :=
    (hR.lev c _ q hq).2 ⟨g, hgam, hact, TC.Chart0.cos0 I _ _⟩
  refine ⟨⟨yc⁻¹ * I.yStd u 0 c', hmem⟩, ?_, ?_⟩
  · show _ = yc * (yc⁻¹ * I.yStd u 0 c')
    rw [hyS, mul_inv_cancel_left]
  · have hpt2 : TC.PtOf (yc * (yc⁻¹ * I.yStd u 0 c') * A.kb 0 (A.chOf 0 c))
        ((I.stp u a 0).act c.1 g ((I.stp u a 0).rep c)).1.1 := by
      rw [hact]
      exact hq
    have hc := hR.chr c ⟨yc⁻¹ * I.yStd u 0 c', hmem⟩ g hgam hpt2
    apply Units.ext
    refine hc.trans ?_
    rw [hchr]
    simp
