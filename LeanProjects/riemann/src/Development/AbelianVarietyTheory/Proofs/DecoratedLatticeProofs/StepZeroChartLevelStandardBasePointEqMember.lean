import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroApproximationTwistPrimesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ZeroLevel

open Formalism.L2.Col Formalism.L2.Ker Formalism.UG GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

theorem stepZeroReduction_of_moved_representative (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (y : TC.GA B (B.R.N 0))
    (hy : TC.PtOf (y * TC.kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1)) (x : TC.GA B (B.R.N 0))
    (κ : (I.stp u a 0).G c.1) (h1 : (I.stp u a 0).gam c.1 κ = 1)
    (h2 : TC.PtOf (y * x * TC.kStd X u (B.R.N 0)) ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1) :
    ∃ hJ : x ∈ Formalism.L2.Col.J0 B.sp.cm (B.R.N 0) ((B.primes X).vT u),
      Formalism.L2.Col.redG B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs ⟨x, hJ⟩ = κ.2.1.1⁻¹ := by
  have hg := dia_of_pt hPr u hy
  have hx := dia_of_pt hPr u h2
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  exact red_of_act B.sp.cm (B.R.N 0) (Formalism.L2.Col.diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : Formalism.L2.Col.UF B.fields.E (B.R.N 0) × Formalism.L2.Col.GLG B.fields.E (B.R.N 0) (B.primes X).vGs) • _ = _
    rw [e1]
    rfl)

theorem stepZeroColumnLevel_eq_orbitStabilizer (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (y : TC.GA B (B.R.N 0))
    (hy : TC.PtOf (y * TC.kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1)) (x : TC.GA B (B.R.N 0))
    (q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) (h : TC.PtOf (y * x * TC.kStd X u (B.R.N 0)) q) :
    x ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (Formalism.L2.Col.colLev I.Ch 0).grp ↔
      ∃ κ : (I.stp u a 0).G c.1, (I.stp u a 0).gam c.1 κ = 1 ∧ ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1 = q ∧
        cosetIn ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)) = cosetIn ((I.stp u a 0).rep c) := by
  have hL := hI.idx_ok a
  have hy' := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  have hg := dia_of_pt hPr u hy
  have hx := dia_of_pt hPr u h
  constructor
  · intro hxU
    have h1 := act_of_mem B.sp.cm (B.R.N 0) _ (Formalism.L2.Col.diaT (Pr := B.primes X) u) hg.1 ⟨x, hxU⟩
    rw [hg.2, hx.2] at h1
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, h2, h3⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy' hΛ hΘ c.1 ((I.stp u a 0).rep c) p
      (1, (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩)⁻¹) (by rw [hp]; exact h1.symm)
    refine ⟨g, ?_, ?_, Chart0.cos0 I _ _⟩
    · show Formalism.L2.Col.ufGL B.fields.E (B.R.N 0) g.1 = 1
      rw [show g.1 = 1 from congrArg Prod.fst h2, map_one]
    · exact (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp
  · rintro ⟨κ, h1, h2, -⟩
    obtain ⟨hJ, hr⟩ := stepZeroReduction_of_moved_representative I hPr u a c y hy x κ h1 (h2 ▸ h)
    refine (Formalism.L2.Col.mem_levU _ _ _ _ _).2 ⟨hJ, ?_⟩
    have key : ∀ (Λ' : Formalism.L2.Col.LevFam B.fields.E B.fields.K (B.R.N 0) (B.primes X).vGs), Λ' = Formalism.L2.Col.colLev I.Ch 0 →
        ∀ g : Λ'.grp, g.1 ∈ (Formalism.L2.Col.colLev I.Ch 0).grp := by
      rintro _ rfl g
      exact g.2
    have hm : κ.2.1.1 ∈ (Formalism.L2.Col.colLev I.Ch 0).grp := key _ (hΛ c.1) κ.2.1
    rw [hr]
    exact inv_mem hm

end GlobalTheory.ZeroLevel

noncomputable section
namespace GlobalTheory.ZeroLevel
open Formalism.L2.Col Formalism.L2.Ker Formalism.UG GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

set_option maxHeartbeats 2000000 in

theorem right_lev (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z))
    (hC : I.StdC l Z C) (u : B.Word) (x : TC.GA B (B.R.N 0)) :
    x ∈ (C.forms u).to0.cls0.lev.U ↔
      x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp := by
  have hPr := l.pr
  obtain ⟨k, hR⟩ := (hC u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hyE := (hC u).yE 0 (Nat.zero_le _) (Or.inl rfl)
  obtain ⟨c, -⟩ := hR.onto ()
  haveI : NeZero (B.R.N 0) := ⟨(B.R.N_pos 0).ne'⟩
  have hQ : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  obtain ⟨p0, hp0, -⟩ := hR.k_std ()
  have hk : k () ∈ UAd B.sp.cm (B.R.N 0) := hp0.uni
  have h1 : TC.PtOf (I.yStd u 0 c * k ()) ((I.stp u I.mu0 0).rep c).1.1 := by
    have := hR.pt c
    rw [hyE c] at this
    exact GlobalTheory.Mem.SRe.StdUnique.pt_of_deco hQ (extTo_deco _ _).symm this
  have h2 : TC.PtOf (I.yStd u 0 c * TC.kStd X u (B.R.N 0)) ((I.stp u I.mu0 0).rep c).1.1 :=
    GlobalTheory.Mem.SRe.StdUnique.pt_of_deco hQ (extTo_deco _ _).symm (yStd_spec I hI u 0 c)
  have key : x ∈ UAd B.sp.cm (B.R.N 0) → (x ∈ (C.forms u).to0.cls0.lev.U ↔
      x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp) := by
    intro hx
    have hg : I.yStd u 0 c * x * k () ∈ UAd B.sp.cm (B.R.N 0) := by
      have e : I.yStd u 0 c * x * k () = (I.yStd u 0 c * k ()) * ((k ())⁻¹ * x * k ()) := by group
      rw [e]
      exact mul_mem h1.uni (mul_mem (mul_mem (inv_mem hk) hx) hk)
    obtain ⟨q, hq⟩ := GlobalTheory.Mem.Col2.ChiFinTop.exists_isPtOf_of_mem (ST := (B.primes X).vT u) (SG := (B.primes X).vGs)
      (Q := QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) B.sp.cm hQ hg
    have hq' : TC.PtOf (I.yStd u 0 c * x * TC.kStd X u (B.R.N 0)) q := by
      have e : I.yStd u 0 c * x * TC.kStd X u (B.R.N 0) =
          I.yStd u 0 c * x * k () * ((I.yStd u 0 c * k ())⁻¹ * (I.yStd u 0 c * TC.kStd X u (B.R.N 0))) := by group
      rw [e]
      exact GlobalTheory.Mem.Col2.PtStab.isPtOf_mul_stab _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 hq
    have a1 := hR.lev c x q (by rw [hyE c]; exact hq)
    exact a1.trans (Chart0.lev0 I hI hPr u I.mu0 c x q hq').symm
  constructor
  · intro hx
    exact (key (GlobalTheory.Mem.SRe.StdUnique.lev_le I l hI hP Z u 0 _ _ hx)).1 hx
  · intro hx
    exact (key (levU_le_UAd _ _ _ _ _ hx)).2 hx

set_option maxHeartbeats 2000000 in

theorem left_lev (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type)
    (A : GlobalTheory.AdForm.TwDat I l Z u a Ch) (hA : A.Is) (β : Ch 0) (hβ : A.kb 0 β = TC.kStd X u (B.R.N 0)) (x : TC.GA B (B.R.N 0)) :
    x ∈ (A.K 0 (Nat.zero_le _) β).lev.U ↔
      x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp := by
  have hPr := l.pr
  have hR := hA.reads 0 (Nat.zero_le _)
  obtain ⟨c, rfl⟩ := hA.chOf_onto 0 (Nat.zero_le _) β
  have hy : TC.PtOf ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * TC.kStd X u (B.R.N 0))
      (extTo I.SQ ((I.stp u a 0).rep c).1.1) := by
    have := hR.pt c
    rw [hβ] at this
    exact this
  have rat : ∀ (x : TC.GA B (B.R.N 0)) (q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0), TC.PtOf ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1) * x * TC.kStd X u (B.R.N 0)) q →
      (x ∈ (A.K 0 (Nat.zero_le _) (A.chOf 0 c)).lev.U ↔
        x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp) := fun x q h =>
    (hR.lev c x q (by rw [hβ]; exact h)).trans (stepZeroColumnLevel_eq_orbitStabilizer I hI hPr u a c _ hy x q h).symm
  have hg1 : gramN (I.rec7 l Z) 0 (Nat.zero_le _) = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 0 (Nat.zero_le _)).1
  have eU : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      UAd B.sp.cm (B.R.N 0) := by rw [hg1]; rfl
  have hUl : ∀ x, x ∈ (A.K 0 (Nat.zero_le _) (A.chOf 0 c)).lev.U → x ∈ UAd B.sp.cm (B.R.N 0) := fun x hx =>
    eU ▸ (((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).lev.U_eq x).1 hx).1
  constructor
  · intro hx
    obtain ⟨h, h1, h2, q, hq⟩ := GlobalTheory.T.stepZero_approximation_twistPrimes I hI hP l Z u a Ch A hA (A.chOf 0 c) hβ ⟨c, rfl⟩ x (hUl x hx)
    have e := (rat _ q hq).1 (mul_mem hx h1)
    have e2 := mul_mem e (inv_mem h2)
    rwa [mul_inv_cancel_right] at e2
  · intro hx
    obtain ⟨h, h1, h2, q, hq⟩ := GlobalTheory.T.stepZero_approximation_twistPrimes I hI hP l Z u a Ch A hA (A.chOf 0 c) hβ ⟨c, rfl⟩ x (levU_le_UAd _ _ _ _ _ hx)
    have e := (rat _ q hq).2 (mul_mem hx h2)
    have e2 := mul_mem e (inv_mem h1)
    rw [show x = x * h * h⁻¹ from (mul_inv_cancel_right x h).symm]
    exact e2

set_option maxHeartbeats 2000000 in

theorem lev_zero_std : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ x, x ∈ (A.K 0 (Nat.zero_le _) β).lev.U ↔ x ∈ (C.forms u).to0.cls0.lev.U := by
  intro B X I hI hP l Z C hC u a Ch A hA β hβ x
  exact (left_lev I hI hP l Z u a Ch A hA β hβ x).trans (right_lev I hI hP l Z C hC u x).symm

end GlobalTheory.ZeroLevel
