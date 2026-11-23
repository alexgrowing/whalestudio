import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead

theorem smallAt_natCast_mul {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal) {t : EAf D}
    (ht : t ∈ GlobalTheory.StdFrames.OA D) : SmallAt PP ((N : EAf D) * t) := by
  unfold SmallAt
  rw [map_mul, map_natCast, Valuation.map_mul]
  have hv : Valued.v (N : PP.adicCompletion D.host.E) < 1 := by
    have := (PP.valuation_lt_one_iff_mem (K := D.host.E) (N : 𝓞 D.host.E)).2 hN
    rw [← Formalism.UG.P.levelaf_valued_algebraMap] at this
    simpa using this
  have ht' := (GlobalTheory.AdIsom.mem_OA t).1 ht PP
  exact lt_of_le_of_lt (mul_le_of_le_one_right' ht') hv

theorem sg_hY {D : D7} (x y : Fin (Yc D 0).rank → EAf D) : GlobalTheory.StdFrames.sg D (hY D x y) = hY D y x := by
  have := GlobalTheory.AdIsom.cjA_hA (Yc D 0) y x
  rw [GlobalTheory.AdIsom.hA_eq, GlobalTheory.AdIsom.hA_eq] at this
  exact this

theorem smallAt_of_mul {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal) {c : EAf D}
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, c = (N : EAf D) * t) : SmallAt PP c := by
  obtain ⟨t, ht, rfl⟩ := h
  exact smallAt_natCast_mul hN ht

theorem smallAt_hY_of_swap {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {x y : Fin (Yc D 0).rank → EAf D} {d : EAf D} (hd : GlobalTheory.StdFrames.sg D d = d)
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, hY D y x - d = (N : EAf D) * t) : SmallAt PP (hY D x y - d) := by
  obtain ⟨t, ht, e⟩ := h
  have e' := congrArg (GlobalTheory.StdFrames.sg D) e
  rw [map_sub, sg_hY, hd, map_mul, map_natCast] at e'
  rw [e']
  exact smallAt_natCast_mul hN (GlobalTheory.AdIsom.cjA_mem ht)

theorem smallAt_hY_of_swap0 {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {x y : Fin (Yc D 0).rank → EAf D} (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, hY D y x = (N : EAf D) * t) :
    SmallAt PP (hY D x y) := by
  have := smallAt_hY_of_swap hN (x := x) (y := y) (d := 0) (map_zero _) (by simpa using h)
  simpa using this

theorem smallAt_hY_of_swap_delta {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {ι : Type} [DecidableEq ι] {a c : ι} {x y : Fin (Yc D 0).rank → EAf D}
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, hY D y x - (if c = a then 1 else 0) = (N : EAf D) * t) :
    SmallAt PP (hY D x y - if a = c then 1 else 0) := by
  refine smallAt_hY_of_swap hN (by split_ifs <;> simp) ?_
  simpa only [eq_comm (a := a)] using h

theorem smallAt_sub_of_cpt {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {ι : Type} [DecidableEq ι] {i j : ι} {c e : EAf D} (he : GlobalTheory.StdFrames.cpt PP e = 1)
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, c - (if i = j then e else 0) = (N : EAf D) * t) :
    SmallAt PP (c - if i = j then 1 else 0) := by
  obtain ⟨t, ht, e'⟩ := h
  have h1 : GlobalTheory.StdFrames.cpt PP (c - if i = j then 1 else 0) = GlobalTheory.StdFrames.cpt PP ((N : EAf D) * t) := by
    rw [← e']
    split_ifs <;> simp [he]
  have h2 := smallAt_natCast_mul hN ht
  unfold SmallAt at h2 ⊢
  rwa [h1]

theorem pairTable_of_cpt_one : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (bwT X h) (bwdT X h) (z0T X h) := by
  intro D X h PP hg hew
  have F0g := X.gramIntegral
  have F0z := X.formsAtZero
  have F0W := X.weightVectorsIntegral
  have bd := X.bw_dual
  have ge := X.g_eq
  rcases X with ⟨⟨I⟩⟩
  dsimp only at h F0g F0z F0W bd ge hew ⊢
  subst h
  subst ge
  refine ⟨fun a c => smallAt_hY_of_swap_delta hg (F0g c a).2.2, fun a j => smallAt_of_mul hg ((F0W j).2.2 a).2.1,
    fun a => smallAt_of_mul hg (F0z.2 a).2, fun a c => smallAt_of_mul hg (F0g a c).2.1,
    fun i a => smallAt_hY_of_swap0 hg ((F0W i).2.2 a).2.2.1, fun i j => smallAt_sub_of_cpt hg hew (bd i j),
    fun i => smallAt_hY_of_swap0 hg (F0W i).2.1, fun i a => smallAt_hY_of_swap0 hg ((F0W i).2.2 a).2.2.2,
    fun a => smallAt_hY_of_swap0 hg (F0z.2 a).1, fun j => smallAt_of_mul hg (F0W j).1, smallAt_of_mul hg F0z.1,
    fun a => smallAt_hY_of_swap0 hg (F0z.2 a).2, fun a c => smallAt_of_mul hg (F0g a c).1,
    fun a j => smallAt_of_mul hg ((F0W j).2.2 a).1, fun a => smallAt_of_mul hg (F0z.2 a).1,
    fun a c => smallAt_of_mul hg (F0g a c).2.2⟩

end GlobalTheory.SeeConjRead
