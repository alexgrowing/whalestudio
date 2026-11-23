import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterTrivialOnSubgroup
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpanPlaces

theorem pg_nonempty {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) : L.Pg.Nonempty := by
  obtain ⟨⟨W, hW, hWQ⟩⟩ := (inferInstance : Nonempty ((L.C.P.pb 0).asIdeal.primesOver (𝓞 D.host.E)))
  have hne : W ≠ ⊥ := by
    rintro rfl
    have := hWQ.over
    rw [Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)] at this
    exact (L.C.P.pb 0).ne_bot this
  exact ⟨⟨W, hW, hne⟩, (hL.Pg _).2 ⟨0, HeightOneSpectrum.ext hWQ.over.symm⟩⟩

theorem two_not_mem {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (t : T0) (PP : Formalism.L2.DIV.Pl D.host.E)
    (h : PP ∈ L.Pg ∨ PP ∈ L.Q t) : (2 : 𝓞 D.host.E) ∉ PP.asIdeal := by
  rcases h with hm | hm
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 hm
    have hgk := GlobalTheory.LevelPlaces.mem_of_div _ k PP hk
    have hn := GlobalTheory.LevelPlaces.not_mem_of_prime PP.isPrime.ne_top Nat.prime_two (D.host.g_prime k)
      (Formalism.L2.Pj.g_ne_two D k) hgk
    simpa using hn
  · intro h2
    apply (hL.Q_off t PP hm).1
    push_cast
    have hQS : ((D.host.QS : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      obtain ⟨c, hc⟩ := D.host.two_dvd_QS
      rw [hc]
      push_cast
      exact Ideal.mul_mem_right _ _ h2
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hQS))

theorem mem_levG {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i))
    (hk : k ∈ GfC (Wc D i)) (hS : Lev.finE (Wc D i) k ∈ Formalism.L2.DIV.St (L.βW i))
    (hr : ∀ PP ∈ L.Pg, Formalism.L2.DIV.redFn (L.βW i) PP (Lev.finE (Wc D i) k) = 1) :
    k ∈ Lev.levG (Wc D i) (L.βW i) (L.datWp i L.triv) := by
  refine Subgroup.mem_inf.2 ⟨hk, ?_⟩
  show Lev.finE (Wc D i) k ∈ Formalism.L2.DIV.lev D.sp.cm (Wc D i).gram (L.βW i) (L.datWp i L.triv)
  refine GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm (Wc D i).gram (L.βW i) (L.datWp i L.triv) _
    (GlobalTheory.LevSplit.finE_mem_UA _ k) hS (fun PP hP => ?_)
  rcases hP with hP | hP
  · exact hr PP hP
  · exact absurd hP (Finset.notMem_empty _)

theorem places_level : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → L.Pg.Nonempty ∧ (∀ t PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) ∧ ∀ (i : Fin D.R.m) (k : GA D (Wc D i)), k ∈ GfC (Wc D i) → Lev.finE (Wc D i) k ∈ Formalism.L2.DIV.St (L.βW i) → (∀ PP ∈ L.Pg, Formalism.L2.DIV.redFn (L.βW i) PP (Lev.finE (Wc D i) k) = 1) → k ∈ Lev.levG (Wc D i) (L.βW i) (L.datWp i L.triv) ∧ Lev.levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  intro D T0 L μ0 hL
  refine ⟨pg_nonempty hL, fun t PP h => two_not_mem hL t PP h, fun i k hk hS hr => ⟨mem_levG L i k hk hS hr, ?_⟩⟩
  exact GlobalTheory.HolRead.PrincLevelSub.levChi_triv L i k

end GlobalTheory.SpanPlaces
