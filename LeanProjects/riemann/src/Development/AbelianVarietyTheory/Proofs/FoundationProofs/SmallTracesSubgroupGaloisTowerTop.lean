import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationTowerZetaSubOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfCosetRepresentativeTraceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationAlmostEtaleTowerFixerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleSubgroupOfStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerCosetRepresentativeTraceEqOfLtOneStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

theorem small_traces_subgroup : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (H : Subgroup (Gal p Ω)), H ≤ ⨅ n, Gn T n →
    ∀ (S : Finset Ω) (j : ℕ), 1 ≤ j → ∃ (y : Ω) (E : Finset (Gal p Ω)), IsInt p y ∧
      (∀ g ∈ E, g ∈ H) ∧ (∀ h ∈ H, ∃! g, g ∈ E ∧ h y = g y ∧ ∀ s ∈ S, h s = g s) ∧
      ∑ g ∈ E, g y = T.ζ j - 1 := by
  intro p _ Ω _ _ hp2 hclo T H hH S j hj
  classical
  obtain ⟨v, hvint, hvgal, -, hv1, hsep⟩ := GlobalTheory.T.exists_valuation_almostEtale_towerFixer p Ω hp2 hclo T
  obtain ⟨U, -, hUfin, hUS, hUsep⟩ := hsep S
  let K : Subgroup (Gal p Ω) := ⨅ n, Gn T n
  let H' : Subgroup ↥K := H.subgroupOf K
  let U' : Subgroup ↥H' := U.subgroupOf H'
  haveI : U'.FiniteIndex := inferInstance
  haveI : Finite (↥H' ⧸ U') := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (↥H' ⧸ U') := Fintype.ofFinite _
  have hU'sep : AlmostSep v U' := GlobalTheory.T.fixedFieldAlmostEtale_subgroupOf Ω v ↥K U H' hUsep
  have hsmul : ∀ (h : ↥H') (x : Ω), h • x = ((h : ↥K) : Gal p Ω) x := fun _ _ => rfl
  have hinv : ∀ (h : ↥H') (x : Ω), v (h • x) = v x := fun h x => by rw [hsmul]; exact hvgal _ x
  have hfixζ : ∀ h : ↥H', h • (T.ζ j - 1) = T.ζ j - 1 := by
    intro h
    have hm : ((h : ↥K) : Gal p Ω) ∈ Gn T j := (Subgroup.mem_iInf.mp (h : ↥K).2) j
    have h1 : ((h : ↥K) : Gal p Ω) (T.ζ j) = T.ζ j := ((Basic.mem_gn T j _).mp hm).1
    rw [hsmul, map_sub, map_one, h1]
  have hve : v (T.ζ j - 1) < 1 := (GlobalTheory.T.valuation_tower_zeta_sub_one p Ω hp2 T v hv1 j hj).1
  obtain ⟨y₀, hy₀, hy₀le, htr⟩ := GlobalTheory.T.exists_integer_cosetRepresentativeTrace_eq_of_lt_one Ω v ↥H' hinv U' hU'sep (T.ζ j - 1) hfixζ hve
  have hS : ∀ s ∈ S, s ∈ Fix Ω U' := fun s hs g =>
    hUS s hs ⟨((g : ↥H') : ↥K), Subgroup.mem_subgroupOf.mp g.2⟩
  obtain ⟨y, D, E', hy, huniq, hsum⟩ := GlobalTheory.T.exists_reps_of_cosetRepresentativeTrace Ω ↥H' U' S hS y₀ hy₀
  let ι : ↥H' ↪ Gal p Ω := ⟨fun h => ((h : ↥K) : Gal p Ω), fun a b hab => Subtype.ext (Subtype.ext hab)⟩
  have hιH : ∀ h : ↥H', ι h ∈ H := fun h => Subgroup.mem_subgroupOf.mp h.2
  have hιs : ∀ (h : ↥H') (x : Ω), ι h x = h • x := fun _ _ => rfl
  have hy₀int : IsInt p y₀ := (hvint y₀).mp hy₀le
  refine ⟨y, E'.map ι, ?_, ?_, ?_, ?_⟩
  · rw [hy]
    exact IsIntegral.sum _ fun d _ => by rw [← hιs]; exact Basic.isInt_gal _ hy₀int
  · intro g hg
    obtain ⟨g', -, rfl⟩ := Finset.mem_map.mp hg
    exact hιH g'
  · intro h hh
    let h' : ↥H' := ⟨⟨h, hH hh⟩, Subgroup.mem_subgroupOf.mpr hh⟩
    obtain ⟨g', ⟨hg'E, hg'y, hg'S⟩, hg'u⟩ := huniq h'
    refine ⟨ι g', ⟨Finset.mem_map_of_mem ι hg'E, ?_, ?_⟩, ?_⟩
    · rw [hιs]; exact hg'y
    · intro s hs; rw [hιs]; exact hg'S s hs
    · rintro g ⟨hgE, hgy, hgS⟩
      obtain ⟨g'', hg''E, rfl⟩ := Finset.mem_map.mp hgE
      congr 1
      refine hg'u g'' ⟨hg''E, ?_, ?_⟩
      · rw [← hιs]; exact hgy
      · intro s hs; rw [← hιs]; exact hgS s hs
  · rw [Finset.sum_map]
    exact (Finset.sum_congr rfl fun g _ => hιs g y).trans (hsum.trans htr)

end GlobalTheory.K5
