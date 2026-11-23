import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqConjugateOfIsConjMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemConjChartSource
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsExphOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsExphOnUnion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsExphOfIsExphOnUniv
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

namespace GlobalTheory.ConjExph

theorem exists_isExph_of_cover (F : Type) [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ)
    (a : ChartForm Y.str σ Y.dim) (ha : IsKaehlerForm (Y.an σ) a) : ∃ E : ChartMap Y.str σ Y.dim, IsExph a E := by
  classical
  haveI : CompactSpace (CxPts Y.str σ) := CxPts.compactSpace σ Y.isProjOver
  haveI : T2Space (CxPts Y.str σ) := CxPts.t2Space_cxPts_of_isProjOver σ Y.isProjOver
  have hloc : ∀ y : CxPts Y.str σ, ∃ (c : AlgChart Y.str σ Y.dim) (E : ChartMap Y.str σ Y.dim)
      (W K : Set (CxPts Y.str σ)) (ε : ℝ), IsOpen W ∧ W ⊆ c.e.source ∧ IsCompact K ∧ K ∈ 𝓝 y ∧ K ⊆ W ∧ 0 < ε ∧
      ExphOn.IsExphOn a E W ε := fun y => by
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (p := Y.str) (σ := σ) (D := Y.dim) y
    obtain ⟨E, W, ε, hW, hy, hWc, hε, hE⟩ := GlobalTheory.ChernReg.ExphLoc.exists_isExphOn F _ Y.str σ Y.dim (Y.an σ) a ha c y hc
    obtain ⟨K, hK, hKW, hKc⟩ := local_compact_nhds (hW.mem_nhds hy)
    exact ⟨c, E, W, K, ε, hW, hWc, hKc, hK, hKW, hε, hE⟩
  choose c E W K ε hW hWc hKc hK hKW hε hE using hloc
  have hind : ∀ t : Finset (CxPts Y.str σ), ∃ (E' : ChartMap Y.str σ Y.dim) (W' : Set (CxPts Y.str σ)) (ε' : ℝ),
      IsOpen W' ∧ (⋃ y ∈ t, K y) ⊆ W' ∧ 0 < ε' ∧ ExphOn.IsExphOn a E' W' ε' := fun t => by
    induction t using Finset.induction_on with
    | empty => exact ⟨_, ∅, 1, isOpen_empty, by simp, one_pos, ExphOn.isExphOn_empty a 1⟩
    | insert y t _ ih =>
      obtain ⟨E', W', ε', hW', hs, hε', hE'⟩ := ih
      obtain ⟨E'', W'', ε'', h1, h2, h3, h4⟩ := GlobalTheory.ChernReg.ExphOn.exists_isExphOn_union F _ Y.str σ Y.dim (Y.an σ) a ha
        (c y) E' (E y) W' (W y) (⋃ y ∈ t, K y) (K y) ε' (ε y) hW' (hW y) (hWc y)
        (t.isCompact_biUnion fun z _ => hKc z) (hKc y) hs (hKW y) hε' (hε y) hE' (hE y)
      refine ⟨E'', W'', ε'', h1, ?_, h3, h4⟩
      rwa [Finset.set_biUnion_insert, Set.union_comm]
  obtain ⟨t, -, ht⟩ := (isCompact_univ (X := CxPts Y.str σ)).elim_nhds_subcover K fun y _ => hK y
  obtain ⟨E', W', ε', -, hs, hε', hE'⟩ := hind t
  exact GlobalTheory.ChernReg.ExphOn.exists_isExph_of_isExphOn_univ F _ Y.str σ Y.dim (Y.an σ) a E' ε' ha hε'
    (hE'.mono (ht.trans hs) le_rfl)

theorem exists_exph_conjComm : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (Y : Var F) (a : ∀ σ, ChartForm Y.str σ Y.dim), (∀ σ, IsKaehlerForm (Y.an σ) (a σ)) → (∀ σ σ' (ι : Pts Y σ' → Pts Y σ), IsConjMap ι → (∀ W φ, IsPotential (Y.an σ) (a σ) W φ → IsPotential (Y.an σ') (a σ') (ι ⁻¹' W) (φ ∘ ι))) → ∃ E : ∀ σ, ChartMap Y.str σ Y.dim, (∀ σ, IsExph (a σ) (E σ)) ∧ ∀ σ σ' (ι : Pts Y σ' → Pts Y σ), IsConjMap ι → ConjComm ι (E σ) (E σ') := by
  intro F _ _ _ Y a ha hpot
  classical
  have hne : ∀ σ : F →+* ℂ, ComplexEmbedding.conjugate σ ≠ σ := fun σ h =>
    (InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex (InfinitePlace.mk σ))) (ComplexEmbedding.isReal_iff.2 h)
  choose E₀ hE₀ using fun σ => exists_isExph_of_cover F Y σ (a σ) (ha σ)
  let τ : (F →+* ℂ) → (F →+* ℂ) := fun σ => (InfinitePlace.mk σ).embedding
  have hτ : ∀ σ, σ ≠ τ σ → τ σ = ComplexEmbedding.conjugate σ := fun σ h =>
    (InfinitePlace.embedding_mk_eq σ).resolve_left (Ne.symm h)
  have hτc : ∀ σ, τ (ComplexEmbedding.conjugate σ) = τ σ := fun σ => by
    simp only [τ, InfinitePlace.mk_conjugate_eq]
  let ι₀ : ∀ σ, σ ≠ τ σ → Pts Y σ → Pts Y (τ σ) := fun σ h => (exists_isConjMap Y (hτ σ h)).choose
  have hι₀ : ∀ σ h, IsConjMap (ι₀ σ h) := fun σ h => (exists_isConjMap Y (hτ σ h)).choose_spec
  have hE' : ∀ σ (h : σ ≠ τ σ), ∃ E' : ChartMap Y.str σ Y.dim, IsExph (a σ) E' ∧ ConjComm (ι₀ σ h) (E₀ (τ σ)) E' ∧
      ∀ ι' : Pts Y (τ σ) → Pts Y σ, IsConjMap ι' → ConjComm ι' E' (E₀ (τ σ)) := fun σ h =>
    GlobalTheory.ConjExph.exists_conj_exph F Y (τ σ) σ (ι₀ σ h) (a (τ σ)) (a σ) (E₀ (τ σ)) (hι₀ σ h) (ha _) (ha _)
      (hpot _ _ _ (hι₀ σ h)) (hE₀ _)
  choose E₁ hE₁ using hE'
  let E : ∀ σ, ChartMap Y.str σ Y.dim := fun σ => if h : σ = τ σ then E₀ σ else E₁ σ h
  refine ⟨E, fun σ => ?_, fun σ σ' ι hι => ?_⟩
  · by_cases h : σ = τ σ
    · simp only [E, dif_pos h]; exact hE₀ σ
    · simp only [E, dif_neg h]; exact (hE₁ σ h).1
  · by_cases hz : Nonempty (Pts Y σ')
    swap
    · intro c c' _ z
      exact (hz ⟨z⟩).elim
    obtain ⟨z⟩ := hz
    have hσ := eq_conjugate_of_isConjMap Y hι z
    have hσ' : σ' = ComplexEmbedding.conjugate σ := by rw [hσ, conjugate_conjugate]
    have hττ : τ σ' = τ σ := by rw [hσ', hτc]
    by_cases h : σ = τ σ
    · have h' : σ' ≠ τ σ' := by
        rw [hττ, ← h, hσ']; exact hne σ
      simp only [E, dif_pos h, dif_neg h']
      have key := (hE₁ σ' h').2.1
      have gen : ∀ (ρ : F →+* ℂ) (hρ : ρ = σ) (j : Pts Y σ' → Pts Y ρ), IsConjMap j →
          ConjComm j (E₀ ρ) (E₁ σ' h') → ConjComm ι (E₀ σ) (E₁ σ' h') := by
        rintro ρ rfl j hj hc
        rwa [isConjMap_unique Y hι hj]
      exact gen (τ σ') (hττ.trans h.symm) _ (hι₀ σ' h') key
    · have h' : σ' = τ σ' := by rw [hττ, hτ σ h, hσ']
      simp only [E, dif_neg h, dif_pos h']
      have key := (hE₁ σ h).2.2
      have gen : ∀ (ρ : F →+* ℂ) (hρ : ρ = σ'),
          (∀ ι' : Pts Y ρ → Pts Y σ, IsConjMap ι' → ConjComm ι' (E₁ σ h) (E₀ ρ)) →
          ConjComm ι (E₁ σ h) (E₀ σ') := by
        rintro ρ rfl hc
        exact hc ι hι
      exact gen (τ σ) (by rw [← hττ, ← h']) key

end GlobalTheory.ConjExph
