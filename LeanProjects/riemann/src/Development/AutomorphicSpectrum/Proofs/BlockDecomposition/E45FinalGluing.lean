import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSlicesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairRestrictionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairFiniteDimensionalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceTypeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairFirstStepStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSecondStepStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HullGenerationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapacityEquivalenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscreteInfimumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopologicalInfimumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfimumOfEqualityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeafBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceStripStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceShiftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceCompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceInfimumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorInductionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleGluingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitListsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTreesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdCloseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorLimitStatement

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem eFinalGlue_of (hCS : ConvStrip) (hCC : ConvComp) (hFS : FactorStep) (hLL : LimLists) (hOS : OneStep)
    (hFL : FactorLim) (hMC : MCloseFacts) (hPE : PairEmb) (hPS : PairSlices) (hST : SliceType) : InfinitesimalCharacterGlue := by
  intro hE3 hSep hLim hGraft hTw hTr hLV hAD hUn hInf E _ _ _ a b W₁ W₂ hW₁ hW₂
  obtain ⟨Ωs₁, hΩs₁, S₁⟩ := hFS hSep E a W₁ hW₁
  obtain ⟨Ωs₂, hΩs₂, S₂⟩ := hFS hSep E b W₂ hW₂
  obtain ⟨Ωf₁, hΩf₁, X₁⟩ := hLL hLim hTw E a Ωs₁ hΩs₁
  obtain ⟨Ωf₂, hΩf₂, X₂⟩ := hLL hLim hTw E b Ωs₂ hΩs₂
  refine ⟨Ωf₁, Ωf₂, hΩf₁, hΩf₂, fun K₁ K₂ hK₁ hK₂ => ?_⟩
  obtain ⟨Θs₁, hΘs₁, F₁⟩ := S₁ K₁ hK₁
  obtain ⟨Θs₂, hΘs₂, F₂⟩ := S₂ K₂ hK₂
  obtain ⟨Θf₁, hΘf₁, P₁⟩ := X₁ Θs₁ hΘs₁
  obtain ⟨Θf₂, hΘf₂, P₂⟩ := X₂ Θs₂ hΘs₂
  refine ⟨Θf₁, Θf₂, hΘf₁, hΘf₂, ?_⟩
  intro D ι _ M m₁ m₂ n₁ n₂ C lam lam₀ f hC hRep hcont hne hL hWL hTy hs1 hs2 ha1 ha2 hi1 hi2 heig hconv hR1 hR2 hgap hlam
  have hfar : ∀ᶠ k in atTop, ∀ τ, MClose (1 / 8) (m₁ k τ) (n₁ τ) ∧ MClose (1 / 8) (m₂ k τ) (n₂ τ) :=
    Filter.eventually_all.2 fun τ => hconv τ (1 / 8) (by norm_num)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hfar
  have h3 := fun k => hE3 E a b D ι M (f k) K₁ K₂ W₁ W₂ (m₁ k) (m₂ k) hK₁ hK₂ hW₁ hW₂ (hcont k) (hL k) (hWL k)
    (hTy k) (hs1 k) (hs2 k) (ha1 k) (ha2 k) (hi1 k) (hi2 k)
  have hone := fun k => hOS E a b ι K₁ K₂ W₁ W₂ Θs₁ Θs₂ Ωs₁ Ωs₂ (f (k + k₀)) (m₁ (k + k₀)) (m₂ (k + k₀)) hW₁ hW₂ F₁ F₂
    (hne _) (hTy _) (hs1 _) (hs2 _) (h3 _).2.2.1 (h3 _).2.2.2.1 (h3 _).2.2.2.2.1 (h3 _).2.2.2.2.2.1
    (h3 _).2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.2.2.1
    (fun τ => hMC.2.1 (1 / 8) _ _ (by norm_num) (hk₀ (k + k₀) (by omega) τ).1 (hgap τ).1)
    (fun τ => hMC.2.1 (1 / 8) _ _ (by norm_num) (hk₀ (k + k₀) (by omega) τ).2 (hgap τ).2)
    (h3 _).2.2.2.2.2.2.2.2.2.2
  choose t₁ t₂ G ψ₁ ψ₂ hr₁ hr₂ hg₁ hg₂ hl₁ hl₂ hG0 hGm hGt hGe hp₁ hp₁0 hc₁ hp₂ hp₂0 hc₂ using hone
  have hB : ∀ n : (E →+* ℂ) → Multiset ℂ, ∃ B : ℝ, ∀ τ, ∀ y ∈ n τ, ‖y‖ ≤ B := fun n => by
    classical
    obtain ⟨B, hB⟩ := ((Finset.univ.biUnion fun τ => (n τ).toFinset).image norm).finite_toSet.bddAbove
    refine ⟨B, fun τ y hy => hB ?_⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Multiset.mem_toFinset]
    exact ⟨y, ⟨τ, hy⟩, rfl⟩
  obtain ⟨B₁, hB₁⟩ := hB n₁
  obtain ⟨B₂, hB₂⟩ := hB n₂
  obtain ⟨φ₁, t₁', s₁, hφ₁, hC₁, hs₁R, hs₁G, hs₁L, hD₁, hI₁, hE₁⟩ := hFL hTr hGraft hInf E Θs₁ Θf₁ Ωs₁ Ωf₁ a t₁ ψ₁
    (fun k => m₁ (k + k₀)) n₁ (B₁ + 1 / 8) P₁ hRep hr₁ hg₁ hl₁ hp₁ hp₁0 hc₁
    (fun k τ => hMC.1 _ _ _ _ (hk₀ (k + k₀) (by omega) τ).1 (hB₁ τ))
    (fun τ ε hε => ((tendsto_add_atTop_nat k₀).eventually (hconv τ ε hε)).mono fun _ h => h.1)
  obtain ⟨φ₂, t₂', s₂, hφ₂, hC₂, hs₂R, hs₂G, hs₂L, hD₂, hI₂, hE₂⟩ := hFL hTr hGraft hInf E Θs₂ Θf₂ Ωs₂ Ωf₂ b
    (fun k => t₂ (φ₁ k)) (fun k => ψ₂ (φ₁ k))
    (fun k => m₂ (φ₁ k + k₀)) n₂ (B₂ + 1 / 8) P₂ hRep (fun k => hr₂ _) (fun k => hg₂ _) (fun k => hl₂ _)
    (fun k => hp₂ _) (fun k => hp₂0 _) (fun k => hc₂ _)
    (fun k τ => hMC.1 _ _ _ _ (hk₀ (φ₁ k + k₀) (by omega) τ).2 (hB₂ τ))
    (fun τ ε hε => (((tendsto_add_atTop_nat k₀).comp hφ₁.tendsto_atTop).eventually (hconv τ ε hε)).mono fun _ h => h.2)
  have hstab : ∀ {N : ℕ} {t : Tr E N}, t.Good → IsStable t.space := fun h => hTr E _ _ (disc_stable (good_disc h))
  have hG' := fun k => hPE E a b ι K₁ K₂ W₁ W₂ (t₁ (φ₁ (φ₂ k))).space (t₁' (φ₂ k)).space (t₂ (φ₁ (φ₂ k))).space (t₂' k).space
    (G (φ₁ (φ₂ k))) hW₁ hW₂ (hstab (hg₁ _)) (hstab (hg₂ _)) (hE₁ _) (hE₂ _) (hG0 _) (hGm _) (hGt _)
  choose G' hG'0 hG'm hG't hG'e using hG'
  have hCC₁ := (hCS E a _ _).1 (hCC E a _ _ φ₂ hC₁ hφ₂)
  have hCC₂ := (hCS E b _ _).1 hC₂
  obtain ⟨F, hF0, hFm, hFt, hFe⟩ := hLV hAD E a b ι (fun k => t₁' (φ₂ k)) t₂' s₁ s₂ K₁ K₂ W₁ W₂ C
    (fun k => lam (φ₁ (φ₂ k) + k₀)) lam₀ G' hK₁ hK₂ hW₁ hW₂ hC hs₁G hs₂G (fun k => hD₁ _) hD₂ hCC₁.1 hCC₂.1 hCC₁.2 hCC₂.2
    hG'0 hG'm hG't (fun k h hh => hG'e k h _ (hGe _ h _ (heig _ h hh)))
    (fun h hh => (hlam h hh).comp ((tendsto_add_atTop_nat k₀).comp (hφ₁.comp hφ₂).tendsto_atTop))
  obtain ⟨i, hi⟩ : ∃ i, F i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hF0 (funext hcon)
  obtain ⟨x, hx⟩ : ∃ x, F i x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hi (funext hcon)
  have hsl := hPS E a b _ _ (F i) (hFm i)
  have hn₁ : sl₁ (F i) x.2 ≠ 0 := fun h => hx (by
    have := congrFun (hsl.1 x.2).2 x.1
    rw [h] at this
    exact this.symm)
  have hn₂ : sl₂ (F i) x.1 ≠ 0 := fun h => hx (by
    have := congrFun (hsl.2 x.1).2 x.2
    rw [h] at this
    exact this.symm)
  have hb₁ : s₁.space ≠ ⊥ := fun h => hn₁ (by simpa [h] using (hsl.1 x.2).1)
  have hb₂ : s₂.space ≠ ⊥ := fun h => hn₂ (by simpa [h] using (hsl.2 x.1).1)
  exact ⟨s₁, s₂, F, hs₁G, hs₂G, hUn E a s₁ n₁ hs₁G hb₁ hI₁ hR1, hUn E b s₂ n₂ hs₂G hb₂ hI₂ hR2, hs₁L, hs₂L,
    hI₁, hI₂, hF0, hFm, hFt, hFe⟩

theorem eFinalGlue : PositivityTheory.Rg.BcB.SpectralAccumulation.InfinitesimalCharacterGlue :=
  have hPS := GlobalTheory.T.pair_slices
  have hP1 := GlobalTheory.T.pair_first_step hPS
  have hP2 := GlobalTheory.T.pair_second_step hPS
  have hCE := GlobalTheory.T.capacity_equivalence
  have hDI := GlobalTheory.T.discrete_infimum
  have hTI := GlobalTheory.T.topological_infimum
  have hIE := GlobalTheory.T.infimum_of_equality
  have hCS := GlobalTheory.T.convergence_strip
  have hCC := GlobalTheory.T.convergence_composition
  have hMC := GlobalTheory.T.closure_facts_alt
  eFinalGlue_of hCS hCC GlobalTheory.T.factor_induction (GlobalTheory.T.limit_lists hCS GlobalTheory.T.convergence_shift hCC)
    (GlobalTheory.T.single_gluing hPS GlobalTheory.T.pair_restriction GlobalTheory.T.pair_finite_dimensional GlobalTheory.T.slice_type hP1 hP2 GlobalTheory.T.hull_generation hCE)
    (GlobalTheory.T.factor_limit hCC (GlobalTheory.T.limit_trees hCC) (GlobalTheory.T.leaf_bound_alt hDI hTI hIE) (GlobalTheory.T.convergence_infimum hDI hTI) hIE hCE hMC)
    hMC (GlobalTheory.T.pair_embedding hPS hP1 hP2) hPS GlobalTheory.T.slice_type

end GlobalTheory.CompanionTheory.EGlue

end
