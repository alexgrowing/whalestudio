import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairMembersMemSchwartzBruhat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices
open Filter Topology ValuativeRel GlobalTheory.StdPairSB GlobalTheory.StdPairCone

private theorem gfun_lc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ν : kˣ →* ℂˣ} {ϖ : kˣ} {n : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ n ν) (c m r : ℕ) :
    IsLocallyConstant
      (fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k => gfun ν ϖ c q.1 q.2) := by
  have h0 : ∀ e : ℕ, ∀ i j, (0 : Matrix (Fin m) (Fin r) k) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ e) := by
    intro e i j
    rw [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq]
    simp
  have hfac : ∀ (A : Matrix (Fin m) (Fin m) k) (B : Matrix (Fin m) (Fin r) k),
      gfun ν ϖ c A B = if (∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) then
        gfun ν ϖ n A (0 : Matrix (Fin m) (Fin r) k) else 0 := by
    intro A B
    by_cases hB : ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
    · rw [if_pos hB]
      unfold gfun
      by_cases hA : A.det ≠ 0 ∧ IsGLO A
      · rw [dif_pos ⟨hA.1, hA.2, hB⟩, dif_pos ⟨hA.1, hA.2, h0 n⟩]
      · rw [dif_neg fun h => hA ⟨h.1, h.2.1⟩, dif_neg fun h => hA ⟨h.1, h.2.1⟩]
    · rw [if_neg hB]
      unfold gfun
      rw [dif_neg fun h => hB h.2.2]
  have h1 : IsLocallyConstant
      (fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k =>
        gfun ν ϖ n q.1 (0 : Matrix (Fin m) (Fin r) k)) :=
    (isLocallyConstant_gfun hϖ hν m r).comp_continuous
      (f := fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k =>
        (q.1, (0 : Matrix (Fin m) (Fin r) k))) (continuous_fst.prodMk continuous_const)
  rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
  rintro ⟨A, B⟩
  have hnh : ∀ x : k, ∀ᶠ y in 𝓝 x, valuation k (y - x) ≤ valuation k ((ϖ ^ c : kˣ) : k) := by
    intro x
    have ht : Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 0) := by
      simpa using (tendsto_id.sub_const x : Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 (x - x)))
    exact ht (GlobalTheory.SplitWeil.cball_mem_nhds (ϖ ^ c))
  have hev : ∀ᶠ q in 𝓝 (A, B),
      ∀ i j, valuation k ((q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k).2 i j - B i j) ≤
        valuation k ((ϖ ^ c : kˣ) : k) := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    exact ((continuous_snd.matrix_elem i j).tendsto (A, B)).eventually (hnh (B i j))
  filter_upwards [hev, h1 (A, B)] with q hq hq1
  have hiff : (∀ i j, q.2 i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) ↔
      ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    constructor
    · intro h i j
      rw [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, ← sub_sub_cancel (q.2 i j) (B i j)]
      exact Valuation.map_sub_le _ (h i j) (hq i j)
    · intro h i j
      rw [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, ← sub_add_cancel (q.2 i j) (B i j)]
      exact Valuation.map_add_le _ (hq i j) (h i j)
  show gfun ν ϖ c q.1 q.2 = gfun ν ϖ c A B
  rw [hfac, hfac]
  exact if_congr hiff hq1 rfl

private theorem finiteRing_sq_sub_mul_sq_eq_of_card {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) {n : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ n ν) (c a a' : ℕ) :
    stdA ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧
      stdB ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc1 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₁ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.castAdd a' j)
  have hc2 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₂ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.natAdd a j)
  have hK : ∀ m : ℕ, IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin (a + a') => (𝒪[k] : Set k) :
      Set (Matrix (Fin m) (Fin (a + a')) k)) :=
    fun m => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int k
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : stdA ν ϖ c a a' = (fun q => gfun ν ϖ c q.1 q.2) ∘ fun X => (blk₁ X, blk₂ X) := rfl
    rw [this]
    exact (gfun_lc hϖ hν c a a').comp_continuous ((hc1 a).prodMk (hc2 a))
  · refine HasCompactSupport.intro (hK a) fun X hX => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := integral_of_ne (A := blk₁ X) (B := blk₂ X) hϖ hne
    exact hX fun i _ j _ => Fin.addCases (motive := fun j => X i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
  · have : stdB ν ϖ c a a' = (fun q => gfun ν ϖ c q.1 q.2) ∘ fun Y => (blk₂ Y, blk₁ Y) := rfl
    rw [this]
    exact (gfun_lc hϖ hν c a' a).comp_continuous ((hc2 a').prodMk (hc1 a'))
  · refine HasCompactSupport.intro (hK a') fun Y hY => ?_
    by_contra hne
    obtain ⟨h2, h1⟩ := integral_of_ne (A := blk₂ Y) (B := blk₁ Y) hϖ hne
    exact hY fun i _ j _ => Fin.addCases (motive := fun j => Y i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j

end SlopeTestRemainingChoices

theorem UpperTheory.stdA_stdB_mem_schwartzBruhat :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∃ m, GlobalTheory.SplitFlip.CondLE ϖ m ν) → ∀ c a a' : ℕ,
        GlobalTheory.StdPairCone.stdA ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧
        GlobalTheory.StdPairCone.stdB ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) := by
  intro k _ _ _ _ ν ϖ hϖ hν c a a'
  obtain ⟨n, hn⟩ := hν
  exact finiteRing_sq_sub_mul_sq_eq_of_card ν ϖ hϖ hn c a a'
