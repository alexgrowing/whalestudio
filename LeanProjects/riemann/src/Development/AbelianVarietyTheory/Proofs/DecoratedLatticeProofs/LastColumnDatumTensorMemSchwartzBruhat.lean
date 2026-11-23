import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialFourierInversion
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocFlat.CFac
open scoped Topology

noncomputable section
namespace GlobalTheory.LocFlat.LastColumn

def colJoin (n n' k : Type) [TopologicalSpace k] : Matrix n n' k × (n → k) ≃ₜ Matrix n (n' ⊕ Unit) k where
  toFun p := fromCols p.1 (Matrix.of fun r _ => p.2 r)
  invFun M := (M.toCols₁, fun r => M r (Sum.inr ()))
  left_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ ?_
    · ext r j; simp [toCols₁]
    · funext r; simp
  right_inv M := by
    ext r (j | u)
    · simp [toCols₁]
    · cases u; simp
  continuous_toFun := by
    refine continuous_matrix fun r j => ?_
    cases j with
    | inl j => simpa using continuous_fst.matrix_elem r j
    | inr u => simpa using (by fun_prop : Continuous fun a : Matrix n n' k × (n → k) => a.2 r)
  continuous_invFun := by
    refine Continuous.prodMk (continuous_matrix fun r j => ?_) (continuous_pi fun r => ?_)
    · simpa [toCols₁] using continuous_id.matrix_elem r (Sum.inl j)
    · exact continuous_id.matrix_elem r (Sum.inr ())

def colSplit (n n' k : Type) [TopologicalSpace k] :
    Matrix n (n' ⊕ Unit) k ≃ₜ Matrix n n' k × Matrix n Unit k where
  toFun x := (x.toCols₁, Matrix.of fun r _ => x r (Sum.inr ()))
  invFun p := fromCols p.1 p.2
  left_inv x := by
    ext r (j | u)
    · simp [toCols₁]
    · cases u; simp
  right_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ ?_
    · ext r j; simp [toCols₁]
    · ext r u; cases u; simp
  continuous_toFun := by
    refine Continuous.prodMk (continuous_matrix fun r j => ?_) (continuous_matrix fun r u => ?_)
    · simpa [toCols₁] using continuous_id.matrix_elem r (Sum.inl j)
    · simpa using continuous_id.matrix_elem r (Sum.inr ())
  continuous_invFun := by
    refine continuous_matrix fun r j => ?_
    cases j with
    | inl j => simpa using continuous_fst.matrix_elem r j
    | inr u => simpa using continuous_snd.matrix_elem r u

def rowSplit (n n' Z k : Type) [TopologicalSpace k] :
    Matrix n n' k × Matrix (Z ⊕ Unit) n k ≃ₜ (Matrix n n' k × (n → k)) × Matrix Z n k where
  toFun q := ((q.1, q.2 (Sum.inr ())), q.2.toRows₁)
  invFun p := (p.1.1, fromRows p.2 (Matrix.of fun _ => p.1.2))
  left_inv q := by
    obtain ⟨x, M⟩ := q
    refine Prod.ext rfl ?_
    ext (i | u) j
    · simp [toRows₁]
    · cases u; simp
  right_inv p := by
    obtain ⟨⟨x, y⟩, A⟩ := p
    refine Prod.ext (Prod.ext rfl ?_) ?_
    · funext j; simp
    · ext i j; simp [toRows₁]
  continuous_toFun := by
    refine Continuous.prodMk (Continuous.prodMk continuous_fst (continuous_pi fun j => ?_))
      (continuous_matrix fun i j => ?_)
    · exact continuous_snd.matrix_elem (Sum.inr ()) j
    · simpa [toRows₁] using continuous_snd.matrix_elem (Sum.inl i) j
  continuous_invFun := by
    refine Continuous.prodMk (continuous_fst.comp continuous_fst) (continuous_matrix fun i j => ?_)
    cases i with
    | inl i => simpa using continuous_snd.matrix_elem i j
    | inr u => simpa using (by fun_prop : Continuous fun a : (Matrix n n' k × (n → k)) × Matrix Z n k => a.1.2 j)

theorem isLocallyConstant_integral {Q Y : Type} [TopologicalSpace Q] [TopologicalSpace Y] [MeasurableSpace Y]
    (μ : Measure Y) {H : Q × Y → ℂ} (hH : IsLocallyConstant H) {K : Set Y} (hK : IsCompact K)
    (hz : ∀ q, ∀ y ∉ K, H (q, y) = 0) : IsLocallyConstant fun q => ∫ y, H (q, y) ∂μ := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun q₀ => ?_
  have h1 : ∀ᶠ q in 𝓝 q₀, ∀ y ∈ K, H (q, y) = H (q₀, y) := by
    refine IsCompact.eventually_forall_of_forall_eventually hK fun y _ => ?_
    have h2 : IsLocallyConstant fun p : Q × Y => (H p, H (q₀, p.2)) :=
      hH.prodMk (hH.comp_continuous (by fun_prop))
    filter_upwards [h2.eventually_eq (q₀, y)] with p hp
    simp only [Prod.mk.injEq] at hp
    exact hp.1.trans hp.2.symm
  filter_upwards [h1] with q hq
  congr 1
  funext y
  by_cases hy : y ∈ K
  · exact hq y hy
  · rw [hz q y hy, hz q₀ y hy]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem hatCol_mem_SB (ψ : AddChar k Circle) (hψ : Continuous ψ) (hne : ψ ≠ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] {n n' : Type} [Fintype n] [DecidableEq n]
    {Ψ : Matrix n (n' ⊕ Unit) k → ℂ} (hΨ : Ψ ∈ SB (Matrix n (n' ⊕ Unit) k)) :
    (fun p : Matrix n n' k × (n → k) =>
      GlobalTheory.StepData.hat ψ ν (-1) (fun y => Ψ (fromCols p.1 (Matrix.of fun r _ => y r))) p.2) ∈
      SB (Matrix n n' k × (n → k)) := by
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ hne
  set f : Matrix n n' k × (n → k) → ℂ := fun p => Ψ (colJoin n n' k p) with hfdef
  have hf : f ∈ SB (Matrix n n' k × (n → k)) :=
    ⟨hΨ.1.comp_continuous (colJoin n n' k).continuous, hΨ.2.comp_homeomorph _⟩
  obtain ⟨s, hs⟩ : ∃ s : kˣ, ∀ t ∈ FourierPi.box n s, ∀ x y, f (x, y + t) = f (x, y) := by
    have h1 := PartialFourier.eventually_add_invariant hf
    have h2 : Filter.Tendsto (fun t : n → k => ((0, t) : Matrix n n' k × (n → k))) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun t : n → k => ((0, t) : Matrix n n' k × (n → k))) := by fun_prop
      exact this.tendsto 0
    obtain ⟨s, hs⟩ := FourierPi.exists_box_subset (h2.eventually h1)
    exact ⟨s, fun t ht x y => by simpa using hs ht (x, y)⟩
  have hfun : (fun p : Matrix n n' k × (n → k) =>
      GlobalTheory.StepData.hat ψ ν (-1) (fun y => Ψ (fromCols p.1 (Matrix.of fun r _ => y r))) p.2) =
      fun p => ∫ y, f (p.1, y) * (ψ (y ⬝ᵥ (-p.2)) : ℂ) ∂(Measure.pi fun _ => ν) := by
    funext p
    simp only [GlobalTheory.StepData.hat]
    congr 1
    funext y
    rw [dotProduct_neg, dotProduct_comm, neg_one_mul]
    rfl
  rw [hfun]
  refine ⟨?_, ?_⟩
  · refine isLocallyConstant_integral _
      (H := fun q : (Matrix n n' k × (n → k)) × (n → k) => f (q.1.1, q.2) * (ψ (q.2 ⬝ᵥ (-q.1.2)) : ℂ))
      ?_ (hf.2.image continuous_snd) ?_
    · refine (hf.1.comp_continuous (by fun_prop)).mul ?_
      exact (hc.isLocallyConstant.comp_continuous
        (continuous_snd.dotProduct (continuous_snd.comp continuous_fst).neg)).comp (fun z : Circle => (z : ℂ))
    · intro q y hy
      have : f (q.1, y) = 0 := image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, h, rfl⟩
      simp [this]
  · refine HasCompactSupport.intro
      ((hf.2.image continuous_fst).prod (FourierPi.isCompact_box (n := n) (c * s⁻¹)).neg) fun p hp => ?_
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · have : ∀ y, f (p.1, y) = 0 := fun y => image_eq_zero_of_notMem_tsupport fun h => hp ⟨_, h, rfl⟩
      simp [this]
    · rw [Set.mem_neg] at hp
      exact FourierPi.fourier_eq_zero_pi _ hc (f := fun y => f (p.1, y)) (fun t ht y => hs t ht p.1 y) hp

theorem lastColumn_datum_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n n' Z : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype Z] [DecidableEq Z], (∀ (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ψ₂ : SB (Matrix Z n k)), ∃ Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k), ∀ q, Ξ.1 q = Ψ₂.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => Ψ₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) (q.2 (Sum.inr ()))) ∧ ∀ (Ξ₁ : SB (Matrix n n' k)) (c : SB (Matrix n Unit k)), ∃ Ψ₁ : SB (Matrix n (n' ⊕ Unit) k), ∀ x, Ψ₁.1 x = Ξ₁.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ())) := by
  intro k _ _ _ _ _ _ ν hν ψk hψ hne n n' Z _ _ _ _ _ _
  haveI := hν
  refine ⟨fun Ψ₁ Ψ₂ => ?_, fun Ξ₁ c => ?_⟩
  · let F : SB (Matrix n n' k × (n → k)) := ⟨_, hatCol_mem_SB ψk hψ hne ν Ψ₁.2⟩
    exact ⟨comapH (rowSplit n n' Z k) (prodSB F Ψ₂), fun q => mul_comm _ _⟩
  · exact ⟨comapH (colSplit n n' k) (prodSB Ξ₁ c), fun x => rfl⟩

end GlobalTheory.LocFlat.LastColumn
