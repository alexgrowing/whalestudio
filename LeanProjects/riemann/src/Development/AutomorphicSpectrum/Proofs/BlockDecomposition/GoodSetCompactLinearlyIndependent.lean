import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo

open GlobalTheory.CompanionTheory.WhitFree.AvgInf

variable {K W : Type} [CommRing K] [TopologicalSpace K] [Fintype W]

lemma cont_coord (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) {n M : ℕ} (b : Fin n) (i : Fin M) (w : W) :
    Continuous fun X : Fin n → Fin M → K => κ (X b i) w :=
  (continuous_apply w).comp (hκ.continuous.comp ((continuous_apply i).comp (continuous_apply b)))

lemma isOpen_nearK (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) {n M : ℕ} (w : W) (s : Fin n → ℂ) (ε : ℝ) :
    IsOpen (nearK (M := M) κ w s ε) := by
  have : nearK (M := M) κ w s ε = ⋂ i, {X | ‖∑ b, s b * κ (X b i) w‖ < ε} := by
    ext X; simp [nearK]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  refine isOpen_lt ?_ continuous_const
  refine Continuous.norm ?_
  refine continuous_finset_sum _ fun b _ => ?_
  exact continuous_const.mul (cont_coord κ hκ b i w)

lemma isCompact_boxK (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) {n M : ℕ} (r : Fin n → W → ℝ) :
    IsCompact (boxK (M := M) κ r) := by
  let e : K ≃ₜ (W → ℂ) := hκ.homeomorph κ
  let Φ : (Fin n → Fin M → K) ≃ₜ (Fin n → Fin M → W → ℂ) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => e
  have hB : IsCompact (Set.univ.pi fun a : Fin n => Set.univ.pi fun _ : Fin M =>
      Set.univ.pi fun w : W => Metric.closedBall (0 : ℂ) (r a w)) :=
    isCompact_univ_pi fun a => isCompact_univ_pi fun _ => isCompact_univ_pi fun w =>
      isCompact_closedBall _ _
  have : boxK (M := M) κ r = Φ ⁻¹' (Set.univ.pi fun a : Fin n => Set.univ.pi fun _ : Fin M =>
      Set.univ.pi fun w : W => Metric.closedBall (0 : ℂ) (r a w)) := by
    ext X
    simp [boxK, Φ, e]
  rw [this]
  exact (Homeomorph.isCompact_preimage Φ).2 hB

lemma linIndep_iff (κ : K ≃+* (W → ℂ)) {n M : ℕ} (X : Fin n → Fin M → K) :
    LinearIndependent K X ↔ ∀ w, LinearIndependent ℂ (fun b i => κ (X b i) w) := by
  classical
  constructor
  · intro hX w
    rw [Fintype.linearIndependent_iff] at hX ⊢
    intro t ht b
    have key := hX (fun b => κ.symm (Pi.single w (t b))) (by
      funext i
      apply κ.injective
      funext w'
      have := congrFun ht i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
        RingEquiv.apply_symm_apply, Pi.zero_apply, map_zero, Finset.sum_apply, Pi.mul_apply]
      by_cases h : w' = w
      · subst h; simpa using this
      · simp [Pi.single_apply, h])
    have := congrFun (congrArg κ (key b)) w
    simpa using this
  · intro h
    rw [Fintype.linearIndependent_iff]
    intro c hc b
    apply κ.injective
    funext w
    have hw := h w
    rw [Fintype.linearIndependent_iff] at hw
    have := hw (fun b => κ (c b) w) (by
      funext i
      have := congrArg (fun y => κ y w) (congrFun hc i)
      simpa [Finset.sum_apply, map_sum, map_mul] using this) b
    simpa using this

lemma isOpen_linIndep (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) (n M : ℕ) :
    IsOpen {X : Fin n → Fin M → K | LinearIndependent K X} := by
  have : {X : Fin n → Fin M → K | LinearIndependent K X} =
      ⋂ w, (fun X : Fin n → Fin M → K => fun b i => κ (X b i) w) ⁻¹'
        {Y : Fin n → Fin M → ℂ | LinearIndependent ℂ Y} := by
    ext X; simp [linIndep_iff κ X]
  rw [this]
  refine isOpen_iInter_of_finite fun w => ?_
  refine isOpen_setOfPred_linearIndependent.preimage ?_
  exact continuous_pi fun b => continuous_pi fun i => cont_coord κ hκ b i w

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo

open GlobalTheory.CompanionTheory.WhitFree.AvgInf

variable {K W : Type} [CommRing K] [TopologicalSpace K] [Fintype W]

lemma goodK_subset (κ : K ≃+* (W → ℂ)) {n M : ℕ} (R ε : ℝ) (hε : 0 < ε) :
    goodK (n := n) (M := M) κ R ε ⊆ {X : Fin n → Fin M → K | LinearIndependent K X} := by
  intro X hX
  rcases hX with ⟨-, hX⟩
  show LinearIndependent K X
  rw [Fintype.linearIndependent_iff]
  intro c hc b0
  by_contra h0
  have hk : κ (c b0) ≠ 0 := by
    intro h; exact h0 (κ.injective (by simpa using h))
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hk
  haveI : Nonempty (Fin n) := ⟨b0⟩
  obtain ⟨a, ha⟩ := Finite.exists_max fun b => ‖κ (c b) w‖
  have hca : κ (c a) w ≠ 0 := by
    intro h
    have := ha b0
    rw [h, norm_zero] at this
    exact hw (norm_le_zero_iff.1 this)
  have hsum : ∀ i, ∑ b, κ (c b) w * κ (X b i) w = 0 := by
    intro i
    have := congrArg (fun y => κ y w) (congrFun hc i)
    simpa [Finset.sum_apply, map_sum, map_mul] using this
  apply hX
  simp only [Set.mem_iUnion]
  refine ⟨w, a, fun b => κ (c b) w / κ (c a) w, ⟨div_self hca, fun b => ?_⟩, ?_⟩
  · rw [norm_div]
    exact div_le_one_of_le₀ (ha b) (norm_nonneg _)
  · intro i
    have : ∑ b, κ (c b) w / κ (c a) w * κ (X b i) w = (κ (c a) w)⁻¹ * ∑ b, κ (c b) w * κ (X b i) w := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [this, hsum i, mul_zero, norm_zero]
    exact hε

theorem boxK_goodK_topology : ∀ (K W : Type) [CommRing K] [TopologicalSpace K] [Fintype W] (κ : K ≃+* (W → ℂ)), IsHomeomorph κ → ∀ n M : ℕ, (∀ r : Fin n → W → ℝ, IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) ∧ IsOpen {X : Fin n → Fin M → K | LinearIndependent K X} ∧ ∀ R ε : ℝ, 0 < ε → IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε) ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε ⊆ {X : Fin n → Fin M → K | LinearIndependent K X} := by
  intro K W _ _ _ κ hκ n M
  refine ⟨fun r => isCompact_boxK κ hκ r, isOpen_linIndep κ hκ n M, fun R ε hε => ⟨?_, goodK_subset κ R ε hε⟩⟩
  refine (isCompact_boxK κ hκ _).diff ?_
  exact isOpen_iUnion fun w => isOpen_iUnion fun a => isOpen_iUnion fun s => isOpen_iUnion fun _ =>
    isOpen_nearK κ hκ w s ε

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo
