import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsIntegers

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.SchAFactor

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_finset_of_isCompact {C : Set (FiniteAdeleRing (𝓞 F) F)} (hC : IsCompact C) :
    ∃ T : Finset (Pl F), ∀ y ∈ C, ∀ v ∉ T, evalV F v y ∈ v.adicCompletionIntegers F := by
  classical
  let U : Set (FiniteAdeleRing (𝓞 F) F) := {f | ∀ v, f.1 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))}
  have hU : IsOpen U := RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun c : C => (fun y => y - c.1) ⁻¹' U)
    (fun c => hU.preimage (continuous_sub_right _)) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, by
      intro v
      show (y - y).1 v ∈ _
      rw [sub_self]
      exact zero_mem _⟩)
  have hfin : ∀ c : C, {v : Pl F | ¬ c.1.1 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))}.Finite :=
    fun c => Filter.eventually_cofinite.1 c.1.2
  refine ⟨t.biUnion fun c => (hfin c).toFinset, fun y hy v hv => ?_⟩
  obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hy)
  have h1 : (y - c.1).1 v ∈ v.adicCompletionIntegers F := hc v
  have h2 : c.1.1 v ∈ v.adicCompletionIntegers F := by
    by_contra h
    exact hv (Finset.mem_biUnion.2 ⟨c, hct, (hfin c).mem_toFinset.2 h⟩)
  have e : evalV F v y = (y - c.1).1 v + c.1.1 v := by
    change y.1 v = y.1 v - c.1.1 v + c.1.1 v
    exact (sub_add_cancel _ _).symm
  rw [e]
  exact add_mem h1 h2

def GoodAt (v : Pl F) (Φ : (κ → AF F) → ℂ) : Prop :=
  (∀ x, Φ x ≠ 0 → ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F) ∧
    ∀ x z, At (evFin F v) z → (∀ i, evFin F v (z i) ∈ v.adicCompletionIntegers F) → Φ (x + z) = Φ x

theorem at_comp {v : Pl F} {z : κ → AF F} (hz : At (evFin F v) z) (i : κ) :
    (z i).1 = 0 ∧ ∀ w, w ≠ v → evFin F w (z i) = 0 := by
  have e : z i = GlobalTheory.LatVac.liftV v 1 * z i := by
    conv_lhs => rw [← partFin_of_at hz]
    rfl
  refine ⟨?_, fun w hw => ?_⟩
  · rw [e]
    change (GlobalTheory.LatVac.liftV v 1 : AF F).1 * (z i).1 = 0
    rw [show (GlobalTheory.LatVac.liftV v 1 : AF F).1 = 0 from rfl, zero_mul]
  · rw [e, map_mul, show evFin F w (GlobalTheory.LatVac.liftV v 1) = 0 from evalV_singleFin_ne hw 1, zero_mul]

theorem goodAt_zero (v : Pl F) : GoodAt v (0 : (κ → AF F) → ℂ) :=
  ⟨fun x h => absurd rfl h, fun _ _ _ _ => rfl⟩

theorem goodAt_add {v : Pl F} {Φ Ψ : (κ → AF F) → ℂ} (h : GoodAt v Φ) (h' : GoodAt v Ψ) : GoodAt v (Φ + Ψ) := by
  refine ⟨fun x hx => ?_, fun x z hz hi => ?_⟩
  · by_cases h0 : Φ x = 0
    · refine h'.1 x fun h1 => hx ?_
      simp [h0, h1]
    · exact h.1 x h0
  · simp only [Pi.add_apply, h.2 x z hz hi, h'.2 x z hz hi]

theorem goodAt_smul {v : Pl F} (c : ℂ) {Φ : (κ → AF F) → ℂ} (h : GoodAt v Φ) : GoodAt v (c • Φ) := by
  refine ⟨fun x hx => h.1 x fun h1 => hx ?_, fun x z hz hi => ?_⟩
  · simp [h1]
  · simp only [Pi.smul_apply, h.2 x z hz hi]

theorem goodAt_pureA (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : ∃ T : Finset (Pl F), ∀ v ∉ T, GoodAt v (pureA F f g) := by
  classical
  have hC : ∀ i : κ, IsCompact ((fun y : κ → FiniteAdeleRing (𝓞 F) F => y i) '' tsupport g) :=
    fun i => hg.2.isCompact.image (continuous_apply i)
  choose Ti hTi using fun i => exists_finset_of_isCompact (hC i)
  obtain ⟨B, -, -, hBev, hBinv⟩ := GlobalTheory.SBBox.exists_box_invariant F κ g hg
  have hfin := Filter.eventually_cofinite.1 hBev
  refine ⟨Finset.univ.biUnion Ti ∪ hfin.toFinset, fun v hv => ⟨fun x hx i => ?_, fun x z hz hi => ?_⟩⟩
  · have hg0 : g (fun i => (x i).2) ≠ 0 := fun h0 => hx (by simp [pureA, h0])
    have hmem : (x i).2 ∈ (fun y : κ → FiniteAdeleRing (𝓞 F) F => y i) '' tsupport g :=
      ⟨_, subset_tsupport g hg0, rfl⟩
    exact hTi i _ hmem v fun h => hv (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, h⟩))
  · have hBv : (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F := by
      by_contra h
      exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
    have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + z) i).1) =
        fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
      funext i
      rw [Pi.add_apply]
      congr 1
      change (x i).1 + (z i).1 = (x i).1
      rw [(at_comp hz i).1, add_zero]
    have e2 : (fun i => ((x + z) i).2) = (fun i => (x i).2) + fun i => (z i).2 := rfl
    have hg' : g (fun i => ((x + z) i).2) = g fun i => (x i).2 := by
      rw [e2]
      refine hBinv _ _ fun i w => ?_
      by_cases hw : w = v
      · subst hw
        rw [← SetLike.mem_coe, hBv]
        exact hi i
      · rw [show evalV F w (z i).2 = evFin F w (z i) from rfl, (at_comp hz i).2 w hw]
        exact zero_mem _
    simp only [pureA]
    rw [e1, hg']

theorem exists_goodAt {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : ∃ T : Finset (Pl F), ∀ v ∉ T, GoodAt v Φ := by
  classical
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact goodAt_pureA f hg
  | zero => exact ⟨∅, fun v _ => goodAt_zero v⟩
  | add Φ Ψ _ _ h h' =>
    obtain ⟨T, hT⟩ := h
    obtain ⟨T', hT'⟩ := h'
    exact ⟨T ∪ T', fun v hv => goodAt_add (hT v fun h => hv (Finset.mem_union_left _ h))
      (hT' v fun h => hv (Finset.mem_union_right _ h))⟩
  | smul c Φ _ h =>
    obtain ⟨T, hT⟩ := h
    exact ⟨T, fun v hv => goodAt_smul c (hT v hv)⟩

theorem exists_tens : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ, ∃ T : Finset (Pl F), ∀ v : Pl F, v ∉ T →
    ∃ (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ), Rest (evFin F v) φ r ∧ Φ = tens (evFin F v) φ r := by
  intro F _ _ κ _ Φ hΦ
  obtain ⟨T, hT⟩ := exists_goodAt hΦ
  refine ⟨T, fun v hv => ?_⟩
  obtain ⟨h1, h2⟩ := hT v hv
  have key : Φ = tens (evFin F v) (Set.indicator {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} 1)
      (fun x => Φ (x - partFin v x)) := by
    funext x
    simp only [tens]
    by_cases hx : ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F
    · rw [Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F}
        from hx), Pi.one_apply, one_mul]
      have h := h2 (x - partFin v x) (partFin v x) (at_partFin v x) fun i => by
        change evFin F v (GlobalTheory.LatVac.liftV v 1 * x i) ∈ _
        rw [map_mul, GlobalTheory.LatVac.evFin_liftV, one_mul]
        exact hx i
      rw [sub_add_cancel] at h
      exact h
    · rw [Set.indicator_of_notMem (show (fun i => evFin F v (x i)) ∉ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F}
        from hx), zero_mul]
      by_contra h
      exact hx (h1 x h)
  refine ⟨_, _, ⟨fun x z hz => ?_, by rw [← key]; exact hΦ⟩, key⟩
  have hz' : GlobalTheory.LatVac.liftV v 1 • z = z := partFin_of_at hz
  change Φ (x + z - GlobalTheory.LatVac.liftV v 1 • (x + z)) = Φ (x - GlobalTheory.LatVac.liftV v 1 • x)
  rw [smul_add, hz']
  congr 1
  abel

end GlobalTheory.SchAFactor
