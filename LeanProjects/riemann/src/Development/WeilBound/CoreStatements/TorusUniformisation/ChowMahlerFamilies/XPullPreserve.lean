import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_pull_preserve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)

theorem below_ne {Ω : Type} [Field Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (h : mseg (joinCoord x z) s ≠ 0) : mseg x (restrictChart s) ≠ 0 := by
  unfold mseg at h ⊢
  rw [Finset.prod_ne_zero_iff] at h ⊢
  intro k _
  exact h (Sum.inl k) (Finset.mem_univ _)

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {V : Type} [AddCommGroup V]
  [Module Ω V]

theorem smul_mem (R : Subalgebra O Ω) (L : AddSubgroup V) (b : Ω) (hb : b ∈ R) (v : V)
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e}) :
    b • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, e, he, rfl⟩ := hv
    exact AddSubgroup.subset_closure ⟨b * a, R.mul_mem hb ha, e, he, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
  | neg v _ hv => rw [smul_neg]; exact neg_mem hv

theorem le_closure (R : Subalgebra O Ω) (L L' : AddSubgroup V) (h : L ≤ L') :
    AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e} ≤
      AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L', v = a • e} := by
  apply AddSubgroup.closure_mono
  rintro v ⟨a, ha, e, he, rfl⟩
  exact ⟨a, ha, e, h he, rfl⟩

theorem gen_closure [IsDomain O] (R : Subalgebra O Ω) (L L' : AddSubgroup V)
    (h : ∀ v ∈ L, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ L') (v : V)
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e}) :
    ∃ c : O, c ≠ 0 ∧
      algebraMap O Ω c • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L', v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, e, he, rfl⟩ := hv
    obtain ⟨c, hc, hce⟩ := h e he
    exact ⟨c, hc, AddSubgroup.subset_closure ⟨a, ha, _, hce, smul_comm _ _ _⟩⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | add v w _ _ hv hw =>
    obtain ⟨c, hc, hv⟩ := hv
    obtain ⟨d, hd, hw⟩ := hw
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add, map_mul]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact smul_mem R L' _ (R.algebraMap_mem d) _ hv
    · rw [mul_smul]
      exact smul_mem R L' _ (R.algebraMap_mem c) _ hw
  | neg v _ hv =>
    obtain ⟨c, hc, hv⟩ := hv
    exact ⟨c, hc, by rw [smul_neg]; exact neg_mem hv⟩

theorem scaled_closure (R : Subalgebra O Ω) (L L' : AddSubgroup V) (c : Ω)
    (h : ∀ v, v ∈ L' ↔ ∃ e ∈ L, v = c • e) (v : V) :
    v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L', v = a • e} ↔
      ∃ e ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e}, v = c • e := by
  constructor
  · intro hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨a, ha, e, he, rfl⟩ := hv
      obtain ⟨e', he', rfl⟩ := (h e).1 he
      exact ⟨a • e', AddSubgroup.subset_closure ⟨a, ha, e', he', rfl⟩, smul_comm _ _ _⟩
    | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
    | add v w _ _ hv hw =>
      obtain ⟨e, he, rfl⟩ := hv
      obtain ⟨f, hf, rfl⟩ := hw
      exact ⟨e + f, add_mem he hf, (smul_add _ _ _).symm⟩
    | neg v _ hv =>
      obtain ⟨e, he, rfl⟩ := hv
      exact ⟨-e, neg_mem he, (smul_neg _ _).symm⟩
  · rintro ⟨e, he, rfl⟩
    induction he using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨a, ha, e, he, rfl⟩ := hv
      exact AddSubgroup.subset_closure ⟨a, ha, c • e, (h _).2 ⟨e, he, rfl⟩, smul_comm _ _ _⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | neg v _ hv => rw [smul_neg]; exact neg_mem hv

end PositivityTheory.Xgn.A_pull_preserve

theorem PositivityTheory.Xgn.t_pull_preserve : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → (LatLE O x E E' → LatLE O (joinCoord x z) EB E'B) ∧ (SameGeneric O x E E' → SameGeneric O (joinCoord x z) EB E'B) ∧ (∀ c : Ω, IsScaled x c E.lat E'.lat → IsScaled (joinCoord x z) c EB.lat E'B.lat) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E E' K' _ _ ι' _ z EB E'B hP hP'
  refine ⟨fun h s hs => ?_, fun h s hs => ?_, fun c h s hs v => ?_⟩
  · rw [hP s hs, hP' s hs]
    exact PositivityTheory.Xgn.A_pull_preserve.le_closure _ _ _ (h _ (PositivityTheory.Xgn.A_pull_preserve.below_ne x z s hs))
  · rw [hP s hs, hP' s hs]
    have h0 := h _ (PositivityTheory.Xgn.A_pull_preserve.below_ne x z s hs)
    exact ⟨PositivityTheory.Xgn.A_pull_preserve.gen_closure _ _ _ h0.1,
      PositivityTheory.Xgn.A_pull_preserve.gen_closure _ _ _ h0.2⟩
  · rw [hP s hs, hP' s hs]
    exact PositivityTheory.Xgn.A_pull_preserve.scaled_closure _ _ _ c
      (h _ (PositivityTheory.Xgn.A_pull_preserve.below_ne x z s hs)) v
