import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtDivOfIsGenAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Transition

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem germ_res_val {U W : X.Opens} (h : W ≤ U) (u : Γ(X, U)ˣ) (q : X) (hq : q ∈ W) :
    X.presheaf.germ W q hq (res h u).val = X.presheaf.germ U q (h hq) u.val :=
  TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE h) q hq u.val

theorem sec_ext {U : X.Opens} {s t : Γ(X, U)}
    (h : ∀ q (hq : q ∈ U), X.presheaf.germ U q hq s = X.presheaf.germ U q hq t) : s = t :=
  TopCat.Presheaf.section_ext X.sheaf U s t h

theorem exists_unit_of_unitAt [IsLocallyNoetherian X] (hξ : IsCptGen ξ) (U : X.Opens)
    (hU : ∀ q ∈ U, genPt ξ ⤳ q) (a : Ω) (ha : ∀ q (hq : q ∈ U), unitAt ξ ⟨q, hU q hq⟩ a) :
    ∃ u : Γ(X, U)ˣ, ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq u.val) = a := by
  by_cases hne : (U : Set X).Nonempty
  · obtain ⟨s, hs, -⟩ := RegSection.existsUnique_section X Ω ξ hξ U hU a hne fun q hq => (ha q hq).2.1
    obtain ⟨t, ht, -⟩ := RegSection.existsUnique_section X Ω ξ hξ U hU a⁻¹ hne fun q hq => (ha q hq).2.2
    have st : s * t = 1 := RegSection.section_eq hξ U hU _ _ fun q hq => by
      rw [map_mul, map_mul, hs q hq, ht q hq, map_one, map_one, mul_inv_cancel₀ (ha q hq).1]
    exact ⟨⟨s, t, st, by rw [mul_comm, st]⟩, hs⟩
  · exact ⟨1, fun q hq => (hne ⟨q, hq⟩).elim⟩

theorem exists_transition : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) [IsLocallyNoetherian X] (I : Type) (V : Option I → X.Opens) (T : I → Ω), IsCptGen ξ → (∀ i, ∀ q ∈ V (some i), genPt ξ ⤳ q) → (∀ q ∈ V none, ¬ genPt ξ ⤳ q) → (∀ (i j : I) (q : X) (hq : genPt ξ ⤳ q), q ∈ V (some i) → q ∈ V (some j) → unitAt ξ ⟨q, hq⟩ (T j / T i)) → (⨆ i, V i = ⊤) → ∃ g : ∀ i j, Γ(X, V i ⊓ V j)ˣ, (LB.mk (Option I) V g).IsLB ∧ ∀ (i j : I) (q : X) (hq : genPt ξ ⤳ q) (h : q ∈ V (some i) ⊓ V (some j)), genMap ξ ⟨q, hq⟩ (X.presheaf.germ _ q h (g (some i) (some j)).val) = T j / T i := by
  intro X Ω _ ξ _ I V T hξ hsome hnone hunit hcov
  have hU : ∀ (i j : I), ∀ q ∈ V (some i) ⊓ V (some j), genPt ξ ⤳ q := fun i j q hq => hsome i q hq.1
  have A := fun i j => exists_unit_of_unitAt hξ (V (some i) ⊓ V (some j)) (hU i j) (T j / T i)
    fun q hq => hunit i j q _ hq.1 hq.2
  choose u hu using A
  obtain ⟨g, hg₁, hg₂, hg₃⟩ : ∃ g : ∀ i j, Γ(X, V i ⊓ V j)ˣ, (∀ i j, g (some i) (some j) = u i j) ∧
      (∀ j, g none j = 1) ∧ (∀ i, g (some i) none = 1) :=
    ⟨fun i j => match i, j with
      | some i, some j => u i j
      | none, _ => 1
      | some _, none => 1, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  have val : ∀ (i j : I) {W : X.Opens} (h : W ≤ V (some i) ⊓ V (some j)) (q : X) (hq : q ∈ W)
      (hq' : genPt ξ ⤳ q), genMap ξ ⟨q, hq'⟩ (X.presheaf.germ W q hq (res h (u i j)).val) = T j / T i := by
    intro i j W h q hq hq'
    rw [germ_res_val]
    exact hu i j q (h hq)
  refine ⟨g, ⟨hcov, ?_, ?_⟩, fun i j q hq h => ?_⟩
  · intro i
    dsimp only
    apply Units.ext
    rcases i with _ | i
    · simp only [hg₂, map_one]
    · apply sec_ext
      intro q hq
      have hq' := hsome i q hq
      apply hξ.inj ⟨q, hq'⟩
      rw [hg₁, val i i _ q hq hq', Units.val_one, map_one, map_one]
      exact div_self fun e => (hunit i i q hq' hq hq).1 (by simp [e])
  · intro i j k
    dsimp only
    apply Units.ext
    apply sec_ext
    rintro q ⟨⟨hi, hj⟩, hk⟩
    have bad : ∀ a : I, q ∈ V none → q ∈ V (some a) → False := fun a h h' => hnone q h (hsome a q h')
    rcases i with _ | i <;> rcases j with _ | j <;> rcases k with _ | k
    · simp only [hg₂, map_one, _root_.mul_one]
    · exact (bad _ hi hk).elim
    · exact (bad _ hi hj).elim
    · exact (bad _ hi hj).elim
    · exact (bad _ hj hi).elim
    · exact (bad _ hj hi).elim
    · exact (bad _ hk hi).elim
    · have hq' := hsome i q hi
      apply hξ.inj ⟨q, hq'⟩
      have n₁ := (hunit i j q hq' hi hj).1
      have t₁ : T i ≠ 0 := fun e => n₁ (by simp [e])
      have t₂ : T j ≠ 0 := fun e => n₁ (by simp [e])
      simp only [hg₁, Units.val_mul, map_mul]
      have hW : q ∈ V (some i) ⊓ V (some j) ⊓ V (some k) := ⟨⟨hi, hj⟩, hk⟩
      have e₁ := val i j (W := V (some i) ⊓ V (some j) ⊓ V (some k)) inf_le_left q hW hq'
      have e₂ := val j k (W := V (some i) ⊓ V (some j) ⊓ V (some k))
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) q hW hq'
      have e₃ := val i k (W := V (some i) ⊓ V (some j) ⊓ V (some k))
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right) q hW hq'
      refine (congrArg₂ (· * ·) e₁ e₂).trans (Eq.trans ?_ e₃.symm)
      field_simp
  · simpa only [hg₁] using hu i j q h

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Transition
