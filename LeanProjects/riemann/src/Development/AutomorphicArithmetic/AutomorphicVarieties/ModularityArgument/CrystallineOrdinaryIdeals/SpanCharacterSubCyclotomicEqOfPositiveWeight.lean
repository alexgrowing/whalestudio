import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.CharCycIdeal

theorem isClosed_ideal {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [TopologicalSpace B]
    [IsModuleTopology ℚ_[l] B] (J : Ideal B) : IsClosed (J : Set B) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨f, hf, hJ⟩ := Submodule.exists_le_ker_of_notMem (p := J.restrictScalars ℚ_[l]) (v := x) hx
  have hc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  refine Filter.mem_of_superset ((isOpen_ne.preimage hc).mem_nhds (x := x) hf) fun y hy h => hy ?_
  exact hJ (x := y) h

theorem span_range_sub_cyc : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → Ideal.span (Set.range fun g => (χ g : B) - (cycA l l B (φ g) : B)) = (if w = 1 then Ideal.span {(χ σ : B) - (cycA l l B (φ σ) : B)} else ⊤) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ χ hχ w hw hI σ hσ
  have hA : ∀ g : GQ l, (cycA l l B g : B) = algebraMap ℚ_[l] B (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := fun g =>
    IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B _
  split_ifs with h1
  · subst h1
    refine le_antisymm ?_ (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨σ, rfl⟩))
    set J := Ideal.span {(χ σ : B) - (cycA l l B (φ σ) : B)} with hJ
    have hε : Continuous fun g => (cycA l l B (φ g) : B) := by
      simp only [hA]
      have h0 : Continuous (algebraMap ℚ_[l] B) :=
        IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] B)
      have h2 : Continuous fun x : ℤ_[l] => (x : ℚ_[l]) := continuous_subtype_val
      exact h0.comp (h2.comp (Units.continuous_val.comp
        ((UpperTheory.V.Loc.cycFacts l l).1.comp hφ.continuous)))
    let q : Bˣ →* (B ⧸ J)ˣ := Units.map (Ideal.Quotient.mk J : B →* B ⧸ J)
    let H : Subgroup G := (q.comp χ).eqLocus (q.comp ((cycA l l B).comp φ))
    have hH : ∀ g, g ∈ H ↔ (χ g : B) - (cycA l l B (φ g) : B) ∈ J := fun g => by
      rw [← Ideal.Quotient.eq]
      exact Units.ext_iff
    have hcl : IsClosed (H : Set G) := by
      have : (H : Set G) = (fun g => (χ g : B) - (cycA l l B (φ g) : B)) ⁻¹' (J : Set B) := Set.ext hH
      rw [this]
      exact (isClosed_ideal (l := l) J).preimage (hχ.sub hε)
    have hle : (Iq l).comap φ ⊔ Subgroup.zpowers σ ≤ H := by
      refine sup_le (fun g hg => ?_) ((Subgroup.zpowers_le).2 ?_)
      · rw [hH, hI g hg, zpow_one, sub_self]
        exact J.zero_mem
      · rw [hH]
        exact Ideal.subset_span rfl
    have htop := Subgroup.topologicalClosure_minimal _ hle hcl
    rw [hσ] at htop
    rw [Ideal.span_le]
    rintro _ ⟨g, rfl⟩
    exact (hH g).1 (htop (Subgroup.mem_top g))
  · obtain ⟨s, ⟨⟨g, rfl⟩, hg⟩, hs⟩ := ((UpperTheory.V.Loc.cycInertia l).2 φ.range hφ.isOpen_range).2
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, w = ((n + 2 : ℕ) : ℤ) := ⟨(w - 2).toNat, by omega⟩
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨g, rfl⟩) ?_
    show IsUnit ((χ g : B) - (cycA l l B (φ g) : B))
    rw [hI g hg, zpow_natCast, Units.val_pow_eq_pow_val, hA, ← map_pow, ← map_sub]
    refine IsUnit.map _ (Ne.isUnit fun h => hs ?_)
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨n + 1, n.succ_pos, ?_⟩
    have h2 : cyc l l (φ g) ^ (n + 2) = cyc l l (φ g) := by
      apply Units.ext
      apply Subtype.ext
      rw [Units.val_pow_eq_pow_val]
      push_cast
      exact sub_eq_zero.1 h
    rw [pow_succ] at h2
    exact mul_eq_right.1 h2

end GlobalTheory.CharCycIdeal
