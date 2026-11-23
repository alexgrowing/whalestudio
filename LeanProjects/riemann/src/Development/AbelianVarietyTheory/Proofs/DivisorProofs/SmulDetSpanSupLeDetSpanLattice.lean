import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.DetColon

variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ}

open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in
private lemma exterior_form_eq_zero_of_two_mem_span_singleton {ι : Type*} [DecidableEq ι]
    (f : V [⋀^ι]→ₗ[F] F) (u : V) (w : ι → V) {i k : ι} (hik : i ≠ k)
    (hi : w i ∈ Submodule.span (𝓞 F) {u}) (hk : w k ∈ Submodule.span (𝓞 F) {u}) :
    f w = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hi
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hk
  by_cases hb0 : algebraMap (𝓞 F) F b = 0
  · have hwk : w k = 0 := by
      rw [← hb, ← algebraMap_smul F b u, hb0, zero_smul]
    exact f.map_coord_zero k hwk
  · have hwi : w i = (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) • w k := by
      rw [← ha, ← hb, ← algebraMap_smul F a u, ← algebraMap_smul F b u, smul_smul,
        div_mul_cancel₀ _ hb0]
    have hfw : f w = f (Function.update w i
        ((algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) • w k)) := by
      rw [← hwi, Function.update_eq_self]
    rw [hfw, f.map_update_smul]
    have h0 : f (Function.update w i (w k)) = 0 :=
      f.map_eq_zero_of_eq (Function.update w i (w k)) (i := i) (j := k)
        (by simp [Function.update_of_ne hik.symm]) hik
    rw [h0, smul_zero]

open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in
private lemma multilinear_mem_span_of_entry_mem_span_singleton {ι : Type*} [DecidableEq ι]
    (f : V [⋀^ι]→ₗ[F] F) (N : Submodule (𝓞 F) V) (u : V) (s : Finset ι) :
    ∀ (i : ι) (w : ι → V), i ∉ s → w i ∈ Submodule.span (𝓞 F) {u} → (∀ j ∉ s, w j ∈ N) →
      (∀ j ∈ s, w j ∈ N ⊔ Submodule.span (𝓞 F) {u}) →
      f w ∈ Submodule.span (𝓞 F) {y | ∃ v : ι → V, (∀ j, v j ∈ N) ∧ y = f v} := by
  induction s using Finset.induction_on with
  | empty =>
    intro i w _ _ hN _
    exact Submodule.subset_span ⟨w, fun j => hN j (by simp), rfl⟩
  | @insert k s hks ih =>
    intro i w his hi hN hs
    have hik : i ≠ k := fun h => his (h ▸ Finset.mem_insert_self k s)
    have his' : i ∉ s := fun h => his (Finset.mem_insert_of_mem h)
    obtain ⟨n, hn, z, hz, hnz⟩ := Submodule.mem_sup.mp (hs k (Finset.mem_insert_self k s))
    have hsplit : f w = f (Function.update w k n) + f (Function.update w k z) := by
      rw [← f.map_update_add, hnz, Function.update_eq_self]
    rw [hsplit]
    refine Submodule.add_mem _ ?_ ?_
    · refine ih i _ his' ?_ ?_ ?_
      · rwa [Function.update_of_ne hik]
      · intro j hj
        by_cases hjk : j = k
        · rw [hjk, Function.update_self]
          exact hn
        · rw [Function.update_of_ne hjk]
          exact hN j (by simp [hjk, hj])
      · intro j hj
        have hjk : j ≠ k := fun h => hks (h ▸ hj)
        rw [Function.update_of_ne hjk]
        exact hs j (Finset.mem_insert_of_mem hj)
    · rw [exterior_form_eq_zero_of_two_mem_span_singleton f u _ hik
        (by rwa [Function.update_of_ne hik]) (by rw [Function.update_self]; exact hz)]
      exact Submodule.zero_mem _

open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in
private lemma smul_multilinear_mem_span {ι : Type*} [DecidableEq ι] (f : V [⋀^ι]→ₗ[F] F)
    (N : Submodule (𝓞 F) V) (u : V) (π : 𝓞 F) (hπ : π • u ∈ N) (s : Finset ι) :
    ∀ w : ι → V, (∀ j ∉ s, w j ∈ N) → (∀ j ∈ s, w j ∈ N ⊔ Submodule.span (𝓞 F) {u}) →
      π • f w ∈ Submodule.span (𝓞 F) {y | ∃ v : ι → V, (∀ j, v j ∈ N) ∧ y = f v} := by
  induction s using Finset.induction_on with
  | empty =>
    intro w hN _
    exact Submodule.smul_mem _ π (Submodule.subset_span ⟨w, fun j => hN j (by simp), rfl⟩)
  | @insert k s hks ih =>
    intro w hN hs
    obtain ⟨n, hn, z, hz, hnz⟩ := Submodule.mem_sup.mp (hs k (Finset.mem_insert_self k s))
    have hsplit : f w = f (Function.update w k n) + f (Function.update w k z) := by
      rw [← f.map_update_add, hnz, Function.update_eq_self]
    rw [hsplit, smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · refine ih _ ?_ ?_
      · intro j hj
        by_cases hjk : j = k
        · rw [hjk, Function.update_self]
          exact hn
        · rw [Function.update_of_ne hjk]
          exact hN j (by simp [hjk, hj])
      · intro j hj
        have hjk : j ≠ k := fun h => hks (h ▸ hj)
        rw [Function.update_of_ne hjk]
        exact hs j (Finset.mem_insert_of_mem hj)
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have key : π • f (Function.update w k (a • u)) = f (Function.update w k ((π * a) • u)) := by
        rw [mul_smul, ← algebraMap_smul F π (a • u), f.map_update_smul, algebraMap_smul]
      rw [key]
      refine multilinear_mem_span_of_entry_mem_span_singleton f N u s k _ hks ?_ ?_ ?_
      · rw [Function.update_self]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
      · intro j hj
        by_cases hjk : j = k
        · rw [hjk, Function.update_self, mul_comm, mul_smul]
          exact N.smul_mem a hπ
        · rw [Function.update_of_ne hjk]
          exact hN j (by simp [hjk, hj])
      · intro j hj
        have hjk : j ≠ k := fun h => hks (h ▸ hj)
        rw [Function.update_of_ne hjk]
        exact hs j (Finset.mem_insert_of_mem hj)

open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in

theorem _root_.GlobalTheory.DetColon.smul_detSpan_sup_le :
    ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
      [IsScalarTower (𝓞 F) F V] (d : ℕ) (b : Module.Basis (Fin d) F V) (N : Submodule (𝓞 F) V)
      (u : V) (π : 𝓞 F), π • u ∈ N →
      ∀ y ∈ Submodule.span (𝓞 F)
          {y | ∃ v : Fin d → V, (∀ i, v i ∈ N ⊔ Submodule.span (𝓞 F) {u}) ∧ y = b.det v},
        π • y ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ N) ∧ y = b.det v} := by
  intro F V _ _ _ _ _ _ d b N u π hπ y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact smul_multilinear_mem_span b.det N u π hπ Finset.univ v
      (fun j hj => absurd (Finset.mem_univ j) hj) (fun j _ => hv j)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hx

end GlobalTheory.DetColon
