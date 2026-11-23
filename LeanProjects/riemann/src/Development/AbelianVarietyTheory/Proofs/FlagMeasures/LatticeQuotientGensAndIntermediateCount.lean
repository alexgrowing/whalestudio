import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.LatticeGens

section Dedekind
variable {R V : Type*} [CommRing R] [IsDedekindDomain R] [AddCommGroup V] [Module R V]

theorem exists_gens_of_between (A : Submodule R V) (m : R) (hm : m ≠ 0) (t : Finset V) :
    (∀ x ∈ t, m • x ∈ A) → ∀ L : Submodule R V, A ≤ L → L ≤ A ⊔ Submodule.span R (t : Set V) →
      ∃ t' : Finset V, t'.card ≤ t.card ∧ L = A ⊔ Submodule.span R (t' : Set V) := by
  induction t using Finset.induction_on with
  | empty =>
    intro _ L h1 h2
    exact ⟨∅, le_rfl, le_antisymm h2 (by simpa using h1)⟩
  | insert x t hx ih =>
    intro ht L h1 h2
    obtain ⟨t', hc, ht'⟩ := ih (fun y hy => ht y (Finset.mem_insert_of_mem hy))
      (L ⊓ (A ⊔ Submodule.span R (t : Set V))) (le_inf h1 le_sup_left) inf_le_right
    set I : Ideal R := (A ⊔ Submodule.span R (t : Set V)).comap (LinearMap.toSpanSingleton R V x)
      with hI
    set J : Ideal R := (L ⊔ Submodule.span R (t : Set V)).comap (LinearMap.toSpanSingleton R V x)
      with hJ
    have hIJ : I ≤ J := Submodule.comap_mono (sup_le_sup_right h1 _)
    have hI0 : I ≠ 0 := by
      intro h
      have : m ∈ I := Submodule.mem_sup_left (ht x (Finset.mem_insert_self _ _))
      rw [h] at this
      exact hm (by simpa using this)
    obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hIJ hI0
    have haJ : a ∈ J := by
      rw [← ha]; exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)
    obtain ⟨l, hl, s, hs, hls⟩ := Submodule.mem_sup.1 haJ
    have hls' : l + s = a • x := hls
    refine ⟨insert l t', ?_, le_antisymm ?_ ?_⟩
    · rw [Finset.card_insert_of_notMem hx]
      exact (Finset.card_insert_le _ _).trans (by omega)
    · intro y hy
      have hy2 := h2 hy
      rw [Finset.coe_insert, Submodule.span_insert] at hy2
      obtain ⟨a0, ha0, z, hz, rfl⟩ := Submodule.mem_sup.1 hy2
      obtain ⟨w, hw, s0, hs0, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have hr : r ∈ J := by
        have : r • x = ((a0 + (r • x + s0)) - a0) - s0 := by abel
        change r • x ∈ L ⊔ Submodule.span R (t : Set V)
        rw [this]
        exact sub_mem (Submodule.mem_sup_left (sub_mem hy (h1 ha0))) (Submodule.mem_sup_right hs0)
      rw [← ha] at hr
      obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.1 hr
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.1 hj
      have hi' : i • x ∈ A ⊔ Submodule.span R (t : Set V) := hi
      have key : a0 + ((i + k * a) • x + s0) - k • l ∈
          L ⊓ (A ⊔ Submodule.span R (t : Set V)) := by
        refine ⟨sub_mem hy (L.smul_mem _ hl), ?_⟩
        have : a0 + ((i + k * a) • x + s0) - k • l = a0 + i • x + s0 + k • s := by
          rw [add_smul, mul_smul, ← hls', smul_add]; abel
        rw [this]
        exact add_mem (add_mem (add_mem (Submodule.mem_sup_left ha0) hi')
          (Submodule.mem_sup_right hs0)) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hs))
      rw [ht'] at key
      have hle : A ⊔ Submodule.span R (t' : Set V) ≤
          A ⊔ Submodule.span R ((insert l t' : Finset V) : Set V) :=
        sup_le_sup_left (Submodule.span_mono (by simp)) _
      have hl' : k • l ∈ A ⊔ Submodule.span R ((insert l t' : Finset V) : Set V) :=
        Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      simpa using add_mem (hle key) hl'
    · rw [Finset.coe_insert, Submodule.span_insert]
      refine sup_le h1 (sup_le ?_ ?_)
      · exact (Submodule.span_singleton_le_iff_mem _ _).2 hl
      · exact (le_sup_right.trans ht'.ge).trans inf_le_left

end Dedekind

section Count
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem idxN_smul_mem (A B : Submodule R V) {x : V} (hx : x ∈ B) :
    ((idxN B A : ℕ) : R) • x ∈ A := by
  rw [Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup (K := B.toAddSubgroup) hx

theorem card_map_mkQ (A B : Submodule R V) : Nat.card (B.map A.mkQ) = idxN B A := by
  have h := AddSubgroup.relIndex_ker (K := B.toAddSubgroup) A.mkQ.toAddMonoidHom
  have hk : A.mkQ.toAddMonoidHom.ker = A.toAddSubgroup := by
    ext x; simp
  rw [hk] at h
  unfold idxN
  rw [h]
  rfl

theorem encard_between_le (A B : Submodule R V) (hn : idxN B A ≠ 0) (e : ℕ)
    (h : ∀ L, A ≤ L → L ≤ B →
      ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span R (t' : Set V)) :
    {L | A ≤ L ∧ L ≤ B}.encard ≤ ((idxN B A ^ e : ℕ) : ℕ∞) := by
  have hfin : Finite (B.map A.mkQ) := Nat.finite_of_card_ne_zero (by rwa [card_map_mkQ])
  let Φ : (Fin e → B.map A.mkQ) → Submodule R V := fun f =>
    (Submodule.span R (Set.range fun i => (f i : V ⧸ A))).comap A.mkQ
  have hsub : {L | A ≤ L ∧ L ≤ B} ⊆ Φ '' Set.univ := by
    rintro L ⟨h1, h2⟩
    obtain ⟨t, hc, ht⟩ := h L h1 h2
    obtain ⟨emb⟩ : Nonempty (t ↪ Fin e) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hc)
    let g : Fin e → V := Function.extend emb (fun x => (x : V)) 0
    have hg : ∀ i, g i ∈ Submodule.span R (t : Set V) := by
      intro i
      by_cases hi : ∃ x, emb x = i
      · obtain ⟨x, rfl⟩ := hi
        simp only [g, emb.injective.extend_apply]
        exact Submodule.subset_span x.2
      · simp only [g, Function.extend_apply' _ _ _ hi]
        simp
    have hspan : Submodule.span R (Set.range g) = Submodule.span R (t : Set V) := by
      refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
      · rintro _ ⟨i, rfl⟩; exact hg i
      · intro x hx
        exact ⟨emb ⟨x, hx⟩, by simp only [g, emb.injective.extend_apply]⟩
    have hgB : ∀ i, g i ∈ B := fun i => h2 (by rw [ht]; exact Submodule.mem_sup_right (hg i))
    refine ⟨fun i => ⟨A.mkQ (g i), Submodule.mem_map_of_mem (hgB i)⟩, trivial, ?_⟩
    have : (Set.range fun i => A.mkQ (g i)) = A.mkQ '' Set.range g := by
      rw [← Set.range_comp]; rfl
    change (Submodule.span R (Set.range fun i => A.mkQ (g i))).comap A.mkQ = L
    rw [this, ← Submodule.map_span, Submodule.comap_map_mkQ, hspan, ← ht]
  calc {L | A ≤ L ∧ L ≤ B}.encard ≤ (Φ '' Set.univ).encard := Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set (Fin e → B.map A.mkQ)).encard := Set.encard_image_le _ _
    _ = _ := by
      rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_fun, card_map_mkQ]
      simp

end Count

theorem exists_scaled_span (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (B : Submodule (𝓞 K) V) (hB : B.FG) :
    ∃ (c : 𝓞 K) (t : Finset V), c ≠ 0 ∧ t.card ≤ Module.finrank K V ∧ (∀ x ∈ t, c • x ∈ B) ∧
      B ≤ Submodule.span (𝓞 K) (t : Set V) := by
  obtain ⟨b, hbB, hspan, hli⟩ := exists_linearIndependent K (B : Set V)
  have hbf : b.Finite := hli.setFinite
  obtain ⟨s, rfl⟩ := hbf.exists_finset_coe
  have hcard : s.card ≤ Module.finrank K V := LinearIndependent.finset_card_le_finrank hli
  obtain ⟨G, rfl⟩ := hB
  have h1 : ∀ x ∈ G, ∃ c : 𝓞 K, c ≠ 0 ∧ c • x ∈ Submodule.span (𝓞 K) (s : Set V) := by
    intro x hx
    have hx' : x ∈ Submodule.span K (s : Set V) := by
      rw [hspan]; exact Submodule.subset_span (Submodule.subset_span hx)
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ hx'
    exact ⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩
  choose! f hf0 hf using h1
  set c : 𝓞 K := ∏ x ∈ G, f x with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 hf0
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := by simpa using hc0
  have hcG : ∀ x ∈ G, c • x ∈ Submodule.span (𝓞 K) (s : Set V) := by
    intro x hx
    rw [hc, ← Finset.prod_erase_mul _ _ hx, mul_smul]
    exact Submodule.smul_mem _ _ (hf x hx)
  let φ : V →ₗ[𝓞 K] V := (LinearMap.lsmul K V (algebraMap (𝓞 K) K c)⁻¹).restrictScalars (𝓞 K)
  have hφ : ∀ x, φ (c • x) = x := by
    intro x
    simp only [φ, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    rw [← algebraMap_smul K c x, smul_smul, inv_mul_cancel₀ hcK, one_smul]
  refine ⟨c, s.image φ, hc0, Finset.card_image_le.trans hcard, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    rw [← map_smul, hφ]
    exact hbB hy
  · rw [Submodule.span_le]
    intro x hx
    rw [Finset.coe_image, ← Submodule.map_span, ← hφ x]
    exact Submodule.mem_map_of_mem (hcG x hx)

theorem gens_and_count : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (A B : Submodule (𝓞 K) V), A ≤ B → idxN B A ≠ 0 → (B.FG → ∃ t : Finset V, t.card ≤ Module.finrank K V ∧ B = A ⊔ Submodule.span (𝓞 K) (t : Set V)) ∧ ∀ (e : ℕ) (t : Finset V), t.card ≤ e → B = A ⊔ Submodule.span (𝓞 K) (t : Set V) → ({L | A ≤ L ∧ L ≤ B}.encard ≤ ((idxN B A ^ e : ℕ) : ℕ∞)) ∧ ∀ L, A ≤ L → L ≤ B → ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span (𝓞 K) (t' : Set V) := by
  intro K V _ _ _ _ _ _ _ A B hAB hn
  have hn' : ((idxN B A : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine ⟨fun hB => ?_, fun e t hc ht => ?_⟩
  · obtain ⟨c, t, hc0, hcard, hcB, hBt⟩ := exists_scaled_span K V B hB
    obtain ⟨t', h1, h2⟩ := exists_gens_of_between A (((idxN B A : ℕ) : 𝓞 K) * c)
      (mul_ne_zero hn' hc0) t
      (fun x hx => by rw [mul_smul]; exact idxN_smul_mem A B (hcB x hx)) B hAB
      (hBt.trans le_sup_right)
    exact ⟨t', h1.trans hcard, h2⟩
  · have key : ∀ L, A ≤ L → L ≤ B →
        ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span (𝓞 K) (t' : Set V) := by
      intro L h1 h2
      obtain ⟨t', h3, h4⟩ := exists_gens_of_between A _ hn' t
        (fun x hx => idxN_smul_mem A B
          (by rw [ht]; exact Submodule.mem_sup_right (Submodule.subset_span hx))) L h1
        (h2.trans ht.le)
      exact ⟨t', h3.trans hc, h4⟩
    exact ⟨encard_between_le A B hn e key, key⟩

end GlobalTheory.Mass.LatticeGens
