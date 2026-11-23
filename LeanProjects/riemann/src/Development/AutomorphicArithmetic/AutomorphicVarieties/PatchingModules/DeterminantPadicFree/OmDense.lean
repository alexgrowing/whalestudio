import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa.Det

open Polynomial

private noncomputable def dsc {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : R :=
  resultant M.charpoly (derivative M.charpoly) n n

private theorem dsc_map {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S) (M : Matrix (Fin n) (Fin n) R) :
    dsc (M.map φ) = φ (dsc M) := by
  unfold dsc
  rw [Matrix.charpoly_map, derivative_map, resultant_map_map]

private theorem dsc_ne_iff {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    dsc M ≠ 0 ↔ M.charpoly.Separable := by
  have hm : M.charpoly.Monic := Matrix.charpoly_monic M
  have hd : M.charpoly.natDegree = n := by simp [Matrix.charpoly_natDegree_eq_dim]
  have hle : (derivative M.charpoly).natDegree ≤ n :=
    (natDegree_derivative_le _).trans (by omega)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  have hc : M.charpoly.coeff n = 1 := by
    have := hm.coeff_natDegree
    rwa [hd] at this
  have h1 : dsc M = resultant M.charpoly (derivative M.charpoly) := by
    unfold dsc
    have := resultant_add_right_deg M.charpoly (derivative M.charpoly) n (derivative M.charpoly).natDegree k le_rfl
    rw [← hk, hc, one_pow, one_mul] at this
    rw [this, hd]
  rw [h1, ← isUnit_iff_ne_zero, isUnit_resultant_iff_isCoprime hm]
  rfl

private theorem sep_iff {A : Type} [CommRing A] [IsDomain A] {n : ℕ} (M : Matrix (Fin n) (Fin n) A) :
    (M.charpoly.map (algebraMap A (FractionRing A))).Separable ↔ dsc M ≠ 0 := by
  rw [← Matrix.charpoly_map, ← dsc_ne_iff, dsc_map]
  exact (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A)))

private theorem sep_open {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) :
    IsOpen {σ : F.G₀ | ((mat x.ρ σ).charpoly.map (algebraMap x.A (FractionRing x.A))).Separable} := by
  simp only [sep_iff]
  rw [isOpen_iff_mem_nhds]
  intro s hs
  have hN : ∃ N : ℕ, dsc (mat x.ρ s) ∉ maximalIdeal x.A ^ N := by
    by_contra hc
    push Not at hc
    have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal x.A) (maximalIdeal.isMaximal _).ne_top
    have h2 : dsc (mat x.ρ s) ∈ ⨅ N : ℕ, maximalIdeal x.A ^ N := Submodule.mem_iInf _ |>.2 hc
    rw [this] at h2
    exact hs (by simpa using h2)
  obtain ⟨N, hN⟩ := hN
  have hev : ∀ᶠ g in nhds s, ∀ i j, Ideal.Quotient.mk (maximalIdeal x.A ^ N) (mat x.ρ g i j)
      = Ideal.Quotient.mk (maximalIdeal x.A ^ N) (mat x.ρ s i j) := by
    simp only [Filter.eventually_all]
    intro i j
    exact (x.cont i j N).eventually_eq s
  filter_upwards [hev] with g hg h0
  apply hN
  have hM : (mat x.ρ g).map (Ideal.Quotient.mk (maximalIdeal x.A ^ N))
      = (mat x.ρ s).map (Ideal.Quotient.mk (maximalIdeal x.A ^ N)) := by
    ext i j; exact hg i j
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← dsc_map, ← hM, dsc_map, h0, map_zero]

end UpperTheory.V.Pa.Det

theorem UpperTheory.V.Pa.Det.omDense :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n h : ℕ} (x : Fin h → NP F n), (∀ i, (x i).N3) → (F.G' : Set F.G₀) ⊆ closure {σ : F.G₀ | σ ∈ F.G' ∧ ∀ i, ((mat (x i).ρ σ).charpoly.map (algebraMap (x i).A (FractionRing (x i).A))).Separable} := by
  intro l _ F n h x hx σ hσ
  rw [mem_closure_iff]
  intro U hU hσU
  have key : ∀ S : Finset (Fin h), ∃ τ ∈ U ∩ (F.G' : Set F.G₀), ∀ i ∈ S,
      ((mat (x i).ρ τ).charpoly.map (algebraMap (x i).A (FractionRing (x i).A))).Separable := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨σ, ⟨hσU, hσ⟩, by simp⟩
    | insert a S ha ih =>
      obtain ⟨τ, ⟨h1, h2⟩, h3⟩ := ih
      have ho : IsOpen (U ∩ ⋂ i ∈ S, {σ : F.G₀ | ((mat (x i).ρ σ).charpoly.map
          (algebraMap (x i).A (FractionRing (x i).A))).Separable}) :=
        hU.inter (isOpen_biInter_finset fun i _ => UpperTheory.V.Pa.Det.sep_open (x i))
      obtain ⟨τ', ⟨⟨g1, g2⟩, g3⟩, g4⟩ := hx a _ ho ⟨τ, ⟨h1, Set.mem_iInter₂.2 h3⟩, h2⟩
      refine ⟨τ', ⟨g1, g3⟩, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact g4
      · exact Set.mem_iInter₂.1 g2 i hi
  obtain ⟨τ, ⟨h1, h2⟩, h3⟩ := key Finset.univ
  exact ⟨τ, h1, h2, fun i => h3 i (Finset.mem_univ i)⟩
