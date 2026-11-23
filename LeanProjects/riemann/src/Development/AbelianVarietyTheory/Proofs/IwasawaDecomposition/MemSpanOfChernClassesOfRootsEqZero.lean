import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPolyChernRoots
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrassKernel

section Esymm

variable (R : Type) [CommRing R] {ι : Type} (m : ι → ℕ)

def blockEsymm : MvPolynomial (Root m) R →ₐ[R] MvPolynomial (Root m) R :=
  aeval fun x : Root m => rename (Sigma.mk x.1) (esymm (Fin (m x.1)) R (x.2 + 1))

theorem split_blockEsymm [DecidableEq ι] (τ₀ : ι) :
    (GlobalTheory.BlockSymm.splitEquiv R τ₀).toAlgHom.comp (blockEsymm R m) =
      ((aeval fun i : Fin (m τ₀) =>
          esymm (Fin (m τ₀)) (MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) (i + 1)).restrictScalars R).comp
        ((mapAlgHom (blockEsymm R (fun τ : {τ // τ ≠ τ₀} => m τ.1))).comp
          (GlobalTheory.BlockSymm.splitEquiv R τ₀).toAlgHom) := by
  ext ⟨τ, i⟩ : 1
  by_cases h : τ = τ₀
  · subst h
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, blockEsymm, aeval_X,
      GlobalTheory.BlockSymm.splitEquiv_X_self, mapAlgHom_apply, map_X, AlgHom.restrictScalars_apply]
    have hc : rename (Sigma.mk τ) (esymm (Fin (m τ)) R ((i : ℕ) + 1)) =
        GlobalTheory.BlockSymm.chernRootsOver R m (X (τ, (i : ℕ) + 1)) := by
      simp [GlobalTheory.BlockSymm.chernRootsOver]
    rw [hc, ← GlobalTheory.BlockSymm.splitEquiv_symm_esymm, AlgEquiv.apply_symm_apply]
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, blockEsymm, aeval_X,
      GlobalTheory.BlockSymm.splitEquiv_X_ne R τ₀ h, mapAlgHom_apply, map_C, AlgHom.restrictScalars_apply, aeval_C]
    simp [esymm, map_sum, map_prod, GlobalTheory.BlockSymm.splitEquiv_X_ne R τ₀ h]

end Esymm

theorem blockEsymm_injective (n : ℕ) : ∀ (ι : Type) [Fintype ι], Fintype.card ι = n →
    ∀ (R : Type) [CommRing R] (m : ι → ℕ), Function.Injective (blockEsymm R m) := by
  induction n with
  | zero =>
    intro ι _ hc R _ m
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    haveI : IsEmpty (Root m) := ⟨fun x => IsEmpty.false x.1⟩
    intro p q hpq
    rw [eq_C_of_isEmpty p, eq_C_of_isEmpty q] at hpq ⊢
    simp only [blockEsymm, aeval_C, algebraMap_eq] at hpq
    rw [hpq]
  | succ n ih =>
    intro ι _ hc R _ m
    classical
    obtain ⟨τ₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    have hc' : Fintype.card {τ // τ ≠ τ₀} = n := by
      simp [Fintype.card_subtype_compl, hc]
    let R' := MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R
    have h1 : Function.Injective (aeval (R := R') fun i : Fin (m τ₀) => esymm (Fin (m τ₀)) R' (i + 1)) := by
      intro p q hpq
      apply esymmAlgHom_fin_injective R' (m := m τ₀) (n := m τ₀) le_rfl
      apply Subtype.ext
      rw [esymmAlgHom_apply, esymmAlgHom_apply]
      exact hpq
    have h2 : Function.Injective (mapAlgHom (R := R) (σ := Fin (m τ₀))
        (blockEsymm R (fun τ : {τ // τ ≠ τ₀} => m τ.1))) := by
      intro p q hpq
      exact map_injective _ (ih _ hc' R _) hpq
    have key := split_blockEsymm R m τ₀
    intro p q hpq
    apply (GlobalTheory.BlockSymm.splitEquiv R τ₀).injective
    apply h2
    apply h1
    have := congrArg (fun F => F p) key
    have h' := congrArg (fun F => F q) key
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.restrictScalars_apply] at this h'
    rw [← this, ← h', hpq]

variable {ι : Type} (m : ι → ℕ)

def truncChern : MvPolynomial (ι × ℕ) ℝ →ₐ[ℝ] MvPolynomial (Root m) ℝ :=
  aeval fun x : ι × ℕ =>
    if x.2 = 0 then 1 else if h : x.2 - 1 < m x.1 then X (⟨x.1, ⟨x.2 - 1, h⟩⟩ : Root m) else 0

def liftChern : MvPolynomial (Root m) ℝ →ₐ[ℝ] MvPolynomial (ι × ℕ) ℝ :=
  aeval fun x : Root m => X (x.1, (x.2 : ℕ) + 1)

theorem chernRoots_eq_comp : chernRoots m = (blockEsymm ℝ m).comp (truncChern m) := by
  ext ⟨τ, k⟩ : 1
  simp only [AlgHom.comp_apply, truncChern, aeval_X]
  rcases k with _ | j
  · simp [chernRoots, esymm_zero]
  · by_cases h : j < m τ
    · simp [chernRoots, h, blockEsymm]
    · have hc : (Finset.univ : Finset (Fin (m τ))).card < j + 1 := by simp; omega
      simp [chernRoots, h, esymm, Finset.powersetCard_eq_empty.mpr hc]

def rankIdeal : Ideal (MvPolynomial (ι × ℕ) ℝ) :=
  Ideal.span ((Set.range fun τ : ι => (X (τ, 0) - 1 : MvPolynomial (ι × ℕ) ℝ)) ∪
    {P | ∃ (τ : ι) (k : ℕ), m τ < k ∧ P = X (τ, k)})

theorem mk_liftChern_truncChern :
    (Ideal.Quotient.mkₐ ℝ (rankIdeal m)).comp ((liftChern m).comp (truncChern m)) =
      Ideal.Quotient.mkₐ ℝ (rankIdeal m) := by
  ext ⟨τ, k⟩ : 1
  simp only [AlgHom.comp_apply, truncChern, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  rcases k with _ | j
  · simp only [if_true, map_one]
    rw [← map_one (Ideal.Quotient.mk (rankIdeal m)), Ideal.Quotient.eq]
    rw [← neg_mem_iff, neg_sub]
    exact Ideal.subset_span (Or.inl ⟨τ, rfl⟩)
  · by_cases h : j < m τ
    · simp [h, liftChern]
    · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, h, dif_neg, not_false_eq_true, map_zero]
      rw [eq_comm, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Or.inr ⟨τ, j + 1, by omega, rfl⟩)

theorem mem_span_of_chernRoots_eq_zero : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (ι × ℕ) ℝ),
    chernRoots m Q = 0 → Q ∈ Ideal.span ((Set.range fun τ : ι => (X (τ, 0) - 1 : MvPolynomial (ι × ℕ) ℝ)) ∪
      {P | ∃ (τ : ι) (k : ℕ), m τ < k ∧ P = X (τ, k)}) := by
  intro ι _ m Q hQ
  have h0 : truncChern m Q = 0 := by
    apply blockEsymm_injective _ ι rfl ℝ m
    rw [map_zero, ← AlgHom.comp_apply, ← chernRoots_eq_comp, hQ]
  have h1 := congrArg (fun F => F Q) (mk_liftChern_truncChern m)
  simp only [AlgHom.comp_apply, h0, map_zero, Ideal.Quotient.mkₐ_eq_mk] at h1
  exact (Ideal.Quotient.eq_zero_iff_mem).mp h1.symm

end GlobalTheory.GrassKernel
