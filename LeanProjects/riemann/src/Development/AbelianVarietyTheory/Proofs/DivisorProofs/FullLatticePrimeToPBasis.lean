import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleLatticeBasisExists
open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt GlobalTheory.LieRead

namespace GlobalTheory.FullLatLocBasis

theorem exists_basis_primeTo_p : ∀ (K : Type) [Field K] [NumberField K] (g p : ℕ) [Fact p.Prime]
    (L : Submodule (𝓞 K) (Fin g → K)), Full L → ∃ (x : Fin g → Fin g → K) (s : ℕ), (∀ i, x i ∈ L) ∧
      LinearIndependent K x ∧ ¬ p ∣ s ∧ ∀ v ∈ L, (s : K) • v ∈ Submodule.span (𝓞 K) (Set.range x) := by
  intro K _ _ g p hp L hL
  classical
  obtain ⟨hfg, hsp⟩ := hL
  have hp' : p.Prime := hp.out
  obtain ⟨r, b, hli, hbL, hw⟩ := GlobalTheory.HomLocBasis.exists_basis_primeTo p hp'.pos L hfg

  have hLsp : ∀ w ∈ L, w ∈ Submodule.span K (Set.range b) := by
    intro w hwL
    obtain ⟨k, hk, hkw⟩ := hw w hwL
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hp'.one_lt.ne' ((Nat.coprime_zero_left _).1 hk)
    have h1 : k • w ∈ Submodule.span K (Set.range b) :=
      Submodule.span_le_restrictScalars (𝓞 K) K (Set.range b) hkw
    have h2 : ((k : K)⁻¹) • ((k : K) • w) ∈ Submodule.span K (Set.range b) := by
      refine Submodule.smul_mem _ _ ?_
      rw [Nat.cast_smul_eq_nsmul]; exact h1
    rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hk0), one_smul] at h2
  have htop : Submodule.span K (Set.range b) = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    exact fun w hwL => hLsp w hwL
  have hrg : r = g := by
    have := finrank_span_eq_card hli
    rw [htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at this
    exact this.symm
  subst hrg

  obtain ⟨T, hT⟩ := hfg
  have hTk : ∀ t ∈ T, ∃ k : ℕ, Nat.Coprime k p ∧ k • t ∈ Submodule.span (𝓞 K) (Set.range b) :=
    fun t ht => hw t (hT ▸ Submodule.subset_span ht)
  choose! k hkc hkm using hTk
  refine ⟨b, ∏ t ∈ T, k t, hbL, hli, ?_, ?_⟩
  · have hc : Nat.Coprime (∏ t ∈ T, k t) p := Nat.Coprime.prod_left fun t ht => hkc t ht
    exact (Nat.Prime.coprime_iff_not_dvd hp').1 hc.symm
  · intro v hv
    rw [← hT] at hv
    induction hv using Submodule.span_induction with
    | mem t ht =>
      rw [Nat.cast_smul_eq_nsmul, ← Finset.mul_prod_erase T k ht, mul_nsmul]
      exact Submodule.smul_of_tower_mem _ _ (hkm t ht)
    | zero => simp
    | add u w _ _ hu hw' => rw [smul_add]; exact add_mem hu hw'
    | smul a u _ hu => rw [smul_comm]; exact Submodule.smul_mem _ a hu

end GlobalTheory.FullLatLocBasis
