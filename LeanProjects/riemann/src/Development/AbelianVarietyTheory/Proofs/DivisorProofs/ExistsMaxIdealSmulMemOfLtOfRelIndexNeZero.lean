import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem exists_maxIdeal_smul_mem_of_lt_of_relIndex_ne_zero (F V : Type) [Field F] [NumberField F]
    [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
    (N₀ N : Submodule (𝓞 F) V) (hlt : N₀ < N)
    (hidx : N₀.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0) :
    ∃ (u : V) (p : Ideal (𝓞 F)), p.IsMaximal ∧ u ∈ N ∧ u ∉ N₀ ∧ ∀ π ∈ p, π • u ∈ N₀ := by
  classical
  set P : Submodule (𝓞 F) N := N₀.comap N.subtype with hP
  have hPne : P ≠ ⊤ := by
    intro h
    obtain ⟨v, hvN, hvN₀⟩ := SetLike.exists_of_lt hlt
    have hv : (⟨v, hvN⟩ : N) ∈ P := h ▸ Submodule.mem_top
    exact hvN₀ hv
  haveI : Nontrivial (N ⧸ P) := Submodule.Quotient.nontrivial_iff.2 hPne
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty (𝓞 F) (N ⧸ P)
  obtain ⟨hprime, x, hx⟩ := (isAssociatedPrime_iff (R := 𝓞 F) (M := N ⧸ P)).1 hp
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P x
  have hmem : ∀ r : 𝓞 F, r ∈ p ↔ r • (y : V) ∈ N₀ := by
    intro r
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, hP, Submodule.mem_comap]
    rfl
  set n := N₀.toAddSubgroup.relIndex N.toAddSubgroup with hn
  have hkill : n • (y : V) ∈ N₀ := by
    have h := AddSubgroup.nsmul_index_mem (N₀.toAddSubgroup.addSubgroupOf N.toAddSubgroup)
      (⟨y.1, y.2⟩ : N.toAddSubgroup)
    exact AddSubgroup.mem_addSubgroupOf.1 h
  have hnp : ((n : ℕ) : 𝓞 F) ∈ p := by
    rw [hmem, Nat.cast_smul_eq_nsmul]
    exact hkill
  have hp0 : p ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hnp
    exact hidx (by exact_mod_cast hnp)
  refine ⟨(y : V), p, Ideal.IsPrime.isMaximal hprime hp0, y.2, ?_, fun π hπ => (hmem π).1 hπ⟩
  intro hy
  apply hprime.ne_top
  rw [eq_top_iff]
  intro r _
  rw [hmem]
  exact N₀.smul_mem r hy

end GlobalTheory
