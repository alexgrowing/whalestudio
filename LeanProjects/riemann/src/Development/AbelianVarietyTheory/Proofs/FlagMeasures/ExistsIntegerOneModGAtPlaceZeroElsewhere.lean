import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CrtG

theorem gS_ne_zero (D : D7) : gS D ≠ 0 := by
  unfold gS; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

theorem exists_crt (D : D7) (p : PlF D) :
    ∃ a₀ : 𝓞 D.host.F,
      (∃ s : 𝓞 D.host.F, s ∉ p.asIdeal ∧ s * (a₀ - 1) ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.F)}) ∧
      ∀ p' : PlF D, p' ≠ p → ∃ s : 𝓞 D.host.F, s ∉ p'.asIdeal ∧
        s * a₀ ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.F)} := by
  set G : Ideal (𝓞 D.host.F) := Ideal.span {((gS D : ℕ) : 𝓞 D.host.F)} with hGdef
  have hG : G ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, hGdef, Ideal.span_singleton_eq_bot]
    exact_mod_cast gS_ne_zero D
  have hirr : Irreducible p.asIdeal := (Ideal.prime_of_isPrime p.ne_bot p.isPrime).irreducible
  obtain ⟨k, A, hA, hGA⟩ := WfDvdMonoid.max_power_factor hG hirr
  have hAp : ¬ A ≤ p.asIdeal := fun h => hA (Ideal.dvd_iff_le.2 h)
  have hsup : p.asIdeal ⊔ A = ⊤ := p.isMaximal.out.2 _ (left_lt_sup.2 hAp)
  have hcop : IsCoprime (p.asIdeal ^ k) A :=
    IsCoprime.pow_left ((Ideal.isCoprime_iff_sup_eq).2 hsup)
  obtain ⟨j, hj, a₀, ha₀, hja⟩ := (Ideal.isCoprime_iff_exists).1 hcop
  refine ⟨a₀, ?_, ?_⟩
  · obtain ⟨s, hsA, hsp⟩ := Set.not_subset.1 hAp
    refine ⟨s, hsp, ?_⟩
    have h1 : s * (a₀ - 1) = -(j * s) := by
      have : a₀ - 1 = -j := by rw [← hja]; ring
      rw [this]; ring
    rw [h1, hGA]
    exact neg_mem (Ideal.mul_mem_mul hj hsA)
  · intro p' hp'
    have hnot : ¬ p.asIdeal ^ k ≤ p'.asIdeal := by
      intro h
      have hle : p.asIdeal ≤ p'.asIdeal := p'.isPrime.le_of_pow_le h
      exact hp' (IsDedekindDomain.HeightOneSpectrum.ext
        (p.isMaximal.eq_of_le p'.isPrime.ne_top hle).symm)
    obtain ⟨s, hsk, hsp'⟩ := Set.not_subset.1 hnot
    refine ⟨s, hsp', ?_⟩
    rw [hGA]
    exact Ideal.mul_mem_mul hsk ha₀

end GlobalTheory.CrtG

namespace GlobalTheory.CrtG

theorem iE_div_g (D : D7) (p : PlF D) (y : 𝓞 D.host.F) (s : 𝓞 D.host.F) (hs : s ∉ p.asIdeal)
    (hy : s * y ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.F)}) :
    ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (algebraMap D.host.F D.host.E (y : D.host.F)) =
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hy
  have hg : ((gS D : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast gS_ne_zero D
  set x : D.host.E := algebraMap D.host.F D.host.E (y : D.host.F) / ((gS D : ℕ) : D.host.E) with hx
  have hcx : algebraMap D.host.F D.host.E (s : D.host.F) * x = algebraMap D.host.F D.host.E (c : D.host.F) := by
    have h2 : ((c * ((gS D : ℕ) : 𝓞 D.host.F) : 𝓞 D.host.F) : D.host.F) = ((s * y : 𝓞 D.host.F) : D.host.F) := by
      rw [hc]
    push_cast at h2
    have h3 := congrArg (algebraMap D.host.F D.host.E) h2
    simp only [map_mul, map_natCast] at h3
    rw [hx, mul_div_assoc', div_eq_iff hg, ← h3]
  have hint : IsIntegral ℤ (algebraMap D.host.F D.host.E (s : D.host.F) * x) := by
    rw [hcx]
    exact (RingOfIntegers.isIntegral_coe c).map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
  refine ⟨(D.s.atP p).ιE x, (Formalism.L2.SG.Pf.LocalDenominators.iE_mem_O_iff_D p x).2 ⟨s, hs, hint⟩, ?_⟩
  rw [← map_mul, hx, mul_div_cancel₀ _ hg]

theorem exists_one_here_zero_elsewhere : ∀ (D : D7) (p : PlF D), ∃ a : 𝓞 D.host.E, (∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (a : D.host.E) - 1 = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o) ∧ ∀ p' : PlF D, p' ≠ p → ∃ o ∈ (D.s.atP p').O, (D.s.atP p').ιE (a : D.host.E) = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) * o := by
  intro D p
  obtain ⟨a₀, ⟨s, hs, h1⟩, h2⟩ := exists_crt D p
  have hint : IsIntegral ℤ (algebraMap D.host.F D.host.E (a₀ : D.host.F)) :=
    (RingOfIntegers.isIntegral_coe a₀).map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
  refine ⟨⟨algebraMap D.host.F D.host.E (a₀ : D.host.F), hint⟩, ?_, ?_⟩
  · obtain ⟨o, ho, he⟩ := iE_div_g D p (a₀ - 1) s hs h1
    refine ⟨o, ho, ?_⟩
    rw [← he]
    simp
    rfl
  · intro p' hp'
    obtain ⟨s', hs', h'⟩ := h2 p' hp'
    exact iE_div_g D p' a₀ s' hs' h'

end GlobalTheory.CrtG
