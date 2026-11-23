import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLiftAt
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceInjectivity

theorem eq_or_conj_of_comap_eq {L : Type} [Field L] [NumberField L] [IsCMField L]
    (P P' : HeightOneSpectrum (𝓞 L))
    (h : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) =
      P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L))) :
    P' = P ∨ ∀ x : 𝓞 L, x ∈ P'.asIdeal ↔ IsCMField.ringOfIntegersComplexConj L x ∈ P.asIdeal := by
  set σ : 𝓞 L →+* 𝓞 L := (IsCMField.ringOfIntegersComplexConj L : 𝓞 L →+* 𝓞 L) with hσ
  have key : ∀ x ∈ P'.asIdeal, x ∈ P.asIdeal ∨ x ∈ P.asIdeal.comap σ := by
    intro x hx
    have hfix : IsCMField.complexConj L ((x * σ x : 𝓞 L) : L) = ((x * σ x : 𝓞 L) : L) := by
      simp [hσ, IsCMField.coe_ringOfIntegersComplexConj, mul_comm]
    obtain ⟨y, hy⟩ := (IsCMField.RingOfIntegers.complexConj_eq_self_iff (K := L) (x * σ x)).1 hfix
    have hy' : algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) y = x * σ x := RingOfIntegers.ext hy
    have h1 : y ∈ P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) := by
      rw [Ideal.mem_comap, hy']; exact P'.asIdeal.mul_mem_right _ hx
    rw [← h, Ideal.mem_comap, hy'] at h1
    rcases P.isPrime.mem_or_mem h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (by rw [Ideal.mem_comap]; exact h2)
  have hsub : (P'.asIdeal : Set (𝓞 L)) ⊆ (P.asIdeal : Set (𝓞 L)) ∪ (P.asIdeal.comap σ : Set (𝓞 L)) :=
    fun x hx => key x hx
  have hmax : P'.asIdeal.IsMaximal := P'.isMaximal
  rcases Ideal.subset_union.1 hsub with h3 | h3
  · left
    exact HeightOneSpectrum.ext (hmax.eq_of_le P.isPrime.ne_top h3)
  · right
    have hpr : (P.asIdeal.comap σ).IsPrime := Ideal.comap_isPrime σ P.asIdeal
    have he := hmax.eq_of_le hpr.ne_top h3
    intro x
    rw [he, Ideal.mem_comap]
    rfl

end GlobalTheory.PlaceInjectivity

namespace GlobalTheory.PlaceInjectivity

theorem not_mem_of_coprime {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (w : HeightOneSpectrum (𝓞 E)) (h1 : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) :
    ((q : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  have hco : IsCoprime ((p : ℤ)) ((q : ℤ)) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_natCast_natCast] using (Nat.coprime_primes hp hq).mpr hpq)
  have hco' : IsCoprime ((p : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) := by
    simpa using hco.map (Int.castRingHom (𝓞 E))
  exact Ideal.IsPrime.notMem_of_isCoprime_of_mem hco' h1

end GlobalTheory.PlaceInjectivity

namespace GlobalTheory.PlaceInj

theorem splitPlace_v_injective : ∀ (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E), (∀ k v, (s k v).w = D.naut.plGw k v) → Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v) := by
  intro D s hs ⟨k, v⟩ ⟨k', v'⟩ heq
  simp only at heq
  have hc : (D.naut.plGw k v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      (D.naut.plGw k' v').asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
    rw [← hs, ← hs, (s k v).w_under, (s k' v').w_under, heq]
  by_cases hk : k = k'
  · subst hk
    rcases GlobalTheory.PlaceInjectivity.eq_or_conj_of_comap_eq _ _ hc with h | h
    · have := D.naut.plGw_inj k h.symm
      subst this
      rfl
    · exfalso
      apply D.naut.plGw_nconj k v v'
      intro x y hxy
      have hconj : (IsCMField.ringOfIntegersComplexConj D.host.E y : D.host.E) = (x : D.host.E) := by
        rw [IsCMField.coe_ringOfIntegersComplexConj, hxy]
        apply D.host.φ₀.injective
        rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
        simp
      rw [h y, RingOfIntegers.ext hconj]
  · exfalso
    have hg : D.host.g k ≠ D.host.g k' := by
      fin_cases k <;> fin_cases k' <;> simp_all [D.host.g_ne, D.host.g_ne.symm]
    have h1 : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈
        (D.naut.plGw k v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      rw [Ideal.mem_comap, map_natCast]; exact D.naut.plGw_over k v
    rw [hc, Ideal.mem_comap, map_natCast] at h1
    exact GlobalTheory.PlaceInjectivity.not_mem_of_coprime (D.host.g_prime k') (D.host.g_prime k) hg.symm _
      (D.naut.plGw_over k' v') h1

end GlobalTheory.PlaceInj
