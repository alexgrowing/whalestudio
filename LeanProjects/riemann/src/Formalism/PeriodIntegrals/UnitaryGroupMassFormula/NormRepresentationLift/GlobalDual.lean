import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.ResidueOnto

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField IsDedekindDomain Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem global_dual (Λ : Submodule (𝓞 E) S.V) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hint : IntLat Λ)
    (e : Fin r → S.V) (hind : LinearIndependent E e) (he : ∀ i, e i ∈ Λ) (g : 𝓞 E)
    (hlocg : ∀ P : HeightOneSpectrum (𝓞 E), g ∈ P.asIdeal → ∀ x ∈ Λ, x ∈ Submodule.span E (Set.range e) →
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Submodule.span (𝓞 E) (Set.range e))
    (c : Fin r) :
    ∃ y ∈ Λ, (∀ i, i ≠ c → S.hT y (e i) = 0) ∧ ∃ q : 𝓞 E, S.hT y (e c) = ((1 + g * q : 𝓞 E) : E) := by
  let J : Ideal (𝓞 E) :=
    { carrier := {o | ∃ y ∈ Λ, (∀ i, i ≠ c → S.hT y (e i) = 0) ∧ S.hT y (e c) = (o : E)}
      zero_mem' := ⟨0, Λ.zero_mem, fun i _ => by simp, by simp⟩
      add_mem' := by
        rintro o o' ⟨y, hy, h0, ho⟩ ⟨y', hy', h0', ho'⟩
        refine ⟨y + y', Λ.add_mem hy hy', fun i hi => ?_, ?_⟩
        · simp [h0 i hi, h0' i hi]
        · simp [ho, ho']
      smul_mem' := by
        rintro κ o ⟨y, hy, h0, ho⟩
        refine ⟨cj κ • y, Λ.smul_mem _ hy, fun i hi => ?_, ?_⟩
        · rw [hT_cj_left, h0 i hi, mul_zero]
        · rw [hT_cj_left, ho, smul_eq_mul]; push_cast; rfl }
  have htop : J ⊔ Ideal.span {g} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hMbot : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
    let P : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, hMbot⟩
    have hg : g ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
    obtain ⟨y, hy, h0, o, ho, hoP⟩ := exact_dual Λ hU hint e hind he P (hlocg P hg) c
    exact hoP (hle (Ideal.mem_sup_left ⟨y, hy, h0, ho⟩))
  have h1 : (1 : 𝓞 E) ∈ J ⊔ Ideal.span {g} := by rw [htop]; trivial
  obtain ⟨j, hj, x, hx, hjx⟩ := Submodule.mem_sup.mp h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  obtain ⟨y, hy, h0, ho⟩ := hj
  refine ⟨y, hy, h0, -a, ?_⟩
  rw [ho]
  have : j = 1 + g * -a := by rw [← hjx]; ring
  rw [this]

end PI.NRL
