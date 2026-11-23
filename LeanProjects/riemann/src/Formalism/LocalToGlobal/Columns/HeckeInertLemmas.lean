import Formalism.LocalToGlobal.Columns.HeckeInert
import Formalism.LocalToGlobal.Columns.GSetLemmas
import Formalism.LocalToGlobal.Columns.UnipotentRightActionFunctionsW

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module Pointwise

section Fin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem DecoSet.inertSet_finite {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) (s : List ℕ) (d : DecoSet E n ST SG) :
    (d.inertSet P s).Finite := by
  have hPk : P ^ s.sum ≠ ⊥ := pow_ne_zero _ hP
  obtain ⟨a, haP, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPk
  have hI : Ideal.span {a} * P ^ s.sum ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨fun h => ha (Ideal.span_singleton_eq_bot.1 h), hPk⟩
  have hfin := finite_between ((Ideal.span {a} * P ^ s.sum) • d.1.N) d.1.N
    (finite_quot_smul d.1.N d.2.lat.fg _ hI)
  refine Set.Finite.of_injOn (f := fun e : DecoSet E n ST SG => Ideal.span {a} • e.1.N) ?_ ?_ hfin
  · intro e he
    obtain ⟨h1, h2⟩ := he.1.smul_le
    refine ⟨?_, ?_⟩
    · rw [mul_smul]
      exact Submodule.smul_mono le_rfl h1
    · exact (Submodule.smul_mono ((Ideal.span_singleton_le_iff_mem _).2 haP) le_rfl).trans h2
  · intro e he e' he' h
    have hN : e.1.N = e'.1.N := by
      simp only [Submodule.ideal_span_singleton_smul] at h
      have hinj : Function.Injective fun x : Sp E n => a • x := smul_right_injective (Sp E n) ha
      have hsub : ∀ A B : Submodule (𝓞 E) (Sp E n), a • A = a • B → A ≤ B := by
        intro A B hAB x hx
        have : a • x ∈ a • B := hAB ▸ Submodule.smul_mem_pointwise_smul x a A hx
        obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 this
        rwa [← hinj hyx]
      exact le_antisymm (hsub _ _ h) (hsub _ _ h.symm)
    exact Subtype.ext (Deco.ext hN (he.2.1.trans he'.2.1.symm) (he.2.2.trans he'.2.2.symm))

theorem DecoSet.mem_inertNb {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) (s : List ℕ) (d e : DecoSet E n ST SG) :
    e ∈ d.inertNb P s ↔ e ∈ d.inertSet P s := by
  unfold DecoSet.inertNb
  rw [dif_pos (DecoSet.inertSet_finite hP s d), Set.Finite.mem_toFinset]

theorem DecoSet.sum_inertNb_smul {M : Type} [AddCommMonoid M] (P : Ideal (𝓞 E)) (s : List ℕ)
    (g : UF E n × GLG E n SG) (d : DecoSet E n ST SG) (ψ : DecoSet E n ST SG → M) :
    ∑ e ∈ (g • d).inertNb P s, ψ e = ∑ e ∈ d.inertNb P s, ψ (g • e) := by
  symm
  exact Finset.sum_equiv (MulAction.toPerm g) (fun e => (DecoSet.smul_mem_inertNb_iff g).symm) (fun e _ => rfl)

end Fin

section Op

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

end Op

end Formalism.L2.Col
