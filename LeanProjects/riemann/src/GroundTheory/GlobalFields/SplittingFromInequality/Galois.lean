import Mathlib
import GroundTheory.GlobalFields.SplittingFromInequality

namespace GroundTheory.Global

open IsDedekindDomain NumberField Filter Module AdeleBaseChange

noncomputable section

section Tower

variable {K K' L : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L]
  [NumberField L] [Algebra K K'] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]

omit [NumberField K] [NumberField L] in

theorem SplitsCompletely.of_liesOver {v : HeightOneSpectrum (𝓞 K)} (hv : SplitsCompletely L v)
    (v' : HeightOneSpectrum (𝓞 K')) [v'.asIdeal.LiesOver v.asIdeal] : SplitsCompletely L v' := by
  intro w hw
  have : w.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans w.asIdeal v'.asIdeal v.asIdeal
  obtain ⟨he, hf⟩ := hv w this
  rw [Ideal.ramificationIdx_tower (R := 𝓞 K) v'.asIdeal w.asIdeal] at he
  rw [Ideal.inertiaDeg_tower (R := 𝓞 K) v'.asIdeal w.asIdeal] at hf
  exact ⟨(mul_eq_one.1 he).2, (mul_eq_one.1 hf).2⟩

variable (K) in

theorem eventually_splitsCompletely_of_tower
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, SplitsCompletely L v) :
    ∀ᶠ v' : HeightOneSpectrum (𝓞 K') in cofinite, SplitsCompletely L v' :=
  ((tendsto_below (K := K) (L := K')).eventually h).mono fun v' hv' ↦ hv'.of_liesOver v'

end Tower

section Galois

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem FirstInequality.finrank_eq_one_of_eventually_splitsCompletely_of_isGalois
    (hFI : FirstInequality.{u})
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, SplitsCompletely L v) :
    finrank K L = 1 := by
  by_contra hne
  have hnt : Nontrivial Gal(L/K) := by
    rw [← Finite.one_lt_card_iff_nontrivial, IsGalois.card_aut_eq_finrank]
    have := finrank_pos (R := K) (M := L)
    omega
  obtain ⟨σ, hσ⟩ := exists_ne (1 : Gal(L/K))
  let H := Subgroup.zpowers σ
  have : IsCyclic Gal(L/IntermediateField.fixedField H) := by
    have e : H ≃* Gal(L/IntermediateField.fixedField H) :=
      (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField H).symm).trans
        (IntermediateField.fixingSubgroupEquiv _)
    have : IsCyclic H := Subgroup.isCyclic_zpowers σ
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have h1 := hFI.finrank_eq_one_of_eventually_splitsCompletely
    (eventually_splitsCompletely_of_tower K (K' := IntermediateField.fixedField H) h)
  rw [IntermediateField.finrank_fixedField_eq_card, Subgroup.card_eq_one] at h1
  exact hσ (Subgroup.mem_bot.1 (h1 ▸ Subgroup.mem_zpowers σ))

theorem FirstInequality.finrank_eq_one_of_splitsCompletely_of_finite_of_isGalois
    (hFI : FirstInequality.{u}) {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite)
    (h : ∀ v ∉ T, SplitsCompletely L v) :
    finrank K L = 1 :=
  hFI.finrank_eq_one_of_eventually_splitsCompletely_of_isGalois
    (eventually_cofinite.2 (hT.subset fun v hv ↦ by_contra fun hvT ↦ hv (h v hvT)))

end Galois

end

end GroundTheory.Global
