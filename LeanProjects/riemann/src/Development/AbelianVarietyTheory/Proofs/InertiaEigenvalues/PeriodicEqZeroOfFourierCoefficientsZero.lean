import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralFundamentalDomainEqMassMulAverageStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

variable {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι]

theorem dot_add_right (ξ : ι → E) (x y : ι → Ad E) : dot ξ (x + y) = dot ξ x + dot ξ y := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_add_left (ξ η : ι → E) (x : ι → Ad E) : dot (ξ + η) x = dot ξ x + dot η x := by
  simp only [dot, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem dot_zero_left (x : ι → Ad E) : dot (0 : ι → E) x = 0 := by
  simp [dot]

theorem dot_rat (ξ c : ι → E) :
    dot ξ (fun t => algebraMap E (Ad E) (c t)) = algebraMap E (Ad E) (∑ t, ξ t * c t) := by
  simp only [dot, map_sum, map_mul]

theorem dot_single [DecidableEq ι] (t : ι) (c : E) (x : ι → Ad E) :
    dot (Pi.single t c) x = algebraMap E (Ad E) c * x t := by
  rw [dot, Finset.sum_eq_single t]
  · simp
  · intro s _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

theorem StdPsi.forall_dot_eq_one_iff {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (x : ι → Ad E) :
    (∀ ξ : ι → E, ψ (-dot ξ x) = 1) ↔ x ∈ ratV E ι := by
  classical
  constructor
  · intro h
    have hx : ∀ t, ∃ d : E, x t = algebraMap E (Ad E) d := by
      intro t
      refine hψ.ann _ fun c => ?_
      have h1 := h (Pi.single t c)
      rw [dot_single, AddChar.map_neg_eq_inv, inv_eq_one] at h1
      rwa [mul_comm]
    choose d hd using hx
    exact ⟨d, funext fun t => (hd t).symm⟩
  · rintro ⟨c, rfl⟩ ξ
    have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom ι) c =
        fun t => algebraMap E (Ad E) (c t) := rfl
    rw [e, dot_rat, AddChar.map_neg_eq_inv, hψ.rat, inv_one]

theorem StdPsi.per_twist {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {Φ : (ι → Ad E) → ℂ} (hΦ : Per (ratV E ι) Φ)
    (ξ : ι → E) : Per (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x) := by
  refine ⟨(hψ.cont.comp (continuous_dot ξ).neg).mul hΦ.1, ?_⟩
  rintro _ ⟨c, rfl⟩ x
  have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom ι) c =
      fun t => algebraMap E (Ad E) (c t) := rfl
  have h2 := hΦ.2 _ ⟨c, rfl⟩ x
  simp only
  rw [h2, AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv, e, hψ.map_dot ξ c x]

theorem eq_zero_of_avg_character_eq_zero : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι]
    (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ Φ : (ι → Ad E) → ℂ, Per (ratV E ι) Φ →
    (∀ ξ : ι → E, avg (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x) = 0) → Φ = 0 := by
  intro E _ _ ι _ ψ hψ Φ hΦ hco
  letI : MeasurableSpace (ι → Ad E) := borel _
  haveI : BorelSpace (ι → Ad E) := ⟨rfl⟩
  have hL := isCoLat_ratV E ι
  obtain ⟨hd, K, hK, hcov⟩ := id hL
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice (ι → Ad E) (ratV E ι) hL
  haveI := hd
  refine GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (ι → Ad E) (ratV E ι) K hK hcov (ι → E)
    (fun ξ x => ψ (-dot ξ x)) (fun ξ => hψ.cont.comp (continuous_dot ξ).neg) ?_ ?_ ?_
    (fun ξ x => hψ.norm _) (hψ.forall_dot_eq_one_iff) μ 𝓕 hμ h𝓕 Φ hΦ.1 hΦ.2 ?_
  · intro ξ x y
    rw [dot_add_right, neg_add, AddChar.map_add_eq_mul]
  · intro ξ η x
    rw [dot_add_left, neg_add, AddChar.map_add_eq_mul]
  · intro x
    rw [dot_zero_left, neg_zero, AddChar.map_zero_eq_one]
  · intro ξ
    have h2 := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average (ι → Ad E) (ratV E ι) hL μ 𝓕 hμ h𝓕 _ (hψ.per_twist hΦ ξ)).2.2.2
    rw [h2, hco ξ, mul_zero]

end GlobalTheory.CuspGeneric
