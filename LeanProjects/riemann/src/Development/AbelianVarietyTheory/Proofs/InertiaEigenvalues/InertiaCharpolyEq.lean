import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective

noncomputable section

namespace GlobalTheory.IneAway

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem placesOver_finite_of_prime (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 hw

theorem isoLoc_cusp (D : D7) {a : ℕ} (π : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, π, 1⟩] w = D.naut.locG π w := by
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

theorem charpoly_inertia : ∀ D : D7, GalAway D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), ((ρ s : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map (iotaO D.nd D.naut i) = D.naut.inePol (D.naut.locG π w) s := by
  intro D hG hF i π ρ hc ha hρ w hw s hs
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.two_le_m
    simp only [Ranks.r]
    omega
  obtain ⟨r, hrc, hr⟩ := hG i D.R.r hr1 π hc ha
  obtain ⟨hιc, -⟩ := GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i
  obtain ⟨hρc, -, hρf⟩ := hρ
  have hcomp : iotaO D.nd D.naut i = (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) := rfl
  have hinj : Function.Injective (Polynomial.map (D.naut.iotaQC i).toRingHom) :=
    Polynomial.map_injective _ (D.naut.iotaQC i).injective
  have hfin := placesOver_finite_of_prime D.host.E (D.nd.lPrime i).out
  have hall := (hfin.eventually_cofinite_notMem.and (D.naut.locG_unr_ae π)).and hρf
  have hd := hF _ (Filter.eventually_cofinite.1 hall)
  have key := GlobalTheory.TypeLeaf.charpoly_eq_of_dense _ (Qbar (D.nd.l i)) D.R.r
    (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaOQ D.nd D.naut i))
    (fun g => ((r g : GL (Fin D.R.r) (Qbar (D.nd.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i))))
    _ hd (hρc.matrix_map hιc) hrc (by
      rintro g ⟨v, hv, -, B, hB, hg⟩
      obtain ⟨⟨h1, h2⟩, h3⟩ := not_not.1 hv
      apply hinj
      have hu : D.naut.unr (D.naut.wdOf i r v) := by
        rw [hr v h1]; exact (D.naut.unr_tw _ _).2 h2
      rw [Matrix.charpoly_map, Polynomial.map_map, ← hcomp, h3 B g hB hg, isoLoc_cusp,
        D.naut.wdOf_frob i r v h1 hrc hu B g hB hg, hr v h1]
      rfl) s
  rw [hcomp, ← Polynomial.map_map, ← Matrix.charpoly_map, key, D.naut.wdOf_ine i r w hw hrc s hs, hr w hw,
    D.naut.inePol_tw _ _ _ hs]

end GlobalTheory.IneAway
