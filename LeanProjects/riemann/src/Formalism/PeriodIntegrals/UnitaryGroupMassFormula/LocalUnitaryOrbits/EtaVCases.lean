import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OBas1OfUnitV

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

abbrev IE : Ideal (𝓞 E) := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))

abbrev QE : Type := 𝓞 E ⧸ IE (E := E) v

def sigO : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)

theorem sigO_coe (x : 𝓞 E) : (sigO σ x : E) = σ (x : E) := rfl

theorem sigO_alg (a : 𝓞 F) : sigO σ (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
  apply RingOfIntegers.ext
  rw [sigO_coe]
  show σ (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)) = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 F) F E]
  exact σ.commutes _

theorem IE_le : IE (E := E) v ≤ (IE (E := E) v).comap (sigO σ) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]
  have hc : (sigO σ).comp (algebraMap (𝓞 F) (𝓞 E)) = algebraMap (𝓞 F) (𝓞 E) := RingHom.ext (sigO_alg σ)
  rw [hc]

def sigQ : QE (E := E) v →+* QE (E := E) v := Ideal.quotientMap (IE (E := E) v) (sigO σ) (IE_le σ v)

theorem sigQ_mk (x : 𝓞 E) : sigQ σ v (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (sigO σ x) := rfl

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem sigQ_sigQ (h : IsCMExt F E σ) (x : QE (E := E) v) : sigQ σ v (sigQ σ v x) = x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [sigQ_mk, sigQ_mk]
  congr 1
  apply RingOfIntegers.ext
  simp only [sigO_coe]
  exact sig_sig σ h _

theorem sigQ_alg (c : 𝓞 F ⧸ v.asIdeal) :
    sigQ σ v (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c) = algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient, sigQ_mk, sigO_alg]

def ResQ : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∃ ρ : OR (E := E) v →+* QE (E := E) v, IsRes σ v ϖ (sigQ σ v) ρ

def EtaLink : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → (etaV (E := E) v = 1 ↔ ¬ (IE (E := E) v).IsPrime)

def QInert : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → (IE (E := E) v).IsPrime → sigQ σ v ≠ RingHom.id _

def QSplit : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ¬ (IE (E := E) v).IsPrime →
    ∃ e : QE (E := E) v ≃+* (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal), ∀ x, e (sigQ σ v x) = (e x).swap

theorem card_res : Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem finite_res : Finite (𝓞 F ⧸ v.asIdeal) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_res]
  exact fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)

theorem IE_ne_bot : IE (E := E) v ≠ ⊥ := by
  exact Ideal.map_ne_bot_of_ne_bot v.ne_bot

end PI.OmLocU.Red
