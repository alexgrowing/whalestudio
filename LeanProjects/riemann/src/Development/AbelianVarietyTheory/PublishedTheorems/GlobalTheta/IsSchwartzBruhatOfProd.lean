import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfTR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.Published.SiegelOneVector

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def IsSchwartzArch {M n : ℕ} (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) : Prop :=
  ∃ (N : ℕ) (e : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)),
    Continuous e ∧ Continuous e.symm ∧ ∃ f : SchwartzMap (Fin N → ℝ) ℂ, ∀ X, Φinf X = f (e X)

def IsSchwartzBruhat {M n : ℕ} (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) : Prop :=
  ∃ (k : ℕ) (Φinf : Fin k → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : Fin k → (Fin n → Fin M → Af F ⊗[F] E) → ℂ),
    (∀ i, IsSchwartzArch (Φinf i)) ∧ (∀ i, IsSB (Φf i)) ∧
      ∀ X, Φ X = ∑ i, Φinf i (projInf X) * Φf i (projFin X)

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def thetaTerm (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) : ℂ :=
  Φ (h⁻¹ • ratTup (F := F) (AF F) x)

def theta (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (h : HA (AF F) σ J) : ℂ :=
  ∑' x : Fin 1 → Fin M → E, thetaTerm σ J Φ h x

def eisIntegrand (ψ : AddChar (AF F) ℂ) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (b : F)
    (x : Fin 1 → Fin M → AF F ⊗[F] E) : ℂ :=
  Φ x * ψ (algebraMap F (AF F) b * qR (AF F) σ J (x 0))

def eisTerm (ψ : AddChar (AF F) ℂ) (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E))
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (b : F) : ℂ :=
  ∫ x, eisIntegrand σ J ψ Φ b x ∂dx

def eisSeries (ψ : AddChar (AF F) ℂ) (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E))
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) : ℂ :=
  Φ 0 + ∑' b : F, eisTerm σ J ψ dx Φ b

def ThetaConverges (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J))
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) : Prop :=
  (∀ h, Summable fun x => ‖thetaTerm σ J Φ h x‖) ∧
    ∫⁻ h in 𝓕, ∑' x, ‖thetaTerm σ J Φ h x‖ₑ ∂μ < ⊤ ∧ IntegrableOn (theta σ J Φ) 𝓕 μ

def EisConverges (ψ : AddChar (AF F) ℂ) (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E))
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) : Prop :=
  (∀ b, Integrable (eisIntegrand σ J ψ Φ b) dx) ∧ Summable fun b => ‖eisTerm σ J ψ dx Φ b‖

end Defs

end GlobalTheory.Published.SiegelOneVector

namespace GlobalTheory.Published

open SiegelOneVector

def WeilSiegelOneVector : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 2 < M →
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
    AllSome (SdW F E σ M J (AF F) ψ 1) fun dx =>
    ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)),
      μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → μ 𝓕 = 1 →
    ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ, IsSchwartzBruhat Φ →
      ThetaConverges σ J μ 𝓕 Φ ∧ EisConverges σ J ψ dx Φ ∧
        ∫ h in 𝓕, theta σ J Φ h ∂μ = eisSeries σ J ψ dx Φ

end GlobalTheory.Published

namespace GlobalTheory.Published.SiegelOneVector

section Inhabitants

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isSchwartzBruhat_of_prod {M n : ℕ} {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ}
    {Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ} {Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ}
    (hi : IsSchwartzArch Φinf) (hf : IsSB Φf) (h : IsProdInfFin Φ Φinf Φf) : IsSchwartzBruhat Φ :=
  ⟨1, fun _ => Φinf, fun _ => Φf, fun _ => hi, fun _ => hf, fun X => by simp [h X]⟩

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem normalise (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ) :
    μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ ((μ 𝓕)⁻¹ • μ).IsHaarMeasure ∧
      IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 ((μ 𝓕)⁻¹ • μ) ∧ ((μ 𝓕)⁻¹ • μ) 𝓕 = 1 := by
  have h0 : μ 𝓕 ≠ 0 := ((GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary F E σ M J μ hμ).2 𝓕 𝓕 h𝓕 h𝓕).2
  have h1 : μ 𝓕 ≠ ⊤ := (GlobalTheory.Mem.VolFin.finVol F E σ hCM M J hJ μ hμ 𝓕 h𝓕).ne
  refine ⟨h0, h1, Measure.IsHaarMeasure.smul μ (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0),
    h𝓕.mono Measure.smul_absolutelyContinuous, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 h1]

theorem exists_normalised (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) :
    ∃ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)),
      μ.IsHaarMeasure ∧ IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ ∧ μ 𝓕 = 1 := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).1
  have hμ : (Measure.haar : Measure (HA (AF F) σ J)).IsHaarMeasure := inferInstance
  obtain ⟨𝓕, h𝓕⟩ := (GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary F E σ M J _ hμ).1
  obtain ⟨-, -, h1, h2, h3⟩ := normalise σ J hCM hJ _ 𝓕 hμ h𝓕
  exact ⟨_, 𝓕, h1, h2, h3⟩

end Inhabitants

end GlobalTheory.Published.SiegelOneVector
