import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.NonarchimedeanSelfdualMeasurePi

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

section Abstract

variable {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]

theorem integral_indicator_char_of_trivial (μ : Measure G) (H : AddSubgroup G)
    (hH : MeasurableSet (H : Set G)) (χ : G → ℂ) (h1 : ∀ x ∈ H, χ x = 1) :
    ∫ x, (H : Set G).indicator χ x ∂μ = ((μ (H : Set G)).toReal : ℂ) := by
  rw [integral_indicator hH, setIntegral_congr_fun hH (g := fun _ => (1 : ℂ)) (fun x hx => h1 x hx)]
  simp [Measure.real]

theorem integral_indicator_char_of_ne (μ : Measure G) [μ.IsAddLeftInvariant] (H : AddSubgroup G)
    (χ : G → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y) {h : G} (hh : h ∈ H) (hne : χ h ≠ 1) :
    ∫ x, (H : Set G).indicator χ x ∂μ = 0 := by
  have key : ∀ x, (H : Set G).indicator χ (x + h) = (H : Set G).indicator χ x * χ h := by
    intro x
    by_cases hx : x ∈ H
    · have hxh : x + h ∈ H := H.add_mem hx hh
      rw [Set.indicator_of_mem (by exact hxh), Set.indicator_of_mem (by exact hx), hχ]
    · have hxh : x + h ∉ H := fun hc => hx (by simpa using H.sub_mem hc hh)
      rw [Set.indicator_of_notMem (by exact hxh), Set.indicator_of_notMem (by exact hx), zero_mul]
  have h2 := integral_add_right_eq_self (μ := μ) ((H : Set G).indicator χ) h
  simp only [key] at h2
  rw [integral_mul_const] at h2
  have h3 : (∫ x, (H : Set G).indicator χ x ∂μ) * (χ h - 1) = 0 := by
    rw [mul_sub, h2, mul_one, sub_self]
  exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hne)

end Abstract

variable {F : Type} [Field F] [NumberField F]

def psiF (ψ : AddChar (AF F) ℂ) (y : Af F) : ℂ := ψ (pairA F 0 y)

def annV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (U : Set (Fv F v)) : Set (Fv F v) :=
  {t | ∀ s ∈ U, psiV F ψ v (s * t) = 1}

def annF (ψ : AddChar (AF F) ℂ) (B : Set (Af F)) : Set (Af F) :=
  {b | ∀ y ∈ B, psiF ψ (y * b) = 1}

def fouInf (ψ : AddChar (AF F) ℂ) (lam : Measure (Ainf F)) (ρ : Ainf F → ℝ) (t : Ainf F) : ℂ :=
  ∫ x, (ρ x : ℂ) * psiInf F ψ (x * t) ∂lam

theorem psiF_add (ψ : AddChar (AF F) ℂ) (x y : Af F) : psiF ψ (x + y) = psiF ψ x * psiF ψ y := by
  have h : pairA F 0 (x + y) = pairA F 0 x + pairA F 0 y := Prod.ext (add_zero (0 : Ainf F)).symm rfl
  rw [psiF, h, AddChar.map_add_eq_mul]
  rfl

theorem psiF_zero (ψ : AddChar (AF F) ℂ) : psiF ψ 0 = 1 := by
  have h : pairA F 0 (0 : Af F) = 0 := rfl
  rw [psiF, h, AddChar.map_zero_eq_one]

theorem psiF_singleV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) :
    psiF ψ (singleV F v s) = psiV F ψ v s := rfl

theorem psi_pairA (ψ : AddChar (AF F) ℂ) (x : Ainf F) (y : Af F) :
    ψ (pairA F x y) = psiInf F ψ x * psiF ψ y := by
  have h : pairA F x y = pairA F x 0 + pairA F 0 y :=
    Prod.ext (add_zero x).symm (zero_add y).symm
  rw [h, AddChar.map_add_eq_mul]
  rfl

theorem psiV_zero (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : psiV F ψ v 0 = 1 := by
  classical
  have h : singleV F v (0 : Fv F v) = 0 := RestrictedProduct.single_zero _ v
  rw [← psiF_singleV, h, psiF_zero]

theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y :=
  GlobalTheory.CompanionTheory.SW.PiV.psiV_add ψ v x y

theorem psiV_neg_of_eq_one (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) {x : Fv F v}
    (hx : psiV F ψ v x = 1) : psiV F ψ v (-x) = 1 := by
  have h := psiV_add ψ v (-x) x
  rw [neg_add_cancel, psiV_zero, hx, mul_one] at h
  exact h.symm

def annS (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (U : Set (Fv F v)) :
    AddSubgroup (Fv F v) where
  carrier := annV ψ v U
  add_mem' := by
    intro a b ha hb s hs
    rw [mul_add, psiV_add, ha s hs, hb s hs, one_mul]
  zero_mem' := by
    intro s _
    rw [mul_zero, psiV_zero]
  neg_mem' := by
    intro a ha s hs
    rw [mul_neg]
    exact psiV_neg_of_eq_one ψ v (ha s hs)

theorem coe_annS (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (U : Set (Fv F v)) :
    (annS ψ v U : Set (Fv F v)) = annV ψ v U := rfl

def boxS (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fv F v)) :
    AddSubgroup (Af F) where
  carrier := Coef.boxA S fun v => (U v : Set (Fv F v))
  add_mem' := by
    intro a b ha hb
    exact ⟨fun v hv => (U v).add_mem (ha.1 v hv) (hb.1 v hv),
      fun v hv => add_mem (ha.2 v hv) (hb.2 v hv)⟩
  zero_mem' := ⟨fun v _ => (U v).zero_mem, fun v _ => zero_mem _⟩
  neg_mem' := by
    intro a ha
    exact ⟨fun v hv => (U v).neg_mem (ha.1 v hv),
      fun v hv => neg_mem (ha.2 v hv)⟩

theorem coe_boxS (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fv F v)) :
    (boxS S U : Set (Af F)) = Coef.boxA S fun v => (U v : Set (Fv F v)) := rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
