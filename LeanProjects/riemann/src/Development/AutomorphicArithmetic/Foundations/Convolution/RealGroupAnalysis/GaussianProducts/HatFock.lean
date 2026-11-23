import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HermAdel
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.FinHat

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.G.FockHat

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private def Ind (m : V4 F → ℂ) : Prop := ∀ v s, m (Function.update v 1 s) = m v

private def mon (e : InfinitePlace F → ℕ) (s : A F) : ℂ := ∏ w, ((TR.pInf F s w : ℝ) : ℂ) ^ e w

private def gE (s : A F) : ℂ := Complex.exp (-(Real.pi : ℂ) * ((∑ w, TR.pInf F s w ^ 2 : ℝ) : ℂ))

private def gR (δ : F) (v : V4 F) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * ((∑ w, TR.pInf F (v 0 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)) w : ℝ) : ℂ))

private theorem gauss_split (δ : F) (v : V4 F) : gauss δ v = gR δ v * gE (v 1) := by
  have h : (∑ w, TR.pInf F (v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)) w : ℝ) =
      (∑ w, TR.pInf F (v 0 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)) w) + ∑ w, TR.pInf F (v 1) w ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    have e : v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2) =
        (v 0 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)) + v 1 ^ 2 := by ring
    rw [e, map_add, map_pow]
    rfl
  rw [gauss, gR, gE, ← Complex.exp_add, h]
  push_cast
  ring_nf

private theorem gR_update (δ : F) (v : V4 F) (s : A F) : gR δ (Function.update v 1 s) = gR δ v := by
  have h0 : Function.update v 1 s 0 = v 0 := Function.update_of_ne (by decide) _ _
  have h2 : Function.update v 1 s 2 = v 2 := Function.update_of_ne (by decide) _ _
  have h3 : Function.update v 1 s 3 = v 3 := Function.update_of_ne (by decide) _ _
  simp only [gR, h0, h2, h3]

private theorem finPart_update (v : V4 F) (s : A F) :
    finPartPi (Function.update v 1 s) = Function.update (finPartPi v) 1 s.2 := by
  funext i
  by_cases h : i = 1
  · subst h; simp [finPartPi]
  · simp [finPartPi, Function.update_of_ne h]

private theorem mon_add (e₁ e₂ : InfinitePlace F → ℕ) (s : A F) :
    mon (e₁ + e₂) s = mon e₁ s * mon e₂ s := by
  simp [mon, pow_add, Finset.prod_mul_distrib]

private theorem mon_zero (s : A F) : mon (0 : InfinitePlace F → ℕ) s = 1 := by
  simp [mon]

private theorem mon_single (w : InfinitePlace F) (s : A F) :
    mon (Pi.single w 1) s = ((TR.pInf F s w : ℝ) : ℂ) := by
  rw [mon, Finset.prod_eq_single w]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

private def Good (δ : F) (χ : V4 F → ℂ) : Prop :=
  (∀ v, Integrable (fun s => χ (Function.update v 1 s) * ψ (-(s * v 1))) (adeleMeasure F)) ∧
    hat χ ∈ FockFn δ

private theorem good_zero (δ : F) : Good δ (0 : V4 F → ℂ) := by
  refine ⟨fun v => by simpa using integrable_zero _ _ _, ?_⟩
  have : hat (0 : V4 F → ℂ) = 0 := by
    funext v
    simp [hat]
  rw [this]
  exact zero_mem _

private theorem good_add {δ : F} {χ₁ χ₂ : V4 F → ℂ} (h₁ : Good δ χ₁) (h₂ : Good δ χ₂) :
    Good δ (χ₁ + χ₂) := by
  refine ⟨fun v => ?_, ?_⟩
  · refine ((h₁.1 v).add (h₂.1 v)).congr (ae_of_all _ fun s => ?_)
    simp only [Pi.add_apply, add_mul]
  · have : hat (χ₁ + χ₂) = hat χ₁ + hat χ₂ := by
      funext v
      simp only [hat, Pi.add_apply, add_mul]
      exact integral_add (h₁.1 v) (h₂.1 v)
    rw [this]
    exact add_mem h₁.2 h₂.2

private theorem good_smul {δ : F} (c : ℂ) {χ : V4 F → ℂ} (h : Good δ χ) : Good δ (c • χ) := by
  refine ⟨fun v => ?_, ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using (h.1 v).const_mul c
  · have : hat (c • χ) = c • hat χ := by
      funext v
      simp only [hat, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul _ _
    rw [this]
    exact Submodule.smul_mem _ c h.2

private theorem good_gen (δ : F) {m : V4 F → ℂ} (hm : m ∈ polyFn (F := F)) (hi : Ind m)
    (e : InfinitePlace F → ℕ) {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) :
    Good δ (fun v => (m v * mon e (v 1)) * gauss δ v * g (finPartPi v)) := by
  obtain ⟨P, hP, hH⟩ := hermAdel F e
  have hfin := finHat F g hg
  have hs : ∀ (v : V4 F) (s : A F),
      (m (Function.update v 1 s) * mon e (Function.update v 1 s 1)) * gauss δ (Function.update v 1 s) *
        g (finPartPi (Function.update v 1 s)) =
      (m v * gR δ v) * (mon e s * gE s * g (Function.update (finPartPi v) 1 s.2)) := by
    intro v s
    rw [gauss_split, gR_update, hi, finPart_update, Function.update_self]
    ring
  refine ⟨fun v => ?_, ?_⟩
  · obtain ⟨hint, -⟩ := hH _ (hfin.1 (finPartPi v))
    simp only [hs]
    have hc : Continuous fun s : A F => ψ (-(s * v 1)) :=
      continuous_ψ.comp (continuous_id.mul continuous_const).neg
    have hi' := hint.const_mul (m v * gR δ v)
    refine hi'.mono (hi'.aestronglyMeasurable.mul hc.aestronglyMeasurable) (ae_of_all _ fun s => ?_)
    rw [norm_mul _ (ψ _), norm_ψ, mul_one]
    exact le_of_eq (by simp only [mon, gE])
  · have hval : hat (fun v => (m v * mon e (v 1)) * gauss δ v * g (finPartPi v)) =
        fun v => (m v * P (v 1)) * gauss δ v *
          (fun u : Fin 4 → FiniteAdeleRing (𝓞 F) F =>
            ∫ s, g (Function.update u 1 s) * ((finiteAdelicChar F (-(s * u 1)) : Circle) : ℂ)
              ∂(finiteAdeleMeasure F)) (finPartPi v) := by
      funext v
      obtain ⟨-, hv⟩ := hH _ (hfin.1 (finPartPi v))
      have h1 : ∫ s : A F, mon e s * gE s * g (Function.update (finPartPi v) 1 s.2) * ψ (-(s * v 1))
            ∂(adeleMeasure F) =
          P (v 1) * gE (v 1) * ∫ s, g (Function.update (finPartPi v) 1 s) *
            ((finiteAdelicChar F (-(s * finPartPi v 1)) : Circle) : ℂ) ∂(finiteAdeleMeasure F) := hv (v 1)
      have hI : ∀ s : A F, (m (Function.update v 1 s) * mon e (Function.update v 1 s 1)) *
            gauss δ (Function.update v 1 s) * g (finPartPi (Function.update v 1 s)) * ψ (-(s * v 1)) =
          (m v * gR δ v) * (mon e s * gE s * g (Function.update (finPartPi v) 1 s.2) * ψ (-(s * v 1))) := by
        intro s
        rw [hs]
        ring
      simp only [hat, hI]
      rw [integral_const_mul, h1, gauss_split]
      ring
    rw [hval]
    exact Submodule.subset_span ⟨_, polyFn.mul_mem hm hP, _, hfin.2, rfl⟩

private theorem poly_decomp {p : V4 F → ℂ} (hp : p ∈ polyFn (F := F)) :
    p ∈ Submodule.span ℂ {q : V4 F → ℂ | ∃ m ∈ polyFn (F := F), Ind m ∧
      ∃ e : InfinitePlace F → ℕ, q = fun v => m v * mon e (v 1)} := by
  have h0 : p ∈ Subalgebra.toSubmodule (polyFn (F := F)) := hp
  rw [polyFn, Algebra.adjoin_eq_span] at h0
  refine Submodule.span_mono ?_ h0
  intro q hq
  induction hq using Submonoid.closure_induction with
  | mem q hq =>
    obtain ⟨i, w, rfl⟩ := hq
    by_cases h : i = 1
    · subst h
      exact ⟨1, one_mem _, fun _ _ => rfl, Pi.single w 1, by funext v; simp [mon_single]⟩
    · refine ⟨_, Algebra.subset_adjoin ⟨i, w, rfl⟩, fun v s => ?_, 0, ?_⟩
      · simp only [Function.update_of_ne h]
      · funext v; simp [mon_zero]
  | one => exact ⟨1, one_mem _, fun _ _ => rfl, 0, by funext v; simp [mon_zero]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨m₁, h₁, i₁, e₁, rfl⟩ := ha
    obtain ⟨m₂, h₂, i₂, e₂, rfl⟩ := hb
    refine ⟨m₁ * m₂, mul_mem h₁ h₂, fun v s => ?_, e₁ + e₂, ?_⟩
    · simp only [Pi.mul_apply, i₁ v s, i₂ v s]
    · funext v
      simp only [Pi.mul_apply, mon_add]
      ring

private theorem good_poly (δ : F) {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) {p : V4 F → ℂ}
    (hp : p ∈ Submodule.span ℂ {q : V4 F → ℂ | ∃ m ∈ polyFn (F := F), Ind m ∧
      ∃ e : InfinitePlace F → ℕ, q = fun v => m v * mon e (v 1)}) :
    Good δ (fun v => p v * gauss δ v * g (finPartPi v)) := by
  induction hp using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨m, hm, hi, e, rfl⟩ := hq
    exact good_gen δ hm hi e hg
  | zero =>
    have : (fun v : V4 F => (0 : V4 F → ℂ) v * gauss δ v * g (finPartPi v)) = 0 := by
      funext v; simp
    rw [this]
    exact good_zero δ
  | add a b _ _ ha hb =>
    have : (fun v : V4 F => (a + b) v * gauss δ v * g (finPartPi v)) =
        (fun v => a v * gauss δ v * g (finPartPi v)) + fun v => b v * gauss δ v * g (finPartPi v) := by
      funext v; simp only [Pi.add_apply]; ring
    rw [this]
    exact good_add ha hb
  | smul c a _ ha =>
    have : (fun v : V4 F => (c • a) v * gauss δ v * g (finPartPi v)) =
        c • fun v => a v * gauss δ v * g (finPartPi v) := by
      funext v; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    exact good_smul c ha

private theorem good_fock (δ : F) {χ : V4 F → ℂ} (hχ : χ ∈ FockFn δ) : Good δ χ := by
  induction hχ using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨p, hp, g, hg, rfl⟩ := hf
    exact good_poly δ hg (poly_decomp hp)
  | zero => exact good_zero δ
  | add a b _ _ ha hb => exact good_add ha hb
  | smul c a _ ha => exact good_smul c ha

end UpperTheory.ConvolutionTheory.R2.G.FockHat

end

theorem UpperTheory.ConvolutionTheory.R2.G.hatFock :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), ∀ χ ∈ FockFn δ, hat χ ∈ FockFn δ := by
  intro F _ _ _ δ χ hχ
  exact (FockHat.good_fock δ hχ).2
