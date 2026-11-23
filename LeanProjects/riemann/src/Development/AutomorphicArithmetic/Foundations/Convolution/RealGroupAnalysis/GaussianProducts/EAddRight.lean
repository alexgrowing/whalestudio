import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.OrthogonalVectors

open GroundTheory.Automorphic.FourierWhittaker

variable {F : Type} [Field F] [NumberField F]

private noncomputable def E (κ : Fin 2 → F) (u : Fin 2 → A F) : ℂ := ψ (rt (κ 0) * u 0 + rt (κ 1) * u 1)

private theorem E_cont (κ : Fin 2 → F) : Continuous (E κ) :=
  continuous_ψ.comp (((continuous_const).mul (continuous_apply 0)).add ((continuous_const).mul (continuous_apply 1)))

private theorem E_norm (κ : Fin 2 → F) (u : Fin 2 → A F) : ‖E κ u‖ = 1 := norm_ψ _

private theorem E_add_left (κ κ' : Fin 2 → F) (u : Fin 2 → A F) : E (κ + κ') u = E κ u * E κ' u := by
  simp only [E, ← UpperTheory.ConvolutionTheory.R2.ψ_add]
  congr 1
  simp only [Pi.add_apply, map_add]
  ring

private theorem E_add_right (κ : Fin 2 → F) (u v : Fin 2 → A F) : E κ (u + v) = E κ u * E κ v := by
  simp only [E, ← UpperTheory.ConvolutionTheory.R2.ψ_add]
  congr 1
  simp only [Pi.add_apply]
  ring

private theorem E_zero (u : Fin 2 → A F) : E (0 : Fin 2 → F) u = 1 := by
  simp [E]

private theorem E_per (κ : Fin 2 → F) : ∀ ξ ∈ vecLattice F (Fin 2), ∀ x, E κ (ξ + x) = E κ x := by
  intro ξ hξ x
  obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
  rw [E_add_right]
  have : E κ (fun i => algebraMap F (A F) (η i)) = 1 := by
    simp only [E]
    rw [← map_mul, ← map_mul, ← map_add]
    exact ψ_rt _
  rw [this, one_mul]

private theorem exists_ne (κ : Fin 2 → F) (hκ : κ ≠ 0) : ∃ a, E κ a ≠ 1 := by
  obtain ⟨x, hx⟩ : ∃ x, adelicChar F x ≠ 1 := by
    by_contra h
    push_neg at h
    exact adelicChar_ne_one (K := F) (DFunLike.ext _ _ fun x => by simpa using h x)
  have hx' : ψ x ≠ 1 := fun h => hx (Circle.ext (by simpa [ψ] using h))
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hκ
  have hr : rt (κ i) * rt (κ i)⁻¹ = (1 : A F) := by
    rw [← map_mul, mul_inv_cancel₀ hi, map_one]
  refine ⟨Pi.single i (rt (κ i)⁻¹ * x), ?_⟩
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue] at hr ⊢
    simp only [E, Pi.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero,
      ← mul_assoc, hr, one_mul, Fin.isValue, one_ne_zero]
    exact hx'
  · simp only [Fin.mk_one, Fin.isValue] at hr ⊢
    simp only [E, Pi.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, zero_add,
      ← mul_assoc, hr, one_mul, Fin.isValue, one_ne_zero]
    exact hx'

private theorem E_int (κ : Fin 2 → F) (hκ : κ ≠ 0) : ∫ u in FS2 F, E κ u ∂(adeleMeasurePi F) = 0 := by
  obtain ⟨a, ha⟩ := exists_ne κ hκ
  change ∫ u in vecDomain F (Fin 2), E κ u ∂(vecMeasure F (Fin 2)) = 0
  have h := setIntegral_comp_add (K := F) (ι := Fin 2) a (h := E κ) (E_per κ)
  simp only [E_add_right] at h
  rw [integral_mul_const] at h
  have h1 : (∫ u in vecDomain F (Fin 2), E κ u ∂(vecMeasure F (Fin 2))) * (E κ a - 1) = 0 := by
    rw [mul_sub, h, mul_one, sub_self]
  exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 ha)

private theorem vol : (adeleMeasurePi F).restrict (FS2 F) Set.univ = 1 := by
  rw [Measure.restrict_apply_univ]
  exact vecMeasure_vecDomain

private theorem fin_inst : IsFiniteMeasure ((adeleMeasurePi F).restrict (FS2 F)) :=
  ⟨by rw [vol]; exact ENNReal.one_lt_top⟩

private theorem int_const (a : ℝ) : ∫ _ in FS2 F, a ∂(adeleMeasurePi (ι := Fin 2) F) = a := by
  rw [integral_const, measureReal_def, vol]
  simp

private theorem E_int_zero : ∫ u in FS2 F, E (0 : Fin 2 → F) u ∂(adeleMeasurePi F) = 1 := by
  simp only [E_zero]
  rw [integral_const, measureReal_def, vol]
  simp

private theorem cont_int {g : (Fin 2 → A F) → ℂ} (hg : Continuous g) : IntegrableOn g (FS2 F) (adeleMeasurePi F) := by
  obtain ⟨C, hC, hs⟩ := exists_isCompact_superset_vecDomain (K := F) (ι := Fin 2)
  exact (hg.continuousOn.integrableOn_compact (μ := vecMeasure F (Fin 2)) hC).mono_set hs

private theorem core (κ₀ : Fin 2 → F) (L : (Fin 2 → F) → Fin 2 → F) (c₀ : ℂ) (c : (Fin 2 → F) → ℂ)
    (hc : Summable fun ξ => ‖c ξ‖) (Φ : (Fin 2 → A F) → ℂ) (hΦ : ∀ u, Φ u = c₀ + ∑' ξ, E (L ξ) u * c ξ) :
    IntegrableOn (fun u => Φ u * E κ₀ u) (FS2 F) (adeleMeasurePi F) ∧
    HasSum (fun ξ => (∫ u in FS2 F, E (κ₀ + L ξ) u ∂(adeleMeasurePi F)) * c ξ)
      ((∫ u in FS2 F, Φ u * E κ₀ u ∂(adeleMeasurePi F)) - c₀ * ∫ u in FS2 F, E κ₀ u ∂(adeleMeasurePi F)) := by
  haveI := countable_numberField F
  haveI := fin_inst (F := F)
  set g : (Fin 2 → F) → (Fin 2 → A F) → ℂ := fun ξ u => E (κ₀ + L ξ) u * c ξ with hgdef
  have hgc : ∀ ξ, Continuous (g ξ) := fun ξ => (E_cont _).mul continuous_const
  have hgn : ∀ ξ u, ‖g ξ u‖ = ‖c ξ‖ := fun ξ u => by simp [hgdef, norm_mul, E_norm]
  have hsum : ∀ u, Summable fun ξ => E (L ξ) u * c ξ := fun u =>
    Summable.of_norm (by simpa [norm_mul, E_norm] using hc)
  have e : ∀ u, Φ u * E κ₀ u = c₀ * E κ₀ u + ∑' ξ, g ξ u := by
    intro u
    rw [hΦ, add_mul, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun ξ => ?_
    simp only [hgdef, E_add_left]
    ring
  have hcont : Continuous fun u => ∑' ξ, g ξ u := continuous_tsum hgc hc fun ξ u => (hgn ξ u).le
  have hI := cont_int hcont
  have hT := cont_int (E_cont κ₀)
  have hT' : IntegrableOn (fun u => c₀ * E κ₀ u) (FS2 F) (adeleMeasurePi F) := hT.const_mul c₀
  refine ⟨?_, ?_⟩
  · simp only [e]
    exact hT'.add hI
  · have hS := hasSum_integral_of_summable_integral_norm (μ := (adeleMeasurePi F).restrict (FS2 F))
      (F := g) (fun ξ => cont_int (hgc ξ)) (by
        simp only [hgn]
        simpa only [int_const] using hc)
    have h2 : (∫ u in FS2 F, Φ u * E κ₀ u ∂(adeleMeasurePi F)) - c₀ * ∫ u in FS2 F, E κ₀ u ∂(adeleMeasurePi F) =
        ∫ u in FS2 F, ∑' ξ, g ξ u ∂(adeleMeasurePi F) := by
      simp only [e]
      rw [integral_add hT' hI, integral_const_mul]
      ring
    rw [h2]
    simpa only [hgdef, integral_mul_const] using hS

end UpperTheory.ConvolutionTheory.R2.G.OrthogonalVectors

open UpperTheory.ConvolutionTheory.R2.G.OrthogonalVectors in
theorem UpperTheory.ConvolutionTheory.R2.G.orth :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → ∀ (c₀ : ℂ) (c : (Fin 2 → F) → ℂ) (Φ : (Fin 2 → A F) → ℂ), Summable (fun ξ => ‖c ξ‖) →
    (∀ u, Φ u = c₀ + ∑' ξ, chi δ ξ u * c ξ) → IntegrableOn Φ (FS2 F) (adeleMeasurePi F) ∧
    IntegrableOn (fun u => Φ u * ψ (2 * u 0)) (FS2 F) (adeleMeasurePi F) ∧
    ∫ u in FS2 F, Φ u ∂(adeleMeasurePi F) = c₀ + c 0 ∧ ∫ u in FS2 F, Φ u * ψ (2 * u 0) ∂(adeleMeasurePi F) = c ![1, 0] := by
  intro F _ _ δ hδ c₀ c Φ hc hΦ
  set L : (Fin 2 → F) → Fin 2 → F := fun ξ => ![-(2 * ξ 0), 2 * δ * ξ 1] with hL
  have hchi : ∀ ξ u, chi δ ξ u = E (L ξ) u := by
    intro ξ u
    simp only [chi, E, hL]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, map_mul, map_ofNat]
    ring
  have hΦ' : ∀ u, Φ u = c₀ + ∑' ξ, E (L ξ) u * c ξ := fun u => by
    rw [hΦ]; simp only [hchi]
  set κ : Fin 2 → F := ![2, 0] with hκ
  have hψ : ∀ u : Fin 2 → A F, ψ (2 * u 0) = E κ u := by
    intro u
    have h2A : rt (2 : F) = (2 : A F) := map_ofNat _ 2
    simp only [E, hκ]
    congr 1
    simp [h2A]
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hκ0 : κ ≠ 0 := fun h => h2 (by simpa [hκ] using congrFun h 0)
  obtain ⟨i0, s0⟩ := core 0 L c₀ c hc Φ hΦ'
  obtain ⟨i1, s1⟩ := core κ L c₀ c hc Φ hΦ'
  simp only [E_zero, mul_one, zero_add] at i0 s0
  simp only [← hψ] at i1
  refine ⟨i0, i1, ?_, ?_⟩
  · have t : HasSum (fun ξ => (∫ u in FS2 F, E (L ξ) u ∂(adeleMeasurePi F)) * c ξ) (c 0) := by
      have hL0 : L 0 = 0 := by
        ext i; fin_cases i <;> simp [hL]
      have := hasSum_single (f := fun ξ => (∫ u in FS2 F, E (L ξ) u ∂(adeleMeasurePi F)) * c ξ) (0 : Fin 2 → F) (fun ξ hξ => by
        have hne : L ξ ≠ 0 := fun h => hξ (by
          have a0 := congrFun h 0
          have a1 := congrFun h 1
          simp only [hL, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, neg_eq_zero, mul_eq_zero, h2, hδ, false_or] at a0 a1
          ext i; fin_cases i
          · exact a0
          · exact a1)
        rw [E_int _ hne, zero_mul])
      simpa only [hL0, E_int_zero, one_mul] using this
    have e1 := s0.unique t
    have e2 : ∫ u in FS2 F, (1 : ℂ) ∂(adeleMeasurePi F) = 1 := by
      simpa only [E_zero] using E_int_zero (F := F)
    rw [e2, mul_one] at e1
    rw [sub_eq_iff_eq_add] at e1
    rw [e1, add_comm]
  · have t : HasSum (fun ξ => (∫ u in FS2 F, E (κ + L ξ) u ∂(adeleMeasurePi F)) * c ξ) (c ![1, 0]) := by
      have hL0 : κ + L ![1, 0] = 0 := by
        ext i; fin_cases i <;> simp [hL, hκ]
      have := hasSum_single (f := fun ξ => (∫ u in FS2 F, E (κ + L ξ) u ∂(adeleMeasurePi F)) * c ξ) (![1, 0] : Fin 2 → F) (fun ξ hξ => by
        have hne : κ + L ξ ≠ 0 := fun h => hξ (by
          have a0 := congrFun h 0
          have a1 := congrFun h 1
          simp only [hL, hκ, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, zero_add, mul_eq_zero, h2, hδ, false_or] at a0 a1
          ext i; fin_cases i
          · have : 2 * (1 - ξ 0) = 0 := by linear_combination a0
            have := (mul_eq_zero.1 this).resolve_left h2
            simpa using (sub_eq_zero.1 this).symm
          · simpa using a1)
        rw [E_int _ hne, zero_mul])
      simpa only [hL0, E_int_zero, one_mul] using this
    have e1 := s1.unique t
    rw [E_int κ hκ0, mul_zero, sub_zero] at e1
    simpa only [hψ] using e1
