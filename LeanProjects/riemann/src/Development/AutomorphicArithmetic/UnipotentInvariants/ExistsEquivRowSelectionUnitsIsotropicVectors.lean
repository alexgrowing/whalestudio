import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.RowCosets
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal

private theorem rt_inj {c c' : ℚ} (h : (rt c : A ℚ) = rt c') : c = c' :=
  AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ h

private theorem rp_inj {ξ ξ' : Fin 4 → ℚ} (h : rp ξ = rp ξ') : ξ = ξ' := by
  funext i
  exact rt_inj (congrFun h i)

private theorem gl_ratS_mul {E : Type} [Field E] [NumberField E] (a b : Matrix.SpecialLinearGroup (Fin 2) E) :
    gl (ratS E (a * b)) = gl (ratS E a) * gl (ratS E b) := by
  rw [map_mul, gl_mul]

private theorem gl_ratS_inv {E : Type} [Field E] [NumberField E] (a : Matrix.SpecialLinearGroup (Fin 2) E) :
    (gl (ratS E a))⁻¹ = gl (ratS E a⁻¹) := by
  rw [map_inv, gl_inv]

theorem UpperTheory.exists_equiv_rowSelection_units_isotropicVectors :
    ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (σ : {r : Fin 2 → E // r ≠ 0} → Matrix.SpecialLinearGroup (Fin 2) E) (Sel : Set {r : Fin 2 → E // r ≠ 0}), Orb1 → M.RowSec σ → (∀ r : {r : Fin 2 → E // r ≠ 0}, ∃! t : Eˣ, ∃ r' ∈ Sel, r'.1 = (t : E) • r.1) → ∃ e : ↥Sel × ℚˣ ≃ ↥{ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0}, ∀ r s, rp (e (r, s)).1 = D.act (gl (ratS E (σ r.1)))⁻¹ (rp ![0, (s : ℚ), 0, 0]) := by
  intro E _ _ _ D σ Sel hO hσ hS
  obtain ⟨h1, h2, h3, h4, -⟩ := hO E D
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hq⟩ := szLaws E D
  have hpt : ∀ p : ↥Sel × ℚˣ, ∃ ξ : Fin 4 → ℚ,
      rp ξ = D.act (gl (ratS E (σ p.1.1)))⁻¹ (rp ![0, (p.2 : ℚ), 0, 0]) := by
    rintro ⟨r, s⟩
    obtain ⟨ρ, hρ⟩ := h1 (σ r.1)⁻¹
    exact ⟨ρ ![0, (s : ℚ), 0, 0], by rw [gl_ratS_inv, hρ]⟩
  choose pt hpt using hpt
  have hmem : ∀ p, pt p ∈ {ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0} := by
    rintro ⟨r, s⟩
    refine ⟨fun h0 => ?_, ?_⟩
    · have hp := congrArg (D.act (gl (ratS E (σ r.1)))) (hpt (r, s))
      rw [D.act_act_inv, h0] at hp
      have hz : rp (0 : Fin 4 → ℚ) = 0 := by
        funext i
        exact map_zero _
      rw [hz] at hp
      have hz' : D.act (gl (ratS E (σ r.1))) (0 : V4 ℚ) = 0 := (D.actL (gl (ratS E (σ r.1)))).map_zero
      rw [hz'] at hp
      have h1' : (rt (0 : ℚ) : A ℚ) = rt (s : ℚ) := (map_zero _).trans (congrFun hp 1)
      exact s.ne_zero (rt_inj h1').symm
    · apply rt_inj
      rw [← hq, hpt (r, s), gl_ratS_inv, D.quadForm_act, nu_gl, hq]
      simp [qr]
  have hinj : Function.Injective pt := by
    rintro ⟨r, s⟩ ⟨r', s'⟩ h
    have hh : D.act (gl (ratS E (σ r.1)))⁻¹ (rp ![0, (s : ℚ), 0, 0]) =
        D.act (gl (ratS E (σ r'.1)))⁻¹ (rp ![0, (s' : ℚ), 0, 0]) := by
      rw [← hpt (r, s), ← hpt (r', s'), h]
    obtain ⟨δ, hδ⟩ : ∃ δ, δ = σ r'.1 * (σ r.1)⁻¹ := ⟨_, rfl⟩
    have hact : D.act (gl (ratS E δ)) (rp ![0, (s : ℚ), 0, 0]) = rp ![0, (s' : ℚ), 0, 0] := by
      rw [hδ, gl_ratS_mul, ← gl_ratS_inv, D.act_mul, hh, D.act_act_inv]
    have h10 := h3 δ s s' s.ne_zero hact
    have e1 : σ r'.1 = δ * σ r.1 := by simp [hδ]
    have hrow : ∀ j, r'.1.1 j = δ 1 1 * r.1.1 j := by
      intro j
      have a : (σ r'.1).1 1 j = r'.1.1 j := congrFun (hσ r'.1) j
      have b : (σ r.1).1 1 j = r.1.1 j := congrFun (hσ r.1) j
      have c : (σ r'.1).1 1 j = (δ * σ r.1).1 1 j := by rw [← e1]
      rw [← a, c, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, b]
      have h10' : δ.1 1 0 = 0 := h10
      rw [h10', zero_mul, zero_add]
    have ht0 : δ 1 1 ≠ 0 := by
      intro h
      apply r'.1.2
      funext j
      rw [hrow, h, zero_mul]
      rfl
    have ht : Units.mk0 _ ht0 = (1 : Eˣ) := (hS r.1).unique
      ⟨r'.1, r'.2, by funext j; exact hrow j⟩ ⟨r.1, r.2, by simp⟩
    have ht1 : δ 1 1 = 1 := by simpa using congrArg Units.val ht
    have hr : r' = r := by
      refine Subtype.ext (Subtype.ext ?_)
      funext j
      rw [hrow, ht1, one_mul]
    subst hr
    have hss : rp ![0, (s : ℚ), 0, 0] = rp ![0, (s' : ℚ), 0, 0] := by
      have := congrArg (D.act (gl (ratS E (σ r'.1)))) hh
      simpa only [D.act_act_inv] using this
    have h1' : (s : ℚ) = s' := rt_inj (congrFun hss 1)
    rw [Units.ext h1']
  have hsurj : ∀ ξ ∈ {ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0}, ∃ p, pt p = ξ := by
    rintro ξ ⟨hξ0, hξq⟩
    obtain ⟨γ, r0, hr0, hγ⟩ := h2 ξ hξ0 hξq
    have hrow : (γ⁻¹).1 1 ≠ 0 := by
      intro h
      have hd := (γ⁻¹).det_coe
      have a : (γ⁻¹).1 1 0 = 0 := congrFun h 0
      have b : (γ⁻¹).1 1 1 = 0 := congrFun h 1
      rw [Matrix.det_fin_two, a, b] at hd
      simp at hd
    obtain ⟨t, ⟨r', hr', hrt⟩, -⟩ := hS ⟨_, hrow⟩
    have ha : ∀ j, (σ r').1 1 j = (t : E) * (γ⁻¹).1 1 j := by
      intro j
      rw [hσ r', hrt]
      rfl
    have h10 : (σ r' * γ) 1 0 = 0 := by
      have hI : (γ⁻¹ * γ).1 1 0 = 0 := by simp
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at hI
      change (σ r' * γ).1 1 0 = 0
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ha, ha, mul_assoc, mul_assoc,
        ← mul_add, hI, mul_zero]
    obtain ⟨c, hc, hcr⟩ := h4 _ h10
    refine ⟨(⟨r', hr'⟩, Units.mk0 (c * r0) (mul_ne_zero hc hr0)), rp_inj ?_⟩
    rw [hpt]
    change D.act (gl (ratS E (σ r')))⁻¹ (rp ![0, c * r0, 0, 0]) = rp ξ
    rw [← hcr, gl_ratS_mul, D.act_mul, D.act_inv_act, hγ]
  refine ⟨Equiv.ofBijective (fun p => ⟨pt p, hmem p⟩) ⟨?_, ?_⟩, fun r s => hpt (r, s)⟩
  · intro p p' h
    exact hinj (congrArg Subtype.val h)
  · rintro ⟨ξ, hξ⟩
    obtain ⟨p, hp⟩ := hsurj ξ hξ
    exact ⟨p, Subtype.ext hp⟩
