import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.LiftCentre
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Exp
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ConjStep
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.WfEig
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.FixTr
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.AeInt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.CosetShift
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.GoodOfGoodAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.HeckeExpl
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.EigOfSat

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem nu_mul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x y : GL (Fin 2) (A E)) :
    nu F (x * y) = nu F x * nu F y := by simp only [nu, map_mul]

private theorem nu_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    nu F (1 : GL (Fin 2) (A E)) = 1 := by simp only [nu, map_one]

private theorem dM_mul' {F : Type} [Field F] [NumberField F] (s t : (A F)ˣ) : dM (s * t) = dM s * dM t :=
  Units.ext (by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [dM, Matrix.mul_apply, Fin.sum_univ_two])

private theorem dM_one' {F : Type} [Field F] [NumberField F] : dM (1 : (A F)ˣ) = 1 :=
  Units.ext (by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [dM])

private theorem coordinate_embedNorm_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (u : A F) :
    D.co (D.mkE u 0) = Pi.single 0 u := by
  letI : Algebra (A F) (A E) := AdeleBaseChange.algebraAdeleRing
  have e : D.mkE u 0 = u • AdeleBaseChange.adeleBasis D.b 0 := by
    rw [AdeleBaseChange.adeleBasis_apply, D.b0, map_one, Algebra.smul_def, mul_one, Dat.mkE, map_zero, zero_mul, add_zero]
    rfl
  funext i
  simp only [Dat.co, e, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_eq_pi_single]

private theorem co_mkE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (u : A F) :
    D.co (D.mkE u 0) 0 = u := by rw [coordinate_embedNorm_zero]; simp

private theorem co_mkE' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (u : A F) :
    D.co (D.mkE u 0) 1 = 0 := by rw [coordinate_embedNorm_zero]; simp

theorem UpperTheory.ConvolutionTheory.R2.H.liftRel :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h₀ : GL (Fin 2) (A E),
      ∀ᶠ v : P F in cofinite, W.η.UnrAt v → W.η.val v = -1 → ∀ α β : ℂˣ, π.HasSat v {α, β} → ∀ (ϖ : (Kv v)ˣ) (z : (A E)ˣ), IsU ϖ →
        (z : A E) = D.mkE (idl v ϖ : (A F)ˣ) 0 → ideleNorm F E z = idl v ϖ ^ 2 →
        WE D (lift W M f.1 φ) (aE z * h₀) = (q v)⁻¹ * ((α : ℂ) ^ 2 + (β : ℂ) ^ 2) * WE D (lift W M f.1 φ) h₀ ∧
          ∀ h, lift W M f.1 φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) = ((α : ℂ) * β) ^ 2 * lift W M f.1 φ h := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h₀
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  have hδ : D.δ ≠ 0 := fun e => by
    have h1 : D.θ = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by rw [D.sq, e, map_zero])
    exact D.b.ne_zero 1 (D.b1.trans h1)
  have hl : IsOpen {k : GL (Fin 2) (Af F) | ∀ g, f.1 (g * finGL F 2 k) = f.1 g} := by
    convert (π.cusp f hf).1.level using 1
    exact Set.ext fun k => ⟨fun a => Subtype.ext (funext a), fun a g => congrFun (congrArg Subtype.val a) g⟩
  let f₁ : GL (Fin 2) (A F) → ℂ := fun g => f.1 (g * dM (nu F h₀))
  have hc : Continuous f₁ := (UpperTheory.ConvolutionTheory.R2.decay F π f hf).1.comp (continuous_mul_const _)
  have hleft : ∀ γ g, f₁ (ratGL F 2 γ * g) = f₁ g := fun γ g => by
    simp only [f₁, mul_assoc]
    exact (π.cusp f hf).1.left γ _
  have hw : ∀ x, w1 W f.1 φ (x * h₀) = w1 W f₁ (W.L h₀ φ) x := fun x => funext fun g => by
    simp only [w1, Wf, f₁, nu_mul', dM_mul', map_mul, Module.End.mul_apply, mul_assoc]
  have hb : w1 W f.1 φ h₀ = fun g => Wf f₁ (gl g) * UpperTheory.ConvolutionTheory.R2.hat (W.Om g (W.L h₀ φ)).1 ![0, 1, 1, 0] := by
    rw [← one_mul h₀, hw, one_mul]
    funext g
    simp only [w1, nu_one', dM_one', map_one, mul_one, Module.End.one_apply]
  obtain ⟨hN, hE⟩ := wfEig F f₁ hc hleft
  filter_upwards [gdAe F D.δ hδ, (aeK F).2.1 (nu F h₀), (aeK F).2.2 f.1 hl, stdAe F (W.L h₀ φ)] with v hg hk hfix hstd
    hu hval α β hB ϖ z hϖ hz hn
  have hEig := UpperTheory.V.Af.Smo.eigOfSat F 2 π v _ hB f hf hfix
  refine ⟨?_, fun h => ?_⟩
  · rw [UpperTheory.ConvolutionTheory.R2.exp F E D W M π f hf φ hφ, UpperTheory.ConvolutionTheory.R2.exp F E D W M π f hf φ hφ]
    obtain ⟨-, -, c1, c2, c3⟩ := UpperTheory.ConvolutionTheory.R2.conv F E D W M π f hf φ hφ (aE z * h₀)
    obtain ⟨-, -, -, -, c4⟩ := UpperTheory.ConvolutionTheory.R2.conv F E D W M π f hf φ hφ h₀
    rw [hw] at c1 c2 c3
    rw [hb] at c4
    have e1 : W1 W M f.1 φ (aE z * h₀) = W1 W M f₁ (W.L h₀ φ) (aE z) := by simp only [W1, hw]
    have hz' : ((z⁻¹ : (A E)ˣ) : A E) = D.mkE (((idl v ϖ)⁻¹ : (A F)ˣ) : A F) 0 := by
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [hz]
      simp only [Dat.mkE, map_zero, zero_mul, add_zero, ← map_mul, Units.mul_inv, map_one]
    rw [e1, conjStep F E D W M f₁ _ z c1 c2 c3, hn, hz', co_mkE, co_mkE',
      core F E D W M v ϖ hϖ hg hu hval (Wf f₁) α β (hE v _ ((fixTr F v f.1 _ hk).2 _ hEig)) hN _ hstd c4]
    simp only [W1, hb]
  · rw [(UpperTheory.ConvolutionTheory.R2.equiv F E D W M π f hf φ).2 ω (hω f hf), hn]
    by_cases h0 : f.1 = 0
    · simp [UpperTheory.ConvolutionTheory.R2.lift, h0]
    · obtain ⟨g, hg0⟩ := Function.ne_iff.1 h0
      obtain ⟨R, -, -, hR⟩ := heckeExpl F v ϖ hϖ
      have h1 : f.1 (g * lc v (1 * dL ϖ ϖ)) = (α : ℂ) * β * f.1 (g * lc v 1) := (hR α β _ (hEig g) 1).2
      have h2 : g * Matrix.GeneralLinearGroup.scalar (Fin 2) (idl v ϖ) = Matrix.GeneralLinearGroup.scalar (Fin 2) (idl v ϖ) * g :=
        Units.ext ((Matrix.scalar_commute _ (fun _ => Commute.all _ _) g.val).eq.symm)
      rw [one_mul, map_one, mul_one, (lcLaws F v).2.2.2.2.1, h2, hω f hf] at h1
      rw [map_pow, Units.val_pow_eq_pow_val, mul_right_cancel₀ hg0 h1]
