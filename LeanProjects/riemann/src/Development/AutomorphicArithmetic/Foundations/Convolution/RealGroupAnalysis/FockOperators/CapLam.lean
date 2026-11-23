import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CapAbs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Capelli
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XaCommCoord
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.EopLift
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.LiftNegForm
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FockOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.capLam :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (O : Ops F) (Λ : TR.Sm F 2 →ₗ[ℂ] S4 F →ₗ[ℂ] Sm E 2), (∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, (Λ f φ).1 = lift W M f.1 φ) → LieLift O W M π → MoveE O W M π →
    ∀ (τ : E →+* ℂ) u, ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, cap τ u (Λ f φ) = Λ (TR.cap (pl F τ) u f) φ := by
  intro F E _ _ _ _ _ _ _ D W M π O Λ hΛ hL hE τ u f hf φ hφ
  obtain ⟨hXX, hDD, hDX, he, hfo, hh⟩ := weylX F E D W O τ
  obtain ⟨c1, c2, c3⟩ := capelli (Module.End ℂ (S4 F)) (O.X D τ) (O.DX D τ) (O.dE D τ)
    (O.X D τ 0 1 * O.X D τ 1 0 - O.X D τ 0 0 * O.X D τ 1 1)
    (O.DX D τ 0 1 * O.DX D τ 1 0 - O.DX D τ 0 0 * O.DX D τ 1 1) (O.h (pl F τ))
    hXX hDD hDX (fun _ _ => rfl) rfl rfl hh
  generalize O.X D τ 0 1 * O.X D τ 1 0 - O.X D τ 0 0 * O.X D τ 1 1 = q at he c1 c3
  generalize O.DX D τ 0 1 * O.DX D τ 1 0 - O.DX D τ 0 0 * O.DX D τ 1 1 = Δ at hfo c1 c3
  have hcc : cc ≠ 0 := by
    simp [cc, Real.pi_ne_zero]
  have hk : cc * -cc⁻¹ = -1 := by
    rw [mul_neg, mul_inv_cancel₀ hcc]
  have k' : -cc⁻¹ * cc = -1 := by
    rw [neg_mul, inv_mul_cancel₀ hcc]
  have hef : O.e D.δ (pl F τ) * O.f D.δ (pl F τ) = -(q * Δ) := by
    rw [he, hfo, smul_mul_smul_comm, hk, neg_smul, one_smul]
  have hfe : O.f D.δ (pl F τ) * O.e D.δ (pl F τ) = -(Δ * q) := by
    rw [he, hfo, smul_mul_smul_comm, k', neg_smul, one_smul]
  have hP : Formalism.REAL.GlRel (Eop (a := 2) τ) := by
    intro i j k l
    have h := congrArg (Cm.uC E 2) (Cm.glRel_genC (a := 2) τ i j k l)
    simpa only [map_sub, map_mul, Cm.uC_genC, apply_ite (Cm.uC E 2), map_zero] using h
  have hst : ∀ i j, ∀ v ∈ π.V, TR.Eop (pl F τ) i j v ∈ π.V := fun i j v hv =>
    π.stable (.lie _) v hv
  have hfock := fun s hs => fockOps F E D O s hs
  have hme : ∀ v ∈ π.V, ∀ s ∈ Fock D.δ, Λ v (O.e D.δ (pl F τ) s) = -Λ (TR.Eop (pl F τ) 0 1 v) s := by
    intro v hv s hs
    refine Subtype.ext (funext fun g => ?_)
    change (Λ v (O.e D.δ (pl F τ) s)).1 g = -(Λ (TR.Eop (pl F τ) 0 1 v) s).1 g
    rw [hΛ v hv _ ((hfock s hs).2.2.1 _), hΛ _ (hst 0 1 v hv) s hs]
    exact hE v hv s hs _ g
  have hmf : ∀ v ∈ π.V, ∀ s ∈ Fock D.δ, Λ v (O.f D.δ (pl F τ) s) = -Λ (TR.Eop (pl F τ) 1 0 v) s := by
    intro v hv s hs
    refine Subtype.ext (funext fun g => ?_)
    change (Λ v (O.f D.δ (pl F τ) s)).1 g = -(Λ (TR.Eop (pl F τ) 1 0 v) s).1 g
    rw [hΛ v hv _ ((hfock s hs).2.2.2.1 _), hΛ _ (hst 1 0 v hv) s hs]
    exact moveF F E D W M π O hE v hv s hs _ g
  have h1 : O.e D.δ (pl F τ) * O.f D.δ (pl F τ) - O.f D.δ (pl F τ) * O.e D.δ (pl F τ) = O.h (pl F τ) := by
    rw [hef, hfe, ← c1]
    abel
  have h3 : (O.dE D τ 0 0 - O.dE D τ 1 1) * (O.dE D τ 0 0 - O.dE D τ 1 1) +
      2 * (O.dE D τ 0 1 * O.dE D τ 1 0 + O.dE D τ 1 0 * O.dE D τ 0 1) =
      O.h (pl F τ) * O.h (pl F τ) + 2 * (O.e D.δ (pl F τ) * O.f D.δ (pl F τ) + O.f D.δ (pl F τ) * O.e D.δ (pl F τ)) := by
    rw [c3, hef, hfe]
    noncomm_ring
  exact capAbs (TR.Sm F 2) (S4 F) (Sm E 2) π.V (Fock D.δ) Λ (TR.Eop (pl F τ)) (Eop τ) (O.dE D τ)
    (O.e D.δ (pl F τ)) (O.f D.δ (pl F τ)) (O.h (pl F τ)) (TR.glRel_Eop _) hP hst
    (fun i j s hs => (hfock s hs).2.2.2.2.2.1 τ i j) (fun s hs => (hfock s hs).2.2.1 _)
    (fun s hs => (hfock s hs).2.2.2.1 _)
    (fun i j v hv s hs => eopLift F E D W M π O Λ hΛ hL τ i j v hv s hs) hme hmf h1 c2 h3
    (u + ((2 : ℕ) - 1) / 2) f hf φ hφ
