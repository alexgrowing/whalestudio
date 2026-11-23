import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieL
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieZ
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.MoveH
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.SumCoordPl
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DLFock
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.OpsFock
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieSplit

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lieLift :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), Fo.LieLift O W M π := by
  intro F E _ _ _ _ _ _ _ D O W M π f hf φ hφ Φ hΦ X h
  obtain ⟨Y, s, hY, rfl, hs⟩ := lieSplit X
  obtain ⟨hcen, hdadd, -, htr⟩ := dLCen F E D O
  obtain ⟨ladd, lsmul, radd, rsmul⟩ := lin F E D W M π
  have hL := lieL F E D O W M π f hf φ hφ Y hY Φ hΦ
  have hZ := lieZ F E D W M π f hf φ hφ s Φ hΦ
  have hH := moveH F E D O W M π f hf φ hφ
  have hE : ∀ (w : InfinitePlace F) (i j : Fin 2), TR.Eop w i j f ∈ π.V := fun w i j => π.stable (.lie _) f hf
  have h0 : lift W M (0 : GL (Fin 2) (A F) → ℂ) φ = 0 := by simpa using rsmul f.1 0 φ
  have hl0 : lift W M f.1 (0 : S4 F) = 0 := by simpa using lsmul f.1 0 φ
  have sumF : ∀ (S : Finset (E →+* ℂ)) (c : (E →+* ℂ) → ℂ) (g : (E →+* ℂ) → TR.Sm F 2), (∀ τ, g τ ∈ π.V) →
      lift W M (∑ τ ∈ S, c τ • g τ).1 φ = ∑ τ ∈ S, c τ • lift W M (g τ).1 φ := by
    intro S c g hg
    induction S using Finset.induction_on with
    | empty => simpa using h0
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        radd _ (π.V.smul_mem _ (hg a)) _ (sum_mem fun τ _ => π.V.smul_mem _ (hg τ)) φ hφ, ih]
      congr 1
      exact rsmul (g a).1 (c a) φ
  have sumP : ∀ (S : Finset (E →+* ℂ)) (c : (E →+* ℂ) → ℂ) (ψ : (E →+* ℂ) → S4 F), (∀ τ, ψ τ ∈ Fock D.δ) →
      lift W M f.1 (∑ τ ∈ S, c τ • ψ τ) = ∑ τ ∈ S, c τ • lift W M f.1 (ψ τ) := by
    intro S c ψ hψ
    induction S using Finset.induction_on with
    | empty => simpa using hl0
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        ladd f hf _ (Submodule.smul_mem _ _ (hψ a)) _ (sum_mem fun τ _ => Submodule.smul_mem _ _ (hψ τ)), ih,
        lsmul]
  have hh : ∀ w, O.h w φ ∈ Fock D.δ := by
    intro w
    have e : O.h w φ = ∑ i, O.x w i (O.d w i φ) + (φ + φ) := by
      have h2 : (2 : Module.End ℂ (S4 F)) = 1 + 1 := one_add_one_eq_two.symm
      simp [Fo.Ops.h, h2, LinearMap.sum_apply]
    rw [e]
    exact add_mem (sum_mem fun i _ => (opsFock F E D O w i _ (opsFock F E D O w i φ hφ).2).1) (add_mem hφ hφ)
  have hd := dLFock F E D O Y φ hφ
  have e1 : O.dL D (Y + zE s) φ = O.dL D Y φ + (-1 : ℂ) • ∑ τ : E →+* ℂ, coord τ s • O.h (Fo.pl F τ) φ := by
    rw [hdadd, (hcen s)]
    simp [LinearMap.sum_apply]
  have hS : ∑ τ : E →+* ℂ, coord τ s • O.h (Fo.pl F τ) φ ∈ Fock D.δ :=
    sum_mem fun τ _ => Submodule.smul_mem _ _ (hh _)
  have e2 : (TR.lie F 2 (zF (trI F s)) f) = ∑ τ : E →+* ℂ, coord τ s • (TR.Eop (Fo.pl F τ) 0 0 f + TR.Eop (Fo.pl F τ) 1 1 f) := by
    rw [htr s]
    simp [LinearMap.sum_apply]
  have ePlus : ∀ w, lift W M (TR.Eop w 0 0 f + TR.Eop w 1 1 f : TR.Sm F 2).1 φ =
      lift W M (TR.Eop w 0 0 f).1 φ + lift W M (TR.Eop w 1 1 f).1 φ := fun w =>
    radd _ (hE w 0 0) _ (hE w 1 1) φ hφ
  have eMinus : ∀ w, lift W M (TR.Eop w 0 0 f - TR.Eop w 1 1 f : TR.Sm F 2).1 φ =
      lift W M (TR.Eop w 0 0 f).1 φ - lift W M (TR.Eop w 1 1 f).1 φ := by
    intro w
    have e : (TR.Eop w 0 0 f - TR.Eop w 1 1 f : TR.Sm F 2) = TR.Eop w 0 0 f + (-1 : ℂ) • TR.Eop w 1 1 f := by
      rw [neg_one_smul, sub_eq_add_neg]
    rw [e, radd _ (hE w 0 0) _ (π.V.smul_mem _ (hE w 1 1)) φ hφ]
    have := rsmul (TR.Eop w 1 1 f).1 (-1) φ
    change _ + lift W M ((-1 : ℂ) • (TR.Eop w 1 1 f).1) φ = _
    rw [this, neg_one_smul, sub_eq_add_neg]
  have hlhs : (lie E 2 (Y + zE s) Φ).1 h = lift W M f.1 (O.dL D Y φ) h +
      lift W M (TR.lie F 2 (zF (trI F s)) f).1 φ h := by
    rw [map_add, LinearMap.add_apply]
    change (lie E 2 Y Φ).1 h + (lie E 2 (zE s) Φ).1 h = _
    rw [hL, hZ]
  rw [hlhs, e1, ladd f hf _ hd _ (Submodule.smul_mem _ _ hS), lsmul, sumP _ _ _ (fun τ => hh _), e2,
    sumF _ _ _ (fun τ => add_mem (hE _ 0 0) (hE _ 1 1)), hs]
  simp only [ePlus, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hHh : ∀ w, lift W M f.1 (O.h w φ) h =
      -(lift W M (TR.Eop w 0 0 f).1 φ h - lift W M (TR.Eop w 1 1 f).1 φ h) := fun w => by
    rw [hH w h, eMinus]; rfl
  simp only [hHh, map_add, add_mul, Finset.mul_sum]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring
