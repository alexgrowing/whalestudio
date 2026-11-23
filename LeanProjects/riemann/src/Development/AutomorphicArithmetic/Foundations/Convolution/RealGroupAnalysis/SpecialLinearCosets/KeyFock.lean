import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Decomp
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.ModSpan
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.KeyPure
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CompCoordMem
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.ThetaIntegralExistsBilinear
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.WeilLiftEquivariance
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.FstDetFin
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ContMkE
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SpanCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Exp
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem keyFock {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2)
    (v : P F) (θ : Kv v) (J : GLv v →* GL (Fin 2) (A E)) (hJ : Splt D v θ J)
    (h' : GL (Fin 2) (A E)) (hc : ∀ s, Commute h' (nbar D v θ s)) (f) (hf : f ∈ π.V)
    (φ : S4 F) (hφ : φ ∈ Fock D.δ) :
    (fun x => W1 W M f.1 φ (h' * J x)) ∈ MC (π.locRep v) := by
  obtain ⟨T, hT⟩ := UpperTheory.ConvolutionTheory.R2.I.ptMem F v
  have lin : ∀ h, ∃ B : Fock (F := F) D.δ →ₗ[ℂ] ℂ, ∀ φ : Fock (F := F) D.δ, B φ = W1 W M f.1 φ.1 h := by
    intro h
    obtain ⟨B, hB⟩ := UpperTheory.ConvolutionTheory.R2.I.thetaIntegral_exists_bilinear F E D W M π h
    exact ⟨B ⟨f, hf⟩, fun φ => hB ⟨f, hf⟩ φ⟩
  have main := Submodule.span_induction
    (p := fun φ _ => φ ∈ Fock (F := F) D.δ ∧ (fun x => W1 W M f.1 φ (h' * J x)) ∈ MC (π.locRep v))
    ?_ ?_ ?_ ?_ (UpperTheory.ConvolutionTheory.R2.I.modSpan F E D W v θ hJ.sq hJ.ne hφ)
  · exact main.2
  · rintro φ ⟨u, a, hu, ha, e⟩
    obtain ⟨φ₀, h₀, e₀⟩ := hu.1 _ (T ⟨a, ha⟩).2
    have hφ₀ : φ = φ₀ := Subtype.ext (by rw [e, e₀, hT])
    exact ⟨hφ₀ ▸ h₀, UpperTheory.ConvolutionTheory.R2.I.keyPure F E D W M π v θ J hJ h' hc u hu a ha φ e f hf⟩
  · refine ⟨zero_mem _, ?_⟩
    have : (fun x => W1 W M f.1 (0 : S4 F) (h' * J x)) = 0 := by
      funext x
      obtain ⟨B, hB⟩ := lin (h' * J x)
      simpa using (hB 0).symm
    rw [this]
    exact zero_mem _
  · rintro a b _ _ ⟨ha, ia⟩ ⟨hb, ib⟩
    refine ⟨add_mem ha hb, ?_⟩
    have : (fun x => W1 W M f.1 (a + b) (h' * J x)) =
        (fun x => W1 W M f.1 a (h' * J x)) + fun x => W1 W M f.1 b (h' * J x) := by
      funext x
      obtain ⟨B, hB⟩ := lin (h' * J x)
      have e := map_add B ⟨a, ha⟩ ⟨b, hb⟩
      rw [hB, hB, hB] at e
      exact e
    rw [this]
    exact add_mem ia ib
  · rintro c a _ ⟨ha, ia⟩
    refine ⟨Submodule.smul_mem _ c ha, ?_⟩
    have : (fun x => W1 W M f.1 (c • a) (h' * J x)) = c • fun x => W1 W M f.1 a (h' * J x) := by
      funext x
      obtain ⟨B, hB⟩ := lin (h' * J x)
      have e := map_smul B c (⟨a, ha⟩ : Fock (F := F) D.δ)
      rw [hB, hB] at e
      exact e
    rw [this]
    exact Submodule.smul_mem _ c ia

theorem UpperTheory.ConvolutionTheory.R2.I.key :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (v : P F) (θ : Kv v) (J : GLv v →* GL (Fin 2) (A E)), Splt D v θ J →
      ∀ Φ ∈ span W M π, ∀ h, (fun x => WE D Φ.1 (h * J x)) ∈ MC (π.locRep v) := by
  intro F E _ _ _ _ _ _ _ D W M π v θ J hJ Φ hΦ
  have lift_mem : ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h,
      (fun x => WE D (lift W M f.1 φ) (h * J x)) ∈ MC (π.locRep v) := by
    intro f hf φ hφ h
    obtain ⟨h', k, rfl, hc, hk⟩ := UpperTheory.ConvolutionTheory.R2.I.decomp F E D v θ J hJ h
    obtain ⟨f', hf', e'⟩ := (UpperTheory.ConvolutionTheory.R2.I.locSm F π v).2.2 E D k f hf
    have hL : W.L (finGL E 2 k) φ ∈ Fock D.δ := (UpperTheory.ConvolutionTheory.R2.fockSt F E D W).fin k φ hφ
    have : (fun x => WE D (lift W M f.1 φ) (h' * finGL E 2 k * J x)) =
        fun x => W1 W M f'.1 (W.L (finGL E 2 k) φ) (h' * J x) := by
      funext x
      rw [UpperTheory.ConvolutionTheory.R2.exp F E D W M π f hf φ hφ, mul_assoc, (hk x).eq, ← mul_assoc,
        (UpperTheory.ConvolutionTheory.R2.I.weilLift_equivariance F E D W M f.1 φ (h' * J x)).1, e']
    rw [this]
    exact keyFock D W M π v θ J hJ h' hc f' hf' _ hL
  have main := Submodule.span_induction
    (p := fun Φ _ => ∀ h, (fun x => WE D Φ.1 (h * J x)) ∈ MC (π.locRep v)) ?_ ?_ ?_ ?_ hΦ
  · exact main
  · rintro Φ ⟨f, hf, φ, hφ, e⟩ h
    rw [e]
    exact lift_mem f hf φ hφ h
  · intro h
    have : (fun x => WE D (0 : Sm E 2).1 (h * J x)) = 0 := by
      funext x
      simp [WE]
    rw [this]
    exact zero_mem _
  · rintro a b ha hb ia ib h
    have ca := (UpperTheory.ConvolutionTheory.R2.H.spanCont F E D W M π a ha).1
    have cb := (UpperTheory.ConvolutionTheory.R2.H.spanCont F E D W M π b hb).1
    have : (fun x => WE D (a + b).1 (h * J x)) =
        (fun x => WE D a.1 (h * J x)) + fun x => WE D b.1 (h * J x) := by
      funext x
      have e := (UpperTheory.ConvolutionTheory.R2.H.weEig F E D a.1 ca).2.2 b.1 1 cb (h * J x)
      simpa using e
    rw [this]
    exact add_mem (ia h) (ib h)
  · rintro c a ha ia h
    have ca := (UpperTheory.ConvolutionTheory.R2.H.spanCont F E D W M π a ha).1
    have : (fun x => WE D (c • a).1 (h * J x)) = c • fun x => WE D a.1 (h * J x) := by
      funext x
      have e := (UpperTheory.ConvolutionTheory.R2.H.weEig F E D 0 continuous_const).2.2 a.1 c ca (h * J x)
      simpa [WE] using e
    rw [this]
    exact Submodule.smul_mem _ c (ia h)
