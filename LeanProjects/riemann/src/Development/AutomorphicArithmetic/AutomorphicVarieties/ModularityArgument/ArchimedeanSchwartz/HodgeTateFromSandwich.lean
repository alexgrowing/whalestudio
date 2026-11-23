import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.NormChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ShiftOf
import GroundTheory.AutomorphicForms.GL2.GJStandardLCuspidalGen

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal
open scoped SchwartzMap Classical

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Inf

def LocDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 1 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 K)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (v.adicCompletion K)) V), π.IsIrreducible → IsAdmissible π →
    ∀ (ξ : V) (ℓ : Module.Dual ℂ V), ℓ ∈ smoothVectors (Representation.dual π) →
    ∀ Φ : Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ, IsSchwartzBruhat Φ →
    ∃ (N D : ℂ → ℂ) (c : ℝ), IsExp N ∧ IsExp D ∧ D ≠ 0 ∧ ∀ s : ℂ, s.re < -c →
      zetaIntegral (localHaar n v) Φ (fun g => Parabolic.matrixCoeff (F := v.adicCompletion K) π ξ ℓ g⁻¹) (1 - s) * D s = N s

def LocUnr : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 1 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 K)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (v.adicCompletion K)) V), π.IsIrreducible → IsAdmissible π →
    fixedVectors π (integralGL (v.adicCompletion K) n) ≠ ⊥ → ∀ z : Fin n → ℂˣ,
    Spherical.IsSatakeParameter (F := v.adicCompletion K) π (localHaar n v) z → ∀ t : ℂ,
      LFunction (F := v.adicCompletion K) π t = ∏ i, (1 - (z i : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-t))⁻¹ ∧
      LFunction (F := v.adicCompletion K) (contragredient π) t =
        ∏ i, (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-t))⁻¹

def SatDict : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (σ : CuspSub K n)
    (h : Cm.carrier σ ≤ centralCuspForms K n) (D : AdelicDecomposition (Cm.toRep σ h).toModule)
    (v : HeightOneSpectrum (𝓞 K)) (B : Multiset ℂˣ), (CG.mk σ).HasSat v B →
    ∃ z : Fin n → ℂˣ, Spherical.IsSatakeParameter (F := v.adicCompletion K) (D.finite.π v) (localHaar n v) z ∧
      B = Finset.univ.val.map z

def CoefSm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ (μ : Measure (Reduction.normOneGL K n))
    [μ.IsHaarMeasure] (σ : CuspSub K n), Cm.carrier σ ≤ centralCuspForms K n → ∀ φ₂ : cuspForms K n,
    ∃ T : σ.V →ₗ[ℂ] Sm K n, (∀ φ : σ.V, (T φ).1 = GJGlobal.matrixCoeff μ φ.1.1 φ₂.1) ∧
      ∀ (τ : K →+* ℂ) (u : ℂ) (φ φ' : σ.V), φ'.1 = cap τ u φ.1 → T φ' = cap τ u (T φ)

def ArchShift : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ (ψ : Sm K n) (m : (K →+* ℂ) → Multiset ℂ),
    (∀ τ u, cap τ u ψ = ((m τ).map (u + ·)).prod • ψ) → ∀ fi : AdelicGLn.InfiniteAdelicGL K n → ℂ,
    (∀ x, fi x = ψ.1 ((AdelicGLn.prodEquiv K n).symm (x, 1))) → (∃ x, fi x ≠ 0) →
    ∀ (μ : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μ.IsHaarMeasure],
    ∃ (φ φ' : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ)) (k k' : ℂ), k ≠ 0 ∧ k' ≠ 0 ∧
      Differentiable ℂ (archZeta μ φ fi) ∧ archZeta μ φ fi ≠ 0 ∧
      (∀ s, archZeta μ φ' fi (s + 1) = k * (linPoly (∑ τ, m τ)).eval s * archZeta μ φ fi s) ∧
      ∀ (g : AdelicGLn.InfiniteAdelicGL K n → ℂ) (s : ℂ),
        archZeta μ (archMatrixFourier φ') g s = k' * archZeta μ (archMatrixFourier φ) g (s + 1)

def ArchBridge : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (μ : Measure (AdelicGLn.InfiniteAdelicGL K n))
    [μ.IsHaarMeasure], (∀ x, ∃ y, archComp K n (infGL K n y) = x) ∧
    (∀ y, (AdelicGLn.prodEquiv K n).symm (archComp K n (infGL K n y), 1) = infGL K n y) ∧
    (∀ y, archAbsDet (archComp K n (infGL K n y)) = nrm (toL y.val)) ∧
    ∃ (e : ℝ) (c c' : ℂ), e ≠ 0 ∧ c ≠ 0 ∧ c' ≠ 0 ∧ ∀ Φ : Lie K n → ℂ, IsTest Φ →
      ∃ φ : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ),
        (∀ (fi : AdelicGLn.InfiniteAdelicGL K n → ℂ) (f : Lie K n → ℂ), ContinuousOn f (invSet K n) →
          (∀ y, fi (archComp K n (infGL K n y)) = f (toL y.val)) → ∀ s : ℂ,
            archZeta μ φ fi s = c * ∫ x, Φ x * f x * ((nrm x : ℝ) : ℂ) ^ (s + ((n : ℂ) - 1) / 2 - n)) ∧
        ∀ y, archSchwartz (archMatrixFourier φ) (archComp K n (infGL K n y)).val = c' * four e Φ (toL y.val)

def BridgeOf : Prop := HaarL → ArchBridge
def ArchOf : Prop := ShiftL → FourD → TestEx → ArchBridge → ArchShift
def SideCenOf : Prop := ExpAlg → LocDual → LocUnr → SatDict → CoefSm → ArchShift → SideCen

end UpperTheory.V.Z.Inf
