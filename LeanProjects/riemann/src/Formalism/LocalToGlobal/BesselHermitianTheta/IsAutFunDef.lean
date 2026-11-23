import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev GA (V : HSp D) : Type := HA (AF D.host.F) D.sp.cm.sig V.gram

abbrev incA : D.host.E →+* AF D.host.F ⊗[D.host.F] D.host.E := inclR (F := D.host.F) (AF D.host.F)

variable {D}

def matHom (V : HSp D) : GA D V →* GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) :=
  (HR (AF D.host.F) D.sp.cm.sig V.gram).subtype

def infHom (V : HSp D) : GA D V →* GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
  (Formalism.UG.bc (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom).comp (matHom V)

def finHom (V : HSp D) : GA D V →* GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) :=
  (Formalism.UG.bc (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom).comp (matHom V)

def GfC (V : HSp D) : Subgroup (GA D V) := (infHom V).ker

def GinfC (V : HSp D) : Subgroup (GA D V) := (finHom V).ker

def GQ (V : HSp D) : Subgroup (GA D V) := HFinIn (AF D.host.F) D.sp.cm.sig V.gram

def IsInfFam (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) : Prop :=
  ∀ ρ, IsInfEmb (tauE D ρ) (θ ρ)

def IsAtTau (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GA D V) : Prop :=
  h ∈ GinfC V ∧ infMat D.sp.cm.sig V.gram (θ τ) h = g ∧ ∀ τ', τ' ≠ τ → infMat D.sp.cm.sig V.gram (θ τ') h = 1

structure IsAutFun (V : HSp D) (φ : GA D V → ℂ) : Prop where
  left : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g
  level : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g
  cont : Continuous φ

def rTr (V : HSp D) (k : GA D V) (φ : GA D V → ℂ) : GA D V → ℂ := fun g => φ (g * k)

structure IsAutFunDef (V : HSp D) (φ : GA D V → ℂ) : Prop extends IsAutFun V φ where
  kfin : FiniteDimensional ℂ (Submodule.span ℂ {ψ : GA D V → ℂ | ∃ k ∈ GinfC V, ψ = rTr V k φ})

def IsIsoFrame (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) : Prop :=
  0 < r ∧ LinearIndependent D.host.E C.transpose ∧ Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram * C = 0

def NI (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) : Subgroup (GA D V) :=
  Subgroup.closure {g | let m : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) := (matHom V g).1 - 1
    HMul.hMul m (C.map (incA D)) = 0 ∧
    HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D)) m = 0 ∧
    ∀ x : Fin V.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).mulVec x = 0 →
      ∃ a : Fin r → AF D.host.F ⊗[D.host.F] D.host.E,
        m.mulVec (fun i => incA D (x i)) = (C.map (incA D)).mulVec a}

def NIQ (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) : Subgroup (NI V C) :=
  (GQ V).subgroupOf (NI V C)

def IsCuspFun (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∀ (μ : Measure (NI V C)) (𝓕 : Set (NI V C)), μ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓕 μ →
      ∀ g, ∫ n in 𝓕, φ ((n : GA D V) * g) ∂μ = 0

def KsphC (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Set (GA D V) :=
  {h | h ∈ GfC V ∧
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      (finMat D.sp.cm.sig V.gram h).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)) ∧
    ∀ v ∈ S, (finMat D.sp.cm.sig V.gram h).map
      (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)) = 1}

def frameMat (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) : Matrix (Fin A.rank) (Fin B.rank) D.host.E :=
  LinearMap.toMatrix B.frame A.frame ι

def EmbRel (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (g : GA D A) (g' : GA D B) : Prop :=
  HMul.hMul ((matHom A g).1 : Matrix _ _ (AF D.host.F ⊗[D.host.F] D.host.E)) ((frameMat A B ι).map (incA D)) =
      HMul.hMul ((frameMat A B ι).map (incA D)) ((matHom B g').1 : Matrix _ _ (AF D.host.F ⊗[D.host.F] D.host.E)) ∧
  ∀ x : Fin A.rank → D.host.E,
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat A B ι) * A.gram).mulVec x = 0 →
      ((matHom A g).1 : Matrix _ _ (AF D.host.F ⊗[D.host.F] D.host.E)).mulVec (fun i => incA D (x i)) =
        fun i => incA D (x i)

end Formalism.L2.Theta

end
