import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import GroundTheory.AutomorphicForms.StrongApproximationSLDense

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt GoodAt)
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.H

section Base

variable {K : Type} [Field K] [NumberField K]

abbrev P (K : Type) [Field K] [NumberField K] : Type := HeightOneSpectrum (𝓞 K)

abbrev Kv (v : P K) : Type := v.adicCompletion K

def sg (v : P K) (x : Kv v) : A K :=
  ((0, GroundTheory.Automorphic.AdelicGLn.finiteAdeleSingleAdd v x) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

def lc (v : P K) : GL (Fin 2) (Kv v) →* GL (Fin 2) (A K) := (finGL K 2).comp (locGL K 2 v)

def cp (v : P K) : A K →+* Kv v := (pLoc K v).comp (pFin K)

def idl (v : P K) (x : (Kv v)ˣ) : (A K)ˣ := localIdele K v x

def IsInt {v : P K} (x : Kv v) : Prop := Valued.v x ≤ 1

def IsU {v : P K} (ϖ : (Kv v)ˣ) : Prop := Formalism.UG.IsUnifV K v (ϖ : Kv v)

def q (v : P K) : ℂ := (Ideal.absNorm v.asIdeal : ℕ)

def nL {v : P K} (b : Kv v) : GL (Fin 2) (Kv v) :=
  ⟨!![1, b; 0, 1], !![1, -b; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

def dL {v : P K} (a d : (Kv v)ˣ) : GL (Fin 2) (Kv v) :=
  ⟨!![(a : Kv v), 0; 0, (d : Kv v)], !![((a⁻¹ : (Kv v)ˣ) : Kv v), 0; 0, ((d⁻¹ : (Kv v)ˣ) : Kv v)],
    by ext i j; fin_cases i <;> fin_cases j <;> simp, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

def KAt (v : P K) (g : GL (Fin 2) (A K)) : Prop := Matrix.GeneralLinearGroup.map (cp v) g ∈ GlobalTheory.LFun.KGL v 2

def Fix (v : P K) (f : GL (Fin 2) (A K) → ℂ) : Prop := ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL v 2, f (g * lc v k) = f g

def Good {v : P K} (χ : Kv v → ℂ) : Prop :=
  (∀ x y, χ (x + y) = χ x * χ y) ∧ (∀ x, IsInt x → χ x = 1) ∧ ∀ x, (∀ c, IsInt c → χ (c * x) = 1) → IsInt x

def IsJ (v : P K) (j : Matrix.SpecialLinearGroup (Fin 2) (Kv v) →* G1 K) : Prop :=
  ∀ x, gl (j x) = lc v (Matrix.SpecialLinearGroup.toGL x)

def Std (v : P K) (φ : V4 K → ℂ) : Prop :=
  (∀ x, φ x ≠ 0 → ∀ i, IsInt (cp v (x i))) ∧ ∀ x (y : Fin 4 → Kv v), (∀ i, IsInt (y i)) → φ (fun i => x i + sg v (y i)) = φ x

structure Gd (δ : K) (v : P K) : Prop where
  psi : Good fun x : Kv v => ψ (sg v x)
  two : Valued.v (2 : Kv v) = 1
  del : Valued.v (algebraMap K (Kv v) δ) = 1

def Aniso (δ : K) (v : P K) : Prop :=
  ∀ u t : Kv v, Valued.v (u ^ 2 - algebraMap K (Kv v) δ * t ^ 2) = max (Valued.v u) (Valued.v t) ^ 2

def Sl0 (φ : V4 K → ℂ) : Prop := ∀ u t, hat φ ![0, 0, u, t] = 0

end Base

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def Below (v : P F) (w : P E) : Prop := v.asIdeal = w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))

structure Inert (D : Dat F E) (v : P F) (w : P E) : Prop where
  norm : normV w = normV v ^ 2
  aniso : Aniso D.δ v
  coord : ∃ e : Kv v × Kv v ≃+ Kv w, (∀ u t, sg w (e (u, t)) = D.mkE (sg v u) (sg v t)) ∧
    (∀ u t, Valued.v (e (u, t)) = max (Valued.v u) (Valued.v t)) ∧ (∀ c u t, e (c, 0) * e (u, t) = e (c * u, c * t)) ∧ e (1, 0) = 1
  unif : ∀ ϖ : (Kv v)ˣ, IsU ϖ → ∃ ϖ' : (Kv w)ˣ, IsU ϖ' ∧
    ((idl w ϖ' : (A E)ˣ) : A E) = D.mkE (idl v ϖ : (A F)ˣ) 0 ∧ ideleNorm F E (idl w ϖ') = idl v ϖ ^ 2

def SplitAt (v : P F) (w : P E) : Prop :=
  normV w = normV v ∧ ∃ i : Kv v ≃+* Kv w, Continuous i ∧ (∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) ∧
    ∀ x, Valued.v (i x) = Valued.v x

end Ext

end UpperTheory.ConvolutionTheory.R2.H

end
