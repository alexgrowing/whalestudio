import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.AffChar
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import GroundTheory.AutomorphicForms.HarishChandraCentre
import GroundTheory.AutomorphicForms.AffineBruhat
import GroundTheory.AutomorphicForms.Cartan

noncomputable section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Fx
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type) [Field K] [NumberField K] (n : ℕ)

abbrev Pl : Type := HeightOneSpectrum (𝓞 K)

abbrev Ix : Type := (K →+* ℂ) × Fin n

abbrev TG : Type := CompactlySupportedContinuousMap (normOneGL K n) ℂ

abbrev TI : Type := CompactlySupportedContinuousMap (archGroup K n) ℂ

abbrev TF : Type := CompactlySupportedContinuousMap (AdelicGLn.FiniteAdelicGL K n) ℂ

abbrev UC : Type := ℂ ⊗[ℝ] UEnv K n

abbrev PR : Type := MvPolynomial (Pl K × Fin n) (MvPolynomial (Option (Ix K n)) ℂ)

variable {K n}

section Test

def tensFun (β : TI K n) (e : TF K n) (x : normOneGL K n) : ℂ :=
  kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) * e (finPart K n (x : AdelicGLn.AdelicGL K n))

open Classical in

def tens (β : TI K n) (e : TF K n) : TG K n :=
  if h : Continuous (tensFun β e) ∧ HasCompactSupport (tensFun β e) then ⟨⟨tensFun β e, h.1⟩, h.2⟩ else 0

def rUC : UC K n →ₐ[ℂ] Module.End ℂ ((isExpLieAlgebra K n).smoothFuns (F := ℂ)) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ _) (isExpLieAlgebra K n).rightUAction
    fun c _ => Algebra.commute_algebraMap_left c _

def uAct : UC K n →ₐ[ℂ] Module.End ℂ (archSmooth K n) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ _) uAction fun c _ => Algebra.commute_algebraMap_left c _

open Classical in

def lact (u : UC K n) (β : TI K n) : TI K n :=
  if h : ∃ (h : (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)) (γ : TI K n),
      ∀ g, γ g = (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹ then h.choose_spec.choose else 0

def SmoothT (β : TI K n) : Prop := (isExpLieAlgebra K n).IsSmoothFun fun g => β g

def LeftFin (β : TI K n) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : archCompact K n => fun g : archGroup K n => β ((k : archGroup K n) * g)))

open Classical in

def along (τ : K →+* ℂ) (z : ℂ) : mixedEmbedding.mixedSpace K :=
  (0, fun w => if w.1 = InfinitePlace.mk τ then (if w.1.embedding = τ then z else starRingEnd ℂ z) else 0)

def elem (τ : K →+* ℂ) (a b : Fin n) (z : ℂ) : UEnv K n :=
  UniversalEnvelopingAlgebra.ι ℝ ((isExpLieAlgebra K n).toLie
    ⟨(Matrix.single a b (along τ z) : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)), Submodule.mem_top⟩)

def IsJ (τ : K →+* ℂ) (j : HarishChandra.U n →ₐ[ℂ] UC K n) : Prop :=
  ∀ a b, j (HarishChandra.e (a, b)) = (2⁻¹ : ℂ) ⊗ₜ elem τ a b 1 - (2⁻¹ * Complex.I) ⊗ₜ elem τ a b Complex.I

def zc (τ : K →+* ℂ) (i : Fin n) : UC K n :=
  Classical.epsilon fun z => ∃ j, IsJ τ j ∧ z = j ((HarishChandra.harishChandraEquiv (n := n)).symm
    ⟨esymm (Fin n) ℂ (i + 1), esymm_isSymmetric (Fin n) ℂ (i + 1)⟩ : Subalgebra.center ℂ (HarishChandra.U n))

end Test

section Ops

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

def Oinf (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : TI K n) : LL μ →L[ℂ] LL μ :=
  ((rightRegularRep (rationalGLOne K n) μ).compHom (archP K n) continuous_archP).integrated ν (UnitaryRep.ccToL1 ν β)

def Ofin (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (e : TF K n) : LL μ →L[ℂ] LL μ :=
  ((rightRegularRep (rationalGLOne K n) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj).integrated m
    (UnitaryRep.ccToL1 m e)

def Compat (ν : Measure (archGroup K n)) (m : Measure (AdelicGLn.FiniteAdelicGL K n)) : Prop :=
  ∀ (β : TI K n) (e : TF K n) (Θ : normOneGL K n → ℂ), Continuous Θ →
    ∫ x, tens β e x * Θ x ∂μ = ∫ a, ∫ h, β a * e h * Θ (archP K n a * MultiplicityOne.finProj K n h) ∂m ∂ν

def rhoF (h : AdelicGLn.FiniteAdelicGL K n) : LL μ →L[ℂ] LL μ :=
  rightRegularRep (rationalGLOne K n) μ (MultiplicityOne.finProj K n h)

def rhoL (w : Pl K) (g : GL (Fin n) (w.adicCompletion K)) : LL μ →L[ℂ] LL μ := rhoF μ (AdelicGLn.localEmbedding w g)

def fixF (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) : Submodule ℂ (LL μ) :=
  ⨅ u ∈ U, LinearMap.eqLocus (rhoF μ u : LL μ →ₗ[ℂ] LL μ) LinearMap.id

def fixL (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) : Submodule ℂ (LL μ) := fixF μ (J.map (AdelicGLn.localEmbedding w))

def Hop (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (x : GL (Fin n) (w.adicCompletion K)) : LL μ →L[ℂ] LL μ :=
  (∑ᶠ c ∈ {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}, rhoL μ w c.out) ∘L prj (fixL μ w J)

def Tsph (w : Pl K) (i : Fin n) : LL μ →L[ℂ] LL μ :=
  (((Ideal.absNorm w.asIdeal : ℝ) ^ (-((((i : ℕ) + 1) * (n - ((i : ℕ) + 1)) : ℕ) : ℝ) / 2) : ℝ) : ℂ) •
    Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) (Cartan.diagPow (w.adicCompletion K) n fun a => if a ≤ i then 1 else 0)

def Uiw (w : Pl K) (ν : Fin n → ℤ) : LL μ →L[ℂ] LL μ :=
  Hop μ w (GLnLocal.iwahori (w.adicCompletion K) n) (Cartan.diagPow (w.adicCompletion K) n ν)

def SInf (V : Submodule ℂ (LL μ)) (τ : K →+* ℂ) (m : Multiset ℂ) : Prop :=
  m.card = n ∧ ∀ (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : TI K n), SmoothT β → ∀ (i : Fin n), ∀ v ∈ V,
    Oinf μ ν (lact (zc τ i) β) v = m.esymm (i + 1) • Oinf μ ν β v

def SSat (V : Submodule ℂ (LL μ)) (w : Pl K) (B : Multiset ℂ) : Prop :=
  B.card = n ∧ V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n) ≠ ⊥ ∧
    ∀ (i : Fin n), ∀ v ∈ V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n), Tsph μ w i v = B.esymm (i + 1) • v

def At (S : Set (Pl K)) (V : Submodule ℂ (LL μ)) (Λ : (K →+* ℂ) → Multiset ℂ) (t : Pl K → Multiset ℂ) : Prop :=
  (∀ τ, SInf μ V τ (Λ τ)) ∧ ∀ w ∉ S, SSat μ V w (t w)

structure Amp where
  ν : Measure (archGroup K n)
  [haar : ν.IsHaarMeasure]
  a₀ : TI K n
  smooth : SmoothT a₀
  fin : LeftFin a₀
  S : Set (Pl K)
  finS : S.Finite
  U : Subgroup (AdelicGLn.FiniteAdelicGL K n)
  le : U ≤ AdelicGLn.integralFiniteGL K n
  isOpen : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n))
  max : ∀ w ∉ S, (GLnLocal.integralGL (w.adicCompletion K) n).map (AdelicGLn.localEmbedding w) ≤ U
  pos : 0 ≤ Oinf μ ν a₀
  norm_le : ‖Oinf μ ν a₀‖ ≤ 1

attribute [instance] Amp.haar

variable {μ}

def Amp.A (𝔞 : Amp μ) : LL μ →L[ℂ] LL μ := Oinf μ 𝔞.ν 𝔞.a₀ ∘L prj (fixF μ 𝔞.U)

def Amp.Z (𝔞 : Amp μ) (x : Ix K n) : LL μ →L[ℂ] LL μ := Oinf μ 𝔞.ν (lact (zc x.1 x.2) 𝔞.a₀) ∘L prj (fixF μ 𝔞.U)

structure Amp.IsEv (𝔞 : Amp μ) (ev : PR K n →+* (LL μ →L[ℂ] LL μ)) : Prop where
  const : ∀ c : ℂ, ev (C (C c)) = c • 1
  amp : ev (C (X none)) = 𝔞.A
  cen : ∀ x, ev (C (X (some x))) = 𝔞.Z x
  hecke : ∀ w ∉ 𝔞.S, ∀ i, ev (X (w, i)) = Tsph μ w i

end Ops

section Points

def msOf (L : Ix K n → ℂ) (τ : K →+* ℂ) : Multiset ℂ := Finset.univ.val.map fun i => L (τ, i)

def hval (t : Pl K → Multiset ℂ) (x : Pl K × Fin n) : ℂ := (t x.1).esymm (x.2 + 1)

variable (K n) in

structure Datum where
  r : ℕ
  two : 2 ≤ r
  d : Fin r → ℕ
  pos : ∀ i, 0 < d i
  sum : ∑ i, d i = n
  μ : ∀ i, Measure (normOneGL K (d i))
  [haar : ∀ i, (μ i).IsHaarMeasure]
  V : ∀ i, Submodule ℂ (LL (μ i))
  summand : ∀ i, IsSummand (μ i) (V i)

attribute [instance] Datum.haar

def Datum.Pt (b : Datum K n) (S : Set (Pl K)) (Λ : (K →+* ℂ) → Multiset ℂ) (t : Pl K → Multiset ℂ) : Prop :=
  ∃ (lam : Fin b.r → ℂ) (m : Fin b.r → (K →+* ℂ) → Multiset ℂ) (B : Fin b.r → Pl K → Multiset ℂ),
    (∀ i, At (b.μ i) S (b.V i) (m i) (B i)) ∧ (∀ τ, Λ τ = ∑ i, (m i τ).map (· + lam i)) ∧
      ∀ w ∉ S, t w = ∑ i, (B i w).map (· * (Ideal.absNorm w.asIdeal : ℂ) ^ (-lam i))

open Classical in

def admitted (S : Set (Pl K)) (F : KF (Ix K n) (Pl K × Fin n)) : Prop :=
  (∀ w : (K →+* ℂ) → Equiv.Perm (Fin n), map (ren fun x : Ix K n => (x.1, w x.1 x.2)) F = F) ∧ ∀ x ∈ F.vars, x.1 ∉ S

def Kills (S : Set (Pl K)) (F : KF (Ix K n) (Pl K × Fin n)) (b : Datum K n) : Prop :=
  ∀ (L : Ix K n → ℂ) (t : Pl K → Multiset ℂ), b.Pt S (msOf L) t → evK L (hval t) F = 0

def homog {ι : Type} (d : ℕ) (p : MvPolynomial ι ℂ) : MvPolynomial (Option ι) ℂ :=
  ∑ α ∈ p.support, X none ^ (d - α.degree) * rename some (monomial α (p.coeff α))

def trunc (d : ℕ) (G : ℕ → MvPolynomial (Pl K × Fin n) (MvPolynomial (Ix K n) ℂ)) : PR K n :=
  ∑ k ∈ Finset.range (d + 1), ∑ β ∈ (G k).support, monomial β (homog d ((G k).coeff β))

def IsGen (F : KF (Ix K n) (Pl K × Fin n)) (G : ℕ → MvPolynomial (Pl K × Fin n) (MvPolynomial (Ix K n) ℂ)) : Prop :=
  ∀ k, map (aeval blockE : MvPolynomial (Ix K n) ℂ →ₐ[ℂ] MvPolynomial (Ix K n) ℂ).toRingHom (G k) = pieceK k F

def powE (f : ℕ) (i : Fin n) : MvPolynomial (Fin n) ℂ :=
  (esymmAlgEquiv (Fin n) ℂ (Fintype.card_fin n)).symm ⟨expand f (esymm (Fin n) ℂ (i + 1)), fun w => by
    rw [rename_expand, esymm_isSymmetric]⟩

variable (F : Type) [Field F] [NumberField F] [Algebra F K]

def resDeg (w : Pl K) : ℕ := w.asIdeal.inertiaDeg (𝓞 F)

def bcPR : PR K n →+* PR F n :=
  eval₂Hom (C.comp (rename (Option.map fun x : Ix K n => (x.1.comp (algebraMap F K), x.2))).toRingHom) fun x =>
    map C (rename (fun i => (x.1.under (𝓞 F), i)) (powE (resDeg F x.1) x.2))

variable {F}

def bcInf (Λ : (F →+* ℂ) → Multiset ℂ) (τ : K →+* ℂ) : Multiset ℂ := Λ (τ.comp (algebraMap F K))

def bcSat (t : Pl F → Multiset ℂ) (w : Pl K) : Multiset ℂ := (t (w.under (𝓞 F))).map (· ^ resDeg F w)

end Points

end UpperTheory.ConvolutionTheory
