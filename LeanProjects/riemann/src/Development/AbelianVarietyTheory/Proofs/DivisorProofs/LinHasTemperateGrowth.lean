import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeIncInf
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0

noncomputable section

open scoped Classical

namespace GlobalTheory.ThK.EvAt0.PolD

variable {F : Type} [Field F] [NumberField F]

def linL {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) :
    (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) ∘ₗ
      ∑ i, (LinearMap.mulRight ℝ (b i)) ∘ₗ LinearMap.proj i)

theorem linL_apply {κ : Type} [Fintype κ] (b x : κ → mixedEmbedding.mixedSpace F) :
    linL b x = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * b i) := by
  simp [linL]

def lin {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) (x : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * b i) : ℝ) : ℂ)

theorem lin_hasTemperateGrowth {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) :
    (lin b).HasTemperateGrowth := by
  have e : lin b = ⇑(Complex.ofRealCLM.comp (linL b)) := by
    funext x; simp [lin, linL_apply]
  rw [e]
  exact (Complex.ofRealCLM.comp (linL b)).hasTemperateGrowth

def mulOp {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) : SInf F κ →L[ℂ] SInf F κ :=
  SchwartzMap.smulLeftCLM ℂ (lin b)

theorem mulOp_apply {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ)
    (x : κ → mixedEmbedding.mixedSpace F) : mulOp b f x = lin b x * f x := by
  simp [mulOp, SchwartzMap.smulLeftCLM_apply_apply (lin_hasTemperateGrowth b)]

def dOp {κ : Type} [Fintype κ] (a b : κ → mixedEmbedding.mixedSpace F) : SInf F κ →L[ℂ] SInf F κ :=
  LineDeriv.lineDerivOpCLM ℂ (SInf F κ) a - ((2 * Real.pi * Complex.I : ℂ)) • mulOp b

theorem dOp_apply {κ : Type} [Fintype κ] (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ)
    (x : κ → mixedEmbedding.mixedSpace F) :
    dOp a b f x = fderiv ℝ f x a - 2 * Real.pi * Complex.I * lin b x * f x := by
  simp [dOp, mulOp_apply, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  ring

def arc {κ : Type} (c : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (c i)

def liftA (v : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm v)

theorem evI_liftA (v : mixedEmbedding.mixedSpace F) : evI F (liftA v) = v := by
  simp [evI, liftA]

theorem smul_liftA {c : AF F} (hc : evI F c = 0) (v : mixedEmbedding.mixedSpace F) : c • liftA v = 0 := by
  have h1 : c.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hc)
  have key : ∀ x y : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F, x.1 = 0 → y.2 = 0 → x * y = 0 :=
    fun x y hx hy => Prod.ext (by simp [hx]) (by simp [hy])
  exact key c (liftA v) h1 rfl

variable {n d d₁ : ℕ}

def pd (h : d = d₁ + 2) (p : Fin n × Fin 2 → mixedEmbedding.mixedSpace F) :
    SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) :=
  LineDeriv.lineDerivOpCLM ℂ (SInf F (Fin n × Fin d)) (glue h (0 : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) p)

def iter (h : d = d₁ + 2) (l : List (Fin n × Fin 2 → mixedEmbedding.mixedSpace F)) :
    SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) :=
  l.foldr (fun p T => T ∘L pd h p) (ContinuousLinearMap.id ℂ _)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def GaussD {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (g : SInf F (Fin n × Fin d)) : Prop :=
  ∃ ε : InfinitePlace F → ℤˣ, ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
    (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
    dOp (arc (M.co.e u').1) (arc (M.co.e u').2) g = Complex.I • dOp (arc (M.co.e u).1) (arc (M.co.e u).2) g

end GlobalTheory.ThK.EvAt0.PolD
