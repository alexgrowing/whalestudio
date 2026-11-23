import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply

noncomputable section

namespace GlobalTheory.ThK.PlaneEv

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def dH {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (a b : κ → mixedEmbedding.mixedSpace F)
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (x : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  fderiv ℝ f x a - 2 * Real.pi * Complex.I *
    (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * b i) : ℝ) * f x

def HasDH (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : Prop :=
  ∀ (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ), ∃ g : SInf F κ, ⇑g = dH a b ⇑f

def cw {F : Type} [Field F] [NumberField F] {V : Type} [AddCommGroup V] [Module (AF F) V] {B : V → V → AF F}
    {κ : Type} [Fintype κ] (co : Darboux B κ) (w : V) :
    (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) :=
  (fun i => evI F ((co.e w).1 i), fun i => evI F ((co.e w).2 i))

def IsPl {n d d₁ : ℕ} (hd : d = d₁ + 2) {R : Type} [Zero R] (γ : Fin n × Fin d → R) : Prop :=
  ∀ p, γ ((idx hd).symm (Sum.inl p)) = 0

theorem incM_map_piInf_emb {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m k : Type}
    (J : Matrix m k E) {w : InfinitePlace F} (τ : EmbOver E w) : (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem evI_zero_eq {F : Type} [Field F] [NumberField F] : evI F (0 : AF F) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : AF F).1 = 0
  rw [show (0 : AF F).1 = 0 from rfl, map_zero]

theorem at_mul_right_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b c : Type}
    [Fintype b] {z : Matrix a b (AE F E)} (hz : At (evI F) z) (N : Matrix b c (AE F E)) : At (evI F) (z * N) :=
  fun t ht => by rw [← Matrix.smul_mul, hz t ht, Matrix.zero_mul]

example {F : Type} [Field F] [NumberField F] (f : (Fin 1 → mixedEmbedding.mixedSpace F) → ℂ) (x : Fin 1 → mixedEmbedding.mixedSpace F) :
    dH 0 0 f x = fderiv ℝ f x 0 := by simp [dH]

end GlobalTheory.ThK.PlaneEv
