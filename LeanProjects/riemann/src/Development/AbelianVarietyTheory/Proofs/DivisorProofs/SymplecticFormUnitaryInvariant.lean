import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SympInv
open Matrix
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem hTens_eq_trace (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    GlobalTheory.WeilM.hTens c JA JB x y = trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∀ i : α, ∑ k : α, ∑ l : β, x i j * JA i k * JB j l * c (y k l) =
      ∑ l : β, ∑ k : α, x i j * JA i k * c (y k l) * JB j l := fun i => by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact Finset.sum_comm

theorem hTens_act (JA : Matrix α α E) (JB : Matrix β β E) (G : Matrix α α E) (H : Matrix β β E)
    (hG : Gᵀ * JA * G.map c = JA) (hH : Hᵀ * JB * H.map c = JB) (x y : Matrix α β E) :
    GlobalTheory.WeilM.hTens c JA JB (G * x * Hᵀ) (G * y * Hᵀ) = GlobalTheory.WeilM.hTens c JA JB x y := by
  rw [hTens_eq_trace, hTens_eq_trace]
  have e1 : (G * y * Hᵀ).map c = G.map c * y.map c * (H.map c)ᵀ := by
    ext i j
    simp [Matrix.mul_apply, map_sum, map_mul]
  have e2 : (H.map c)ᵀ * JBᵀ * H = JBᵀ := by
    conv_rhs => rw [← hH]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [show H * (xᵀ * Gᵀ) * JA * (G.map c * y.map c * (H.map c)ᵀ) * JBᵀ =
      H * (xᵀ * (Gᵀ * JA * G.map c) * y.map c * ((H.map c)ᵀ * JBᵀ)) by simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm, hG, Matrix.mul_assoc _ _ H, e2]

end GlobalTheory.SympInv

namespace GlobalTheory.SympInv

theorem symp_act : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (g : UA σ X.J) (h : UA σ W.J) (x u : Matrix (Fin n) (Fin d) (AE F E)),
    symp (cA σ) (-1) (incM F X.J) (incM F W.J) (mat g * x * (mat h)ᵀ) (mat g * u * (mat h)ᵀ) =
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u := by
  intro F E _ _ _ _ _ σ n d X W g h x u
  have hg : (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J := g.2
  have hh : (mat h)ᵀ * incM F W.J * (mat h).map (cA σ) = incM F W.J := h.2
  unfold GlobalTheory.WeilM.symp
  rw [hTens_act (cA σ) (incM F X.J) (incM F W.J) (mat g) (mat h) hg hh x u]

end GlobalTheory.SympInv
