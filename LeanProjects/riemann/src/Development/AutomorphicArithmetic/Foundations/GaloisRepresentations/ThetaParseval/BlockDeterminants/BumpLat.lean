import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasAd

noncomputable section

open scoped Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.TP.BA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

abbrev sg (v : Pl F) (t : Fv F v) : AF F := PositivityTheory.ThKH.Iwas.sg v t

abbrev eM (v : Pl F) (n : ℕ) : Matrix (Fin n) (Fin n) (AE F E) := sg v 1 • (1 : Matrix (Fin n) (Fin n) (AE F E))

def Oh (E : Type) [Field E] [NumberField E] [Algebra F E] (v : Pl F) : AddSubgroup (AE F E) :=
  AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
    ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}

structure IsFr (X : Spc F E n) (v : Pl F) (b c : Matrix (Fin n) (Fin n) (AE F E)) : Prop where
  at_b : At (evFin F v) b
  at_c : At (evFin F v) c
  bc : b * c = eM v n
  cb : c * b = eM v n
  col : ∀ j, (fun i => b i j) ∈ PositivityTheory.ThK.latW X v
  coord : ∀ z ∈ PositivityTheory.ThK.latW X v, ∀ i, (c *ᵥ z) i ∈ Oh E v

def abelian₂ (v : Pl F) (b c : Matrix (Fin n) (Fin n) (AE F E)) : AddSubgroup (Matrix (Fin n) (Fin n) (AE F E)) where
  carrier := {a | At (evFin F v) a ∧ ∀ i j, (c * a * b) i j ∈ Oh E v}
  zero_mem' := ⟨fun u _ => smul_zero u, fun i j => by simp [zero_mem]⟩
  add_mem' := fun {a a'} h h' => ⟨fun u hu => by rw [smul_add, h.1 u hu, h'.1 u hu, add_zero], fun i j => by
    rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem (h.2 i j) (h'.2 i j)⟩
  neg_mem' := fun {a} h => ⟨fun u hu => by rw [smul_neg, h.1 u hu, neg_zero], fun i j => by
    rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem (h.2 i j)⟩

variable (σ : E →ₐ[F] E)

structure IsIsoW (W : Spc F E d) (v : Pl F) (Y : Matrix (Fin n) (Fin d) (AE F E)) (R : Matrix (Fin d) (Fin n) (AE F E)) : Prop where
  what₂ : ∀ i, Y i ∈ PositivityTheory.ThK.latW W v
  right : Y * R = eM v n
  gram : Y * incM F W.J * (Y.map (cA σ))ᵀ = 0
  coord : ∀ z ∈ PositivityTheory.ThK.latW W v, ∀ j, (z ᵥ* R) j ∈ Oh E v

structure LatData (X : Spc F E n) (W : Spc F E d) (v : Pl F) (Λ : AddSubgroup (Matrix (Fin n) (Fin n) (AE F E)))
    (x₁ : Matrix (Fin n) (Fin d) (AE F E)) (r : Matrix (Fin d) (Fin n) (AE F E)) (ϖ : Fv F v) : Prop where
  at_mem : ∀ a ∈ Λ, At (evFin F v) a
  one_mem : eM v n ∈ Λ
  mul_mem : ∀ a ∈ Λ, ∀ b ∈ Λ, a * b ∈ Λ
  smul_mem : ∀ t ∈ v.adicCompletionIntegers F, ∀ a ∈ Λ, sg v t • a ∈ Λ
  act : ∀ a ∈ Λ, ∀ γ ∈ latAtV X W v, a * γ ∈ latAtV X W v
  x_mem : x₁ ∈ latAtV X W v
  gram : x₁ * incM F W.J * (x₁.map (cA σ))ᵀ = 0
  right : x₁ * r = eM v n
  r_mem : ∀ γ ∈ latAtV X W v, γ * r ∈ Λ
  ϖ_ne : ϖ ≠ 0
  ϖ_mem : ϖ ∈ v.adicCompletionIntegers F
  unit : ∀ p ∈ Λ, ∃ q ∈ Λ, (eM v n + sg v ϖ • p) * q = eM v n
  small : ∀ U ∈ 𝓝 (1 : UA σ X.J), ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ g ∈ UAt σ X (evFin F v),
    (∃ a ∈ Λ, mat g - 1 = sg v (ϖ ^ k) • a) → (∃ a ∈ Λ, mat g⁻¹ - 1 = sg v (ϖ ^ k) • a) → g ∈ U
  nbhd : ∀ k : ℕ, ∃ O : Set (UA σ X.J), IsOpen O ∧ 1 ∈ O ∧ ∀ g ∈ UAt σ X (evFin F v), g ∈ O →
    (∃ a ∈ Λ, mat g - 1 = sg v (ϖ ^ k) • a) ∧ ∃ a ∈ Λ, mat g⁻¹ - 1 = sg v (ϖ ^ k) • a

end UpperTheory.TP.BA

end
