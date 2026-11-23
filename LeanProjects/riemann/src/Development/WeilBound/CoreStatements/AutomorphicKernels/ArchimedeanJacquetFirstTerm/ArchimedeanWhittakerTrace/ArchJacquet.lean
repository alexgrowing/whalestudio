import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DefsPlus

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.FTA.FunctionalEquationHypotheses.B2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n}

def psT (ψ : AddChar (AF F) ℂ) {b : GL (Fin n ⊕ Fin n) E} (T : nF σ Y b) (β : nA σ Y b) : ℂ :=
  ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))

variable (σ Y) in

def nInf (b : GL (Fin n ⊕ Fin n) E) : AddSubgroup (nA σ Y b) where
  carrier := {β | finOne F • β.1 = 0}
  add_mem' := fun {x y} hx hy => by simp only [Set.mem_ofPred_eq, AddSubgroup.coe_add, smul_add] at *; rw [hx, hy, add_zero]
  zero_mem' := by simp
  neg_mem' := fun {x} hx => by simp only [Set.mem_ofPred_eq, AddSubgroup.coe_neg, smul_neg] at *; rw [hx, neg_zero]

variable (σ Y) in

def nFin (b : GL (Fin n ⊕ Fin n) E) : AddSubgroup (nA σ Y b) where
  carrier := {β | (1 - finOne F) • β.1 = 0}
  add_mem' := fun {x y} hx hy => by simp only [Set.mem_ofPred_eq, AddSubgroup.coe_add, smul_add] at *; rw [hx, hy, add_zero]
  zero_mem' := by simp
  neg_mem' := fun {x} hx => by simp only [Set.mem_ofPred_eq, AddSubgroup.coe_neg, smul_neg] at *; rw [hx, neg_zero]

def IsWeyl (b : GL (Fin n ⊕ Fin n) E) (w : G2 σ Y) : Prop := inFrame b w = incM F (b.1ᵀ * dbl Y.J * b.1.map σ)

structure Hyp (B : Base F E) (Y : Spc F E n) (χ : Chr F E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ) : Prop where
  good : B.IsGood σ
  hn : 1 ≤ n
  sign : ∃ r s, Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s
  hecke : IsHecke F E χ
  res : ∃ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c
  stab : IsStab2 B K
  hgt : IsHgt K a

def ArchJacquet : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ)
    (Y : Spc F E n) (χ : Chr F E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), Hyp B Y χ K a →
    ∀ (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f →
    ∀ (b : GL (Fin n ⊕ Fin n) E) (nb : nA σ Y b → G2 σ Y), IsFrame2 σ Y b → IsNMap b nb → ∀ (T : nF σ Y b), IsND T →
    ∀ w : G2 σ Y, IsWeyl b w → ∀ lamI : Measure (nInf σ Y b), lamI.IsAddHaarMeasure →
      ∃ H : ℂ → G2 σ Y → ℂ, (∀ y, Differentiable ℂ fun z => H z y) ∧ ∃ t : ℝ, ∀ z : ℂ, t < z.re → ∀ y : G2 σ Y,
        Integrable (fun β : nInf σ Y b => flat a f s₁ z (w * nb β.1 * y) * psT B.ψ T β.1) lamI ∧
        ∫ β, flat a f s₁ z (w * nb β.1 * y) * psT B.ψ T β.1 ∂lamI = H z y

end PositivityTheory.FTA.FunctionalEquationHypotheses.B2

end
