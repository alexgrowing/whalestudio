import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinateChangeRealisedWithDouble

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

abbrev K1 (m n : ℕ) : Type := (Fin m × Fin n × Fin 2) ⊕ (Fin m × Fin 2)

def eK (m : ℕ) {n N : ℕ} (h : n + 1 = N) : K1 m n ≃ Fin m × Fin N × Fin 2 where
  toFun k := Sum.elim (fun p : Fin m × Fin n × Fin 2 => (p.1, em0 h p.2.1, p.2.2)) (fun p : Fin m × Fin 2 => (p.1, i0 h, p.2)) k
  invFun k := if hk : k.2.1.1 < n then Sum.inl (k.1, ⟨k.2.1.1, hk⟩, k.2.2) else Sum.inr (k.1, k.2.2)
  left_inv k := by
    rcases k with ⟨a, j, t⟩ | ⟨a, t⟩
    · simp [em0]
    · simp [i0]
  right_inv k := by
    obtain ⟨a, j, t⟩ := k
    by_cases hk : j.1 < n
    · simp [hk, em0]
    · have : j = i0 h := Fin.ext (by simp [i0]; omega)
      subst this
      simp [i0]

def ext0 {m n N : ℕ} (h : n + 1 = N) (X : Mx F E m n) : Mx F E m N :=
  fun a i => if hi : i.1 < n then X a ⟨i.1, hi⟩ else 0

def frQ {m n : ℕ} (b : GL (Fin n ⊕ Fin n) E) (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E) := w * (incM F (b⁻¹).1)ᵀ

def emb {m n N : ℕ} (h : n + 1 = N) (b : GL (Fin n ⊕ Fin n) E) (bd : GL (Fin N ⊕ Fin N) E)
    (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin m) (Fin N ⊕ Fin N) (AE F E) :=
  ext0 h (frQ b w).toCols₁ * (incM F bd.1.toCols₁)ᵀ + ext0 h (frQ b w).toCols₂ * (incM F bd.1.toCols₂)ᵀ

def ChartFacts : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G) (ε : ℤˣ), 1 ≤ n → SignOK d Y → IsFrame2 σ Y b →
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε → IsJ d h b j →
  ∀ (dd0 : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))) (Fin d.m × Fin d.n × Fin 2))
    (dd' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) (Fin d.m × Fin n × Fin 2)),
    IsAdapted d.bs d.A d.Y d.b dd0 → IsAdapted d.bs d.A Y b dd' →
    (∀ w', (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e (emb h b d.b w') =
      (Sum.elim (dd'.e w').1 (0 : Fin d.m × Fin 2 → AF F), Sum.elim (dd'.e w').2 (0 : Fin d.m × Fin 2 → AF F))) ∧
    (∀ u v : Fin d.m × Fin 2 → AF F, ∃ w, (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w =
      (Sum.elim (0 : Fin d.m × Fin n × Fin 2 → AF F) u, Sum.elim (0 : Fin d.m × Fin n × Fin 2 → AF F) v)) ∧
    (∀ g w, ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w).1 ∘ Sum.inl = 0 →
      ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w).2 ∘ Sum.inl = 0 → actB (cA σ) (j g) w = w) ∧
    (∀ g (w' : Matrix (Fin d.m) (Fin n ⊕ Fin n) (AE F E)), actB (cA σ) (j g) (emb h b d.b w') = emb h b d.b (actB (cA σ) g w')) ∧
    ∀ (u : UA σ d.A.J) (w' : Matrix (Fin d.m) (Fin n ⊕ Fin n) (AE F E)), mat u * emb h b d.b w' = emb h b d.b (mat u * w')

end PositivityTheory.SiegelWeilFormula.Ald

end
