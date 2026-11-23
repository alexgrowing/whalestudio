import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.EtArchPf
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.EtaleProductPrimes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ParOfTraceOne
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.PhiNeOne

noncomputable section

namespace GlobalTheory.EtaProdCompare

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EtaleProductPrimes GlobalTheory.TorusFrameRigid

section Num

variable (E : Type) [Field E] [NumberField E]

def gap (r m r1 : ℕ) : ℝ := A E r m r1 * (1 + Real.log (2 * Real.pi - 1))

end Num

section Torus

variable {E : Type} [Field E] [NumberField E]

def FixBound (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (r1 Nc nt i : ℕ) (y : ℝ) : Prop :=
  ∃ (c : Fin (2 * r1 ^ 4 * i) → Fin nt → ℤ) (a : Fin (2 * r1 ^ 4 * i) → Fin nt → Fin X.r → Vsp X.dim),
    (∀ g t, |c g t| ≤ Nc) ∧ (∀ g t, TrOK X r1 (a g t)) ∧ y ≤ ∏ g, ∑ t, |(c g t : ℝ)| * thRat X s (a g t)

variable {X : PT E} {s : (Fin 1 → Vsp X.dim) → ℂ} {r1 i : ℕ} {y : ℝ}

theorem FixBound.prodBound {Nc nt : ℕ} {N : ℝ} (hN : (Nc : ℝ) ≤ N) (hn : nt ≤ r1 ^ (2 * PT.f E * X.r ^ 2))
    (h : FixBound X s r1 Nc nt i y) : ProdBound X s r1 N i y := by
  obtain ⟨c, a, hc, ha, hy⟩ := h
  exact ⟨fun _ => nt, c, a, fun _ => hn, fun g t => le_trans (by exact_mod_cast hc g t) hN, ha, hy⟩

variable {Y : PT E} {ψ : Vsp X.dim ≃ₗ[ℝ] Vsp Y.dim}

variable [IsCMField E] {r : ℕ} {Z : FD.Data E r} {x : FD.Frame Z.Ψ r}

theorem isTorusAt (A : TorusAt Z x) : IsTorusAt Z x A.T := TorusAtDataPf.torusAtIs_holds E r Z x A

end Torus

section Record

open Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) {j i : ℕ} (η : (recB h.toLawsCore).Cusp j (wEt D j i))

def nTerms (D : D7) : ℕ := 5 ^ (2 * PT.f D.host.E * D.R.r ^ 2)

def EtProdEps (N : ℝ) : Prop :=
  ∀ σ, GoodEmb T.Q.c σ → ∀ k, ∀ x ∈ ((T.U j σ).X k).dom,
    ∃ X : PT D.host.E, IsTorusAt ((T.U j σ).X k) x X ∧ (∃ w, EpsBy X w) ∧ ∃ s ∈ X.Sec 1 1, s ≠ 0 ∧
      ProdBound X s 5 N i (normAt T j σ (wEt D j i) η.1 k x)

theorem eta_product_of_torus_bound {Nc nt : ℕ} {N : ℝ} (hN : (Nc : ℝ) ≤ N) (hn : nt ≤ nTerms D)
    (H : Formalism.L2.Pj.EtProd h 5 Nc nt j i η) : EtaleProductPrimes.EtProd h N j i η := fun σ hσ k x hx => by
  obtain ⟨A, hA⟩ := H σ hσ k x hx
  exact ⟨A.T, isTorusAt A, A.s, A.s_mem, A.s_ne, FixBound.prodBound hN (by rw [torusAt_r A]; exact hn) hA⟩

end Record

end GlobalTheory.EtaProdCompare
