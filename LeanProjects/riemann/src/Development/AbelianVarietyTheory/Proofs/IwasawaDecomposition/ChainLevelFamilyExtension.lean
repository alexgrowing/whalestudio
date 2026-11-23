import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfBases
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie

noncomputable section

namespace GlobalTheory.Mem.ColTie

theorem map_pairV_one {E K ι : Type} [Field E] [Field K] [StarRing K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K)
    (lam : ι → DomWeight n) (σ : K →+* ℂ) (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x)) (x y : VV K lam) :
    σ (pairV emb lam 1 x y) =
      pairB lam (MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map σ x.1)) (MvPolynomial.map σ y.1) := by
  have e : gramK emb (1 : Matrix (Fin n) (Fin n) E) = fun τ => (((1 : ι → GL (Fin n) K) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    funext τ
    rw [gramK, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  show σ (pairK lam (gramK emb 1) x y) = _
  rw [pairK_apply, e, pairP_eq_pairB, polyAction_one₂, GlobalTheory.PeriodOnStep.map_pairB, MvPolynomial.map_map,
    MvPolynomial.map_map]
  congr 2
  exact congrArg (fun f => MvPolynomial.map f (x : Pol K ι n)) (RingHom.ext fun a => hσ a)

end GlobalTheory.Mem.ColTie
