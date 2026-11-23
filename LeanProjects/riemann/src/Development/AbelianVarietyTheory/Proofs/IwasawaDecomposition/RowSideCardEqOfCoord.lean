import Mathlib
import Formalism.LocalToGlobal.Divisibility.RowSideTie

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem rowSide_card_eq_of_coord {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (X : RowSide D EE) {n d : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE)
    (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V) : n = d := by
  let bC : Module.Basis X.RR.ι ℂ EE := Module.Basis.mk X.jEE_basis.1 X.jEE_basis.2.ge
  let bL : Module.Basis (Fin d) D.what₂.LL X.RR.V := (Pi.basisFun D.what₂.LL (Fin d)).map e
  have e1 : Fin n ≃ X.RR.ι := b.toBasis.indexEquiv bC
  have e2 : X.RR.ι ≃ Fin d := X.RR.b.indexEquiv bL
  simpa using Fintype.card_congr (e1.trans e2)

theorem drows_eq_and_d0_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (S0 : IndefData (A.side P0 ψ0 Zs)) (S1 : IndefData (A.side Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A.side Ps ψs Zs)) (I : DivisionCompatibilityData D A P0 ψ0 Ps ψs Zs S0 S1 X0 Dc), D.what₂.Drows = S1.D ∧ D.what₂.D0 = S0.D := by
  intro D G _ _ Pl0 T A P0 ψ0 Ps ψs Zs S0 S1 X0 Dc I
  exact ⟨rowSide_card_eq_of_coord (RowSide.sharp D) D.what₂.onb I.eRR,
    rowSide_card_eq_of_coord X0.s D.what₂.onb0 I.eRR0⟩

end GlobalTheory
