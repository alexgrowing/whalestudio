import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormOneOfPow

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix

section BC

variable {K K' : Type} [Field K] [Field K'] [CharZero K] [CharZero K'] (j : K →+* K') {ι : Type} [Fintype ι] {N n : ℕ}

theorem map_brStdP (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) (F : Formalism.L2.DIV.Pol K ι N) :
    map j (Formalism.L2.Col.Br.brStdP hN lam sg F : Formalism.L2.DIV.Pol K ι n) =
      (Formalism.L2.Col.Br.brStdP hN lam sg (map j F) : Formalism.L2.DIV.Pol K' ι n) := by
  simp only [Formalism.L2.Col.Br.brStdP, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul]
  rw [MvPolynomial.smul_eq_C_mul, map_mul, map_C, Formalism.L2.Ker.lb_map_projVV, Formalism.L2.Ker.lb_map_coefLast,
    Formalism.L2.Ker.lb_map_brConst, ← MvPolynomial.smul_eq_C_mul]

end BC

section Rec

variable {D : D7} {u : D.what₂.Word}

def brTenL (D : D7) (u : D.what₂.Word) (F : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL) :
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL :=
  (Formalism.L2.Col.Br.brStdP (Nm_succ D.R).symm (lamTr D u) (sgTr D u) F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (D.R.N D.R.m - 1))

theorem map_brTenL (j : D.what₂.LL →+* ℂ) (F : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL) :
    map j (brTenL D u F) = Formalism.L2.Ker.brTen D u (map j F) := by
  unfold brTenL Formalism.L2.Ker.brTen
  rw [map_brStdP, Formalism.L2.Ker.blk_brOne]

end Rec

end Formalism.L2.GlobalTheoryTheory.Br
