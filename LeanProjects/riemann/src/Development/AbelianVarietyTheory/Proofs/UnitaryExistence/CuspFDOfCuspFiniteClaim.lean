import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.CuspMultiplicationClosed

noncomputable section

namespace GlobalTheory.CuspFormsCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma zero_mem_SS_unitary_existence {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) :
    (0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) ∈ X.SS la :=
  ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_zero X la, fun ξ _ x _ => _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_zero X la ξ x 0⟩

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma add_mem_SS {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) (hQ : Q ∈ X.SS la) : P + Q ∈ X.SS la := by
  refine ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_add X hP.1 hQ.1, fun ξ hξ x hx => ?_⟩
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_add X hP.1 hQ.1 hξ hx 0, hP.2 ξ hξ x hx, hQ.2 ξ hξ x hx, add_zero]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma smul_mem_SS {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    (a : ℂ) {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) : a • P ∈ X.SS la := by
  refine ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_smul X a hP.1, fun ξ hξ x hx => ?_⟩
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_smul X la P ξ x 0 a, hP.2 ξ hξ x hx, mul_zero]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.CuspFormsCompare.mem_holSub_iff_forall_SS {r : ℕ} {Comp : Type}
    (X : Comp → _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : ∀ k, _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r)
    (P : _root_.Formalism.L2.PjFree.FDSec X) : P ∈ _root_.Formalism.L2.PjFree.holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  constructor
  · intro hP
    unfold _root_.Formalism.L2.PjFree.holSub at hP
    induction hP using Submodule.span_induction with
    | mem Q hQ => exact hQ
    | zero => exact fun k => zero_mem_SS_unitary_existence (X k) (la k)
    | add Q R _ _ hQ hR => exact fun k => add_mem_SS (X k) (la k) (hQ k) (hR k)
    | smul a Q _ hQ => exact fun k => smul_mem_SS (X k) (la k) a (hQ k)
  · intro hP
    exact _root_.Formalism.L2.PjFree.holCusp_mem_holSub X la hP

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

end GlobalTheory.CuspFormsCompare
