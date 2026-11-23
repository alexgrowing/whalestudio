import Formalism.LocalToGlobal.ProjectiveLattices.RatRgOfSecRat
import Formalism.LocalToGlobal.ProjectiveLattices.GenSpecDesc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ExpBCChart
import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField

noncomputable section

namespace Formalism.L2.Pj

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Fr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem adjoin_weight {Z : Comp Xo c} {I : Type} {wL : WTZ E} {ws : I → AC Z} (hws : ∀ i, ws i ∈ AG Z wL)
    {p : AC Z} (hp : p ∈ Algebra.adjoin c.F (Set.range ws)) : ∀ G, p.coeff G ≠ 0 → ∃ m : ℕ, G = m • wL := by
  classical
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨r, hr⟩ := mem_AG.1 (hws i)
    intro G hG
    rw [hr, AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at hG
    split_ifs at hG with e
    · exact ⟨1, by rw [one_smul, e]⟩
    · exact absurd rfl hG
  | algebraMap r =>
    intro G hG
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply] at hG
    split_ifs at hG with e
    · exact ⟨0, by rw [zero_smul, e]⟩
    · exact absurd rfl hG
  | add x y _ _ hx hy =>
    intro G hG
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hG
    by_cases h1 : x.coeff G = 0
    · rw [h1, zero_add] at hG; exact hy G hG
    · exact hx G h1
  | mul x y _ _ hx hy =>
    intro G hG
    rw [AddMonoidAlgebra.coeff_mul] at hG
    unfold Finsupp.sum at hG
    obtain ⟨g1, hg1, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hG
    obtain ⟨g2, hg2, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    dsimp only at hne2
    split_ifs at hne2 with e
    · obtain ⟨m1, e1⟩ := hx g1 (Finsupp.mem_support_iff.1 hg1)
      obtain ⟨m2, e2⟩ := hy g2 (Finsupp.mem_support_iff.1 hg2)
      exact ⟨m1 + m2, by rw [← e, e1, e2, add_smul]⟩
    · exact absurd rfl hne2

end Fr

open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.T0

variable {D : D7} {T : Top D}

def SpreadRgSt {j : ℕ} (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (x : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r)
    (hx : x ∈ ((T.U j T.σ₀).X (κ Z)).dom),
    ∃ (A : TRing T.Q.c.F) (yA : FrPt (T.Q.Xo j) T.Q.c A.R) (io : A.R →ₐ[T.Q.c.F] Om Z)
      (ev : A.R →ₐ[T.Q.c.F] CAt T.σ₀) (w : FrPt (T.Q.Xo j) T.Q.c (CAt T.σ₀)) (t : Ix (T.Q.Dw j) → (CAt T.σ₀)ˣ)
      (wO : FrPt (T.Q.Xo j) T.Q.c (Om Z)) (tO : Ix (T.Q.Dw j) → (Om Z)ˣ),
      Function.Injective io ∧ FrMap ev yA w ∧ FrBor t w ((T.U j T.σ₀).un (κ Z) ⟨x, hx⟩) ∧
        FrMap io yA wO ∧ FrBor tO wO (genFr hG Z)

end Formalism.L2.Pj
