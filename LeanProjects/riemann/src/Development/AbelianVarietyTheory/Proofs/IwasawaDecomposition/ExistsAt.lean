import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDataNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDeRhamFlagStatement

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.LocM

theorem exists_at (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (hp : p.Prime)
    (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) : ∃ ct : At S κ p, ct.W = W := by
  have h1 : 1 ≤ S.Dw.p + S.Dw.q := by
    have h₁ := S.rank_eq
    have h₂ := S.two_le
    omega
  obtain ⟨B⟩ := GlobalTheory.T.local_system_bases_nonempty _ A.H S.Dw S.Xo p W hp hW (S.sys.Y p W hp hW) ⟨κ.l, κ.c, κ.good p hp⟩ h1
  have hYY : ∃ Z', IsDRFlag (B.X none) Z' := by
    have h := GlobalTheory.T.exists_de_rham_flag _ A.H S.Dw S.Xo p W hp hW (S.sys.Y p W hp hW) ⟨κ.l, κ.c, κ.good p hp⟩
    have hty : ∀ σ, (B.X none).ty σ = ∅ := B.ty none
    have hiso : IsIso (B.X none).π := B.iso none
    first
      | exact h (B.X none)
      | exact h (B.X none) hty
      | exact h (B.X none) hiso hty
      | exact h (B.X none) hty hiso
      | exact h (B.X none) (fun σ => by rw [hty σ]; exact Finset.empty_subset _)
      | exact h (B.X none) (fun σ k hk => by rw [hty σ] at hk; exact absurd hk (Finset.notMem_empty k))
      | exact h B
  obtain ⟨YY, hYY⟩ := hYY
  have hcl := (S.sys.clauses p W hp hW).2
  exact ⟨⟨hp, W, hW, B, YY, hYY, fun Z y =>
    GlobalTheory.T.point_data_nonempty _ A.H S.Dw S.Xo p W hp hW (S.sys.Y p W hp hW) ⟨κ.l, κ.c, κ.good p hp⟩
      (fun i => ⟨(hcl i).1, (hcl i).2.1⟩) Z.i y.C y.P⟩, rfl⟩

end GlobalTheory.LocM
