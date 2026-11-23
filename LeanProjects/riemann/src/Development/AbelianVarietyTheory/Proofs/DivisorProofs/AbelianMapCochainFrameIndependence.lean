import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainFrameLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianMapKillsCochainFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianMapKernelSpannedStatement
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BdFib

theorem ker_eq_span_cochFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [CharZero k] (x : Sp k ⟶ X) (φ : Fib k) (m : CubeMap φ.G t.G), FibAt t x φ m → ∀ (n : ℕ) (v : Fin n → (epsR k ⟶ φ.P.A)), IsLieBasis v → ∀ q : TanM x t.G →ₗ[k] (Fin n → k), IsAbMap φ m v q → ∀ (r : ℕ) (ε : Fin r → TanM x t.G), IsCochFrame t x ε → Module.finrank ℤ φ.X = r → LinearIndependent k ε ∧ LinearMap.ker q = Submodule.span k (Set.range ε) := by
  intro E _ _ _ H X t k _ _ x φ m hφ n v hv q hq r ε hε hr
  have hli : LinearIndependent k ε := GlobalTheory.T.cochain_frame_linear_independent E H X t k x r ε hε
  refine ⟨hli, ?_⟩
  obtain ⟨s, hs⟩ := GlobalTheory.T.abelian_map_kernel_spanned E H X t k x φ m hφ n v hv q hq
  have h1 : Submodule.span k (Set.range ε) ≤ LinearMap.ker q :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact GlobalTheory.T.abelian_map_kills_cochain_frame E H X t k x φ m hφ n v hv q hq r ε hε i)
  haveI : FiniteDimensional k (Submodule.span k (Set.range s)) :=
    FiniteDimensional.span_of_finite k (Set.finite_range s)
  have h2 : Submodule.span k (Set.range ε) = Submodule.span k (Set.range s) := by
    apply Submodule.eq_of_le_of_finrank_le (h1.trans hs)
    rw [finrank_span_eq_card hli, Fintype.card_fin, ← hr]
    exact (finrank_range_le_card (R := k) s).trans_eq (Fintype.card_fin _)
  exact le_antisymm (hs.trans h2.ge) h1

end GlobalTheory.BdFib
