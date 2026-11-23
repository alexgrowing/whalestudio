import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundOfFlag
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coord_degree_bound_of_flag : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X),
      CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier)
      (F : SatFlag B r), (∀ j : Fin (r + 1), IsSubFibre M (flagStep Ω b₀ j.val) z MB (F.F j)) →
      ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∃ (f : Fin i → B.carrier) (ef : Fin i → Li) (s : B.carrier) (e : Li) (t : Ω) (u : L)
        (vf : Fin i → (epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G)) (ve : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
        (∀ j, f j ∈ F.F i.castSucc) ∧ LinearIndependent (𝓞 L) f ∧ s ∈ F.F i.succ ∧ s ∉ F.F i.castSucc ∧
        (∀ j, ef j ∈ flagStep Ω b₀ i) ∧ e ∈ flagStep Ω b₀ (i + 1) ∧
        (∀ j, M.ValAt _ (ef j) (vf j) ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) (f j) (vf j)) ∧
        M.ValAt _ e ve ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) s ve ∧
        IsCls b₀ i e t ∧ ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (t / gen y a e₀ c₀) u ∧ u ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.Pick.pick | exact GlobalTheory.CompanionTheory.Ar.RootHt.Pick.pick | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.Pick.pick <;> assumption)
