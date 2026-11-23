import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAmpleCoverLevels
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_ample_cover_levels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ Xo : ∀ l : Level H, Moduli D l, ∃ (s : Sys Xo) (M : Finset ℕ), (∀ m ∈ M, 1 ≤ m) ∧
      ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p),
        ∃ (I : Type) (_ : Finite I) (R : I → Type) (_ : ∀ i, CommRing (R i)) (a : I → 𝓞 c.F) (b : ∀ i, 𝓞 c.F →+* R i)
          (ω : ∀ i, R i →+* c.F) (C : ∀ i, Model (Xo l) c (ω i)),
          IsCover (algebraMap (𝓞 c.F) c.F) R a b ω ∧ (∀ i, ∃ m ∈ M, AmpAt (C i) m) ∧
          ∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b₀ : 𝓞 c.F →+* c.V W),
            (∀ x, ((b₀ x : c.V W) : c.F) = (x : c.F)) →
            ∃ (i : I) (b' : R i →+* c.V W), b'.comp (b i) = b₀ ∧ (c.V W).subtype.comp b' = ω i ∧
              Dominates (C i) (s.Y p W hp hW ⟨l, c, hg p hp⟩) b' := by
  first | exact @GlobalTheory.CoverFin.coverSt_fin | exact GlobalTheory.CoverFin.coverSt_fin | (intros; apply GlobalTheory.CoverFin.coverSt_fin <;> assumption)
