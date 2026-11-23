import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeStepHoldsPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_step_holds_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (Z₁ : Mdl Y i₀) (g₀ : Z₁.X ⟶ Z.X), IsMap Z₁ Z g₀ → t.Holds Z₁ → ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Field K] [Algebra R K] (z : Sp R ⟶ Z₁.X) (α : D.C.A), ⊤ ≤ (z ≫ g₀) ⁻¹ᵁ D.C.B α → ∃ (n' : ℕ) (a : Matrix (Fin n') (Fin (D.C.n α)) R) (a' : Matrix (Fin (D.C.n α)) (Fin n') R), a * a' = 1 ∧ a' * a = 1 ∧ ∀ (τ : (Y Z₁.i).X ⟶ (Y Z.i).X) (mu : SABMap (Y Z₁.i).t (Y Z.i).t τ) (u : Vecs Dw (Y Z₁.i).t K), LocM.IsTrans Z.i Z₁.i τ mu → Z₁.FlagAt (spMap (algebraMap R K) ≫ z) u → ∀ (y : Sp K ⟶ Z.X), y = spMap (algebraMap R K) ≫ z ≫ g₀ → ∀ (hy : ⊤ ≤ y ⁻¹ᵁ D.C.B α) (v : TanM (y ≫ Z.π) (Y Z.i).t.G) (i : Fin (Dw.mult t.σ)), (i : ℕ) < t.k → (tv v).left = u t.σ i ≫ mu.φ → ∀ j : Fin n', t.k ≤ (j : ℕ) → ∑ l, algebraMap R K (a j l) * D.crd α K y hy v l = 0 := by
  first | exact @GlobalTheory.GrCl.Annih.annih | exact GlobalTheory.GrCl.Annih.annih | (intros; apply GlobalTheory.GrCl.Annih.annih <;> assumption)
