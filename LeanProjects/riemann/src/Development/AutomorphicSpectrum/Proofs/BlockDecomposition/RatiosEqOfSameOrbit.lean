import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {D : ℕ}

abbrev Over {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)
    (z : (Σ k, Bk n k) → ℂ) : Prop :=
  IsUnder (PtsOver.map i rfl _ y) z

abbrev LinProj (n : Fin (m + 1) → ℕ) (D : ℕ) := (((k : Fin (m + 1)) → Bk n k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)

def ratios (Ψ : LinProj n D) (z : (Σ k, Bk n k) → ℂ) : Fin D → ℂ :=
  fun a => Ψ (segre z) a.succ / Ψ (segre z) 0

open Classical in

def liftOf {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) : (Σ k, Bk n k) → ℂ :=
  if h : ∃ z, Over i y z then h.choose else 0

def projCoord {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    Fin D → ℂ :=
  ratios Ψ (liftOf i y)

def IsRegAt {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D)
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) : Prop :=
  LinearMap.det (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) :
    (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) ≠ 0

def IsPiece {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (N : Pol n)
    (e : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ))
    (Γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) : Prop :=
  (∃ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, e.source ⊆ c.e.source) ∧ DifferentiableOn ℂ Γ e.target ∧
    ∀ v ∈ e.target, Over i (e.symm v) (Γ v) ∧ Γ v ∈ mcPts (ptIdeal (i (genericPoint X))) ∧
      Ψ (segre (Γ v)) = Fin.cons 1 v ∧ eval (Γ v) (map (Int.castRingHom ℂ) N) ≠ 0

def pieceSet {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (N : Pol n) :
    Set (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :=
  {y | ∃ e Γ, IsPiece i Ψ N e Γ ∧ y ∈ e.source}

theorem isOpen_pieceSet {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (N : Pol n) :
    IsOpen (pieceSet i Ψ N) := isOpen_iff_forall_mem_open.mpr fun _ ⟨e, Γ, hp, hy⟩ =>
  ⟨e.source, fun _ hy' => ⟨e, Γ, hp, hy'⟩, e.open_source, hy⟩

theorem segre_orbit {z z' : (Σ k, Bk n k) → ℂ} {c : Fin (m + 1) → ℂ} (h : z = fun p => c p.1 * z' p) :
    segre z = (∏ k, c k) • segre z' := by
  subst h
  funext a
  simp [ReciprocityTheory.ChartRestriction.G.Geo.segre, Finset.prod_mul_distrib]

theorem ratios_eq_of_sameOrbit (Ψ : LinProj n D) {z z' : (Σ k, Bk n k) → ℂ} (h : SameOrbit z z')
    (h0 : Ψ (segre z') 0 ≠ 0) : ratios Ψ z = ratios Ψ z' := by
  obtain ⟨c, hc, rfl⟩ := h
  have hprod : (∏ k, c k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  funext a
  simp only [ratios, segre_orbit (c := c) rfl, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hprod

theorem ratios_of_proj (Ψ : LinProj n D) {z : (Σ k, Bk n k) → ℂ} {v : Fin D → ℂ}
    (h : Ψ (segre z) = Fin.cons 1 v) : ratios Ψ z = v := by
  funext a
  simp [ratios, h]

theorem homog_mul {f g : Pol n} {a b : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro d hd k
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hd)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf x hx k, hg y hy k, Pi.add_apply]

end GlobalTheory.CompanionTheory.MixZ.ArchEq
