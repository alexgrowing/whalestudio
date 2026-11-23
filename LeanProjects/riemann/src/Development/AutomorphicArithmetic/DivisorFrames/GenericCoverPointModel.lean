import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocallyStatement
import Development.AutomorphicArithmetic.DivisorFrames.TestPointLiftsToCover
import Development.AutomorphicArithmetic.DivisorFrames.IntegralPAdicPointLabels
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.RootFrame

theorem UpperTheory.generic_cover_point_model :
    GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) [IsLocallyNoetherian Z.X], Z.X.IsSeparated → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ Z.X) (π : Y.X ⟶ gen Z), V.j ≫ ρ' = V.π ≫ π ≫ genι Z → ∀ (W : Y.X.Opens), (∀ y ∈ W, π y ∈ Set.range Z.jQ) → ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 2 ≤ n → LabFam Z ρ' p n → ∃ K : Charts Dw Z.t V ρ' V.X, (∀ x, x ∈ K.U x) ∧ K.HTAt (π ≫ genι Z) W p n := by
  intro hHT E _ _ _ H Dw l Xo c Z _ hsep F _ _ Y V ρ' π hρ W hW p _ n hn hL
  obtain ⟨ch, hch, hh⟩ := hL
  have hc : ∀ x : V.X, ∃ (U : V.X.Opens) (hU : IsAffineOpen U) (g : ℕ)
      (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ Z.t.G.left)) (h : Dw.La → Fin g → Γ(V.X, U)),
      x ∈ U ∧ IsTanBasis Z.t (R := Γ(V.X, U)) (hU.fromSpec ≫ ρ') e ∧
      ∀ (φ : Γ(V.X, U) →+* ↥(intO ℂ_[p])) (x : Sp ↥(intO ℂ_[p]) ⟶ V.X), spMap φ ≫ hU.fromSpec = x →
        ∀ a, DlogIs Z.t p n (ch a x) (fun i => spMap (dualMap φ) ≫ e i) (fun i => φ (h a i)) := by
    intro x
    obtain ⟨⟨U, hU⟩, g, e, hx, he⟩ := GlobalTheory.T.exists_affine_tangent_basis_locally E H Z.X Z.t V.X ρ' x
    obtain ⟨h, hh'⟩ := hh U hU g e he
    exact ⟨U, hU, g, e, h, hx, he, hh'⟩
  choose U hU g e h hx he hd using hc
  refine ⟨⟨U, hU, g, e, he, h⟩, hx, ?_⟩
  intro v ε y z yt hT
  obtain ⟨x, hx1, hx2, hx3⟩ := UpperTheory.test_point_lifts_to_cover E H Z.X Z.t F Y V ρ' (π ≫ genι Z) hρ W p v ε y z yt hT
  have := Z.jQ_open
  have hr : Set.range (spMap (ioOf p ε) ≫ y.1 ≫ π) ⊆ Set.range Z.jQ := by
    rintro _ ⟨q, rfl⟩
    have h1 := hW _ hT.2.1
    have h2 : (spMap (ioOf p ε)) q = IsLocalRing.closedPoint (AlgebraicClosure F) :=
      Subsingleton.elim (α := PrimeSpectrum (AlgebraicClosure F)) _ _
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h2]
    exact h1
  obtain ⟨y', hy'⟩ : ∃ y', y' ≫ Z.jQ = spMap (ioOf p ε) ≫ y.1 ≫ π := ⟨_, IsOpenImmersion.lift_fac Z.jQ _ hr⟩
  have hj : spMap (intO ℂ_[p]).subtype ≫ x ≫ ρ' = y' ≫ Z.j := by
    have : Z.j = Z.jQ ≫ genι Z := rfl
    rw [hx2, this, ← Category.assoc y', hy']
    simp only [Category.assoc]
  have hA : AlgDef (spMap (intO ℂ_[p]).subtype ≫ x ≫ ρ') := by
    refine ⟨AlgebraicClosure F, inferInstance, ioOf p ε, _, fun a => ?_, hx2⟩
    have h1 : Algebra.IsAlgebraic ℚ (AlgebraicClosure F) := Algebra.IsAlgebraic.trans ℚ F _
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ _).2 (h1.isAlgebraic a)
  refine ⟨x ≫ ρ', fun o => ch o x, hx1, fun a ha => ?_⟩
  obtain ⟨φ, hφ, hP⟩ := hx3 (U a) (hU a) ha
  have hb : IsTanBasis Z.t (x ≫ ρ') (fun i => spMap (dualMap φ) ≫ e a i) := by
    have := GlobalTheory.FlatModel.isTanBasis_bc (he a) φ
    rwa [← Category.assoc, hφ] at this
  obtain ⟨b, hb1, hb2⟩ := UpperTheory.integral_p_adic_point_labels hHT E H Dw l Xo c Z hsep p n (x ≫ ρ') y' hn hj hA (fun o => ch o x)
    (hch x y' hj) (g a) _ (fun o i => φ (h a o i)) hb (hd a φ x hφ)
  exact ⟨_, fun o i => φ (h a o i), b, hb, hd a φ x hφ, hb1, hb2, fun M m o f T P hC => hP _ _ M m _ f T P hC⟩
