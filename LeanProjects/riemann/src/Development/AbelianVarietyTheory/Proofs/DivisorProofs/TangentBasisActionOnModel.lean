import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ArLieBase.exists_eig_subspace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (R : Type) [CommRing R] (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)), GlobalTheory.LineNorm.IsTanBasis Z.t x e → ∀ (K : Type) [Field K] (ψ : R →+* K) (φ : c.F →+* K), spMap ψ ≫ x ≫ Z.s = spMap (φ.comp (algebraMap (𝓞 c.F) c.F)) → ∃ V : Submodule K (Fin g → K), Module.finrank K V = Dw.mult τ ∧ ∀ (cf : Fin g → K) (w : Sp (DualNumber K) ⟶ Z.t.G.left), IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w → (IsEigTan Z φ (spMap ψ ≫ x) τ w ↔ cf ∈ V) := by
  intro E _ _ _ H Dw l Xo c Z R _ x τ g e he K _ ψ φ hφ
  have h0 : (spMap ψ ≫ x) ≫ Z.s = spMap φ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Category.assoc, hφ, Guard.sp_comp]
  let y : Sp K ⟶ gen Z := Limits.pullback.lift (spMap ψ ≫ x) (spMap φ) h0
  have hy1 : y ≫ genι Z = spMap ψ ≫ x := Limits.pullback.lift_fst _ _ _
  have hy2 : y ≫ genStr Z = spMap φ := Limits.pullback.lift_snd _ _ _
  have hf := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c _ _ Z K φ y hy2
  rw [hy1] at hf
  obtain ⟨f⟩ := hf
  have hv : ∀ i, IsTanAtG Z.t (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ e i) :=
    fun i => GlobalTheory.FactorDepth.isTanAtG_map Z.t ψ (he.1 i)
  have hb := he.2 K ψ
  choose a ha using fun i => (hb _ (f.tan τ i)).exists
  let A : Matrix (Fin g) (Fin (Dw.mult τ)) K := fun j i => a i j
  have heig : ∀ cf w, IsCombAtG Z.t (spMap ψ ≫ x) (f.v τ) cf w → ∀ b : 𝓞 E,
      w ≫ (Z.t.act.act b).left = spMap (epsMul (φ (embK c τ b))) ≫ w := fun cf w h1 b => by
    rw [← (isCombAtG_iff Z.t _ (fun j => ovT (f.tan τ j)) _ _).1 h1]
    have := Z.t.act.hom b
    exact congrArg (fun f => f.left) (combT_eig _ (fun j => ovT (f.tan τ j)) (Z.t.act.act b) _
      (fun j => Over.OverMorphism.ext (f.eig τ j b)) cf)
  have hi : Guard.Indep Z.t (spMap ψ ≫ x) (f.v τ) := fun cf cf' w h1 h2 =>
    (f.basis τ w (Guard.comb_tan (f.tan τ) h1) (heig cf w h1)).unique h1 h2
  have hinj := (Guard.indep_iff hv (Guard.indep_of_basis hv hb) A ha).1 hi
  refine ⟨LinearMap.range A.mulVecLin, ?_, fun cf w hw => ⟨fun h => ?_, ?_⟩⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  · obtain ⟨b, hb', -⟩ := f.basis τ w h.1 h.2
    exact ⟨b, (hb w h.1).unique (tanLinG _ hv (f.v τ) A b w ha hb') hw⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨w', h1, h2⟩ := Guard.exists_comb (f.tan τ) b
    obtain rfl : w' = w := Guard.comb_unique hv (tanLinG _ hv (f.v τ) A b w' ha h2) hw
    exact ⟨h1, heig b w' h2⟩
