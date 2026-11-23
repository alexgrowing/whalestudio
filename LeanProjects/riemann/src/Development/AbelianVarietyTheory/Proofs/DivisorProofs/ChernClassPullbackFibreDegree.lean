import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkUniqueCharacterizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelTrivializingBlowupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeFinitePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDegreeMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairPullbackCompositeStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PresPullCk

open GlobalTheory.Vert.Model

theorem picSymPull_comp {X Y W : Scheme.{0}} (g : W ⟶ Y) (f : Y ⟶ X) (y : PicSym X) :
    picSymPull (g ≫ f) y = picSymPull g (picSymPull f y) := by
  have : (picSymPull (g ≫ f)).toLinearMap = (picSymPull g).toLinearMap ∘ₗ (picSymPull f).toLinearMap :=
    picSym_linearMap_ext fun n c => by
      simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply, map_prod, picSymPull_c1Pic, pull_comp]
  exact LinearMap.congr_fun this y

theorem ck_pull : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
    [CharZero O] [CharP (ResidueField O) p] (B B' : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X →
    GlobalTheory.IsNormalScheme B'.X → ∀ (f : GlobalTheory.Vert.Model.Hom B' B), f.relDim = 0 → ∀ (P : Pres B) (k : ℕ)
    (Q : PicSym B.X), (P.pull f).ck p k (picSymPull f.f Q) = f.fibreDeg 1 * P.ck p k Q := by
  intro O _ _ _ p _ _ _ B B' hB hB' f hf P k Q
  haveI := P.iso
  simp only [Pres.ck]
  rw [Pres.ofHom_pull]

  set φ := GenIso.ofHom P.ψ with hφ
  have hE := P.vb.pullback f.f
  have hE' := P.vb'.pullback f.f

  obtain ⟨B₂, π, hB₂, hπ, hP⟩ := GlobalTheory.T.normal_model_trivializing_blowup O p B' hB' 1 (fun _ => P.r)
    (fun _ => (Scheme.Modules.pullback f.f).obj P.E) (fun _ => (Scheme.Modules.pullback f.f).obj P.E')
    (fun _ => φ.pull f.comp_str) (fun _ => ⟨hE, hE'⟩)
  obtain ⟨Pr⟩ := hP 0

  obtain ⟨P₂, h₂⟩ := GlobalTheory.T.flag_pair_pullback_composite O p B B' B₂ f.f f.comp_str π.f π.comp_str (π.comp f).f (π.comp f).comp_str rfl
    P.E P.E' φ P.r Pr
  have hrel : (π.comp f).relDim = 0 := by
    have a := f.relDim_add
    have b := π.relDim_add
    have c := (π.comp f).relDim_add
    omega
  let M : FlagModel (φ.pull f.comp_str) P.r := ⟨B₂, π, Pr⟩
  let M' : FlagModel φ P.r := ⟨B₂, π.comp f, P₂⟩
  have e₁ := (GlobalTheory.T.ck_unique_characterization O p B' hB' _ _ (φ.pull f.comp_str) P.r k hE hE').1 M hB₂ hπ (picSymPull f.f Q)
  have e₂ := (GlobalTheory.T.ck_unique_characterization O p B hB _ _ φ P.r k P.vb P.vb').1 M' hB₂ hrel Q
  have hck : ∀ y, ck (M'.toFPair p) k y = ck (M.toFPair p) k y := fun y => by
    change ck (P₂.toFPair p) k y = ck (Pr.toFPair p) k y
    simp only [ck, fun i => (h₂ i).1, fun i => (h₂ i).2.1, fun i => (h₂ i).2.2]
  have hpull : picSymPull (π.comp f).f Q = picSymPull π.f (picSymPull f.f Q) := by
    change picSymPull (π.f ≫ f.f) Q = _
    exact picSymPull_comp π.f f.f Q
  have hdeg := GlobalTheory.T.fibre_degree_multiplicative O B B' B₂ π f hπ hf
  have hpos := (GlobalTheory.T.cap_degree_finite_pullback O p B' hB' B₂ π hπ).1
  rw [hck, hpull, e₁, hdeg] at e₂
  have e₃ := e₂
  rw [mul_assoc] at e₃
  exact mul_left_cancel₀ hpos.ne' e₃

end GlobalTheory.PresPullCk

end
