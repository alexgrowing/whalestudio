import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkUniqueCharacterizationStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixedLocalChains

section IsoZero

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem cls_div_refl_of_isVB {Z : Vert.Model O} {E : Z.X.Modules} {r : ℕ} (hE : GlobalTheory.VB.IsVB E r) :
    (Vert.Model.GenIso.div (Iso.refl _ : Z.GenIso E E) hE hE).cls = 0 := by
  have := Vert.Model.GenIso.cls_div_trans (Iso.refl _ : Z.GenIso E E) hE hE hE (Iso.refl _)
  rw [Iso.trans_refl] at this
  simpa using this

def flagPairOfIso {Z : Vert.Model O} {E E' : Z.X.Modules} {N : ℕ} (φ : Z.GenIso E E') (e : E' ≅ E)
    (he : φ.inv = Z.genRes.map e.hom) (fl' : Flag E' N) : Vert.Model.FlagPair φ N where
  fl := fl'.ofIso e
  fl' := fl'
  gen _ := Iso.refl _
  gen_ι i := by
    change 𝟙 _ ≫ _ = Z.genRes.map (fl'.ι i ≫ e.hom) ≫ φ.hom
    rw [Functor.map_comp, Category.assoc, ← he, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

theorem cls_div_flagPairOfIso {Z : Vert.Model O} {E E' : Z.X.Modules} {N : ℕ} (φ : Z.GenIso E E')
    (e : E' ≅ E) (he : φ.inv = Z.genRes.map e.hom) (fl' : Flag E' N) (i : Fin N) :
    ((flagPairOfIso φ e he fl').div i).cls = 0 := by
  have h : (flagPairOfIso φ e he fl').grIso i = Iso.refl _ := by
    ext1
    have h1 := (flagPairOfIso φ e he fl').π_grIso_hom i
    rw [← cancel_epi (Z.genRes.map ((flagPairOfIso φ e he fl').fl.π i)), h1]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  unfold Vert.Model.FlagPair.div
  rw [h]
  exact cls_div_refl_of_isVB _

end IsoZero

theorem Pres.ck_eq_zero_of_isIso : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (P : Pres B), IsIso P.ψ → ∀ k : ℕ, P.ck p k = 0 := by
  intro O _ _ _ p _ _ _ B hB P hψ k
  haveI := P.iso
  have hT := GlobalTheory.T.ck_unique_characterization O p B hB P.E P.E' (Vert.Model.GenIso.ofHom P.ψ) P.r k P.vb P.vb'
  refine (hT.2.1 0 ?_).symm
  intro M hM _ Q
  have hT' := GlobalTheory.T.ck_unique_characterization O p M.B hM _ _ ((Vert.Model.GenIso.ofHom P.ψ).pull M.π.comp_str) P.r k
    (P.vb.pullback _) (P.vb'.pullback _)
  let e := (Scheme.Modules.pullback M.π.f).mapIso (asIso P.ψ)
  have he : ((Vert.Model.GenIso.ofHom P.ψ).pull M.π.comp_str).inv = M.B.genRes.map e.hom :=
    Vert.Model.GenIso.pull_inv _ rfl
  rw [LinearMap.zero_apply, mul_zero]
  rw [show M.toFPair p = M.pair.toFPair p from rfl]
  rw [← hT'.2.2 M.pair, hT'.2.2 (flagPairOfIso _ e he M.pair.fl')]
  refine Finset.sum_eq_zero fun i _ => ?_
  change (M.B.toITh p).capDeg (Vert.Model.toQ ((flagPairOfIso _ e he M.pair.fl').div i).cls) _ = 0
  rw [cls_div_flagPairOfIso, map_zero]
  first | rfl | exact LinearMap.zero_apply (M := (M.B.toITh p).Ch) _ | simp

end GlobalTheory.MixedLocalChains
