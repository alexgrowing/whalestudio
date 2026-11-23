import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.Vert.Model.GenIso

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : GlobalTheory.Vert.Model O}
  {E E' : Z.X.Modules} {r : ℕ}

theorem cls_div_of_isIso (hE : GlobalTheory.VB.IsVB E r) (hE' : GlobalTheory.VB.IsVB E' r) {φ : Z.GenIso E E'}
    {ψ : E' ⟶ E} [IsIso ψ] (hψ : φ.inv = Z.genRes.map ψ) : (φ.div hE hE').cls = 0 := by
  have := hE.isQuasicoherent
  have := hE'.isQuasicoherent
  refine (VertDiv.IsSum.cls_eq (P := VertDiv.zero Z) (P' := VertDiv.zero Z) fun i j k => ?_).trans
    (by simp)
  obtain ⟨c, c'⟩ := k
  have hV : (VertDiv.zero Z).M.U i ⊓ (VertDiv.zero Z).M.U j ⊓ (c.U ⊓ c'.U) ≤ c.U ⊓ c'.U :=
    inf_le_right
  refine ⟨c.isFrame.detUnit (c'.isFrame.map_iso ψ) (hV.trans inf_le_left) (hV.trans inf_le_right),
    (eqn_div_of_hom hE hE' hψ c c' le_rfl hV).trans ?_⟩
  change _ = _ * (resG _ _ 1 * resG _ _ 1)
  rw [map_one, map_one, mul_one, mul_one, GlobalTheory.VB.IsFrame.val_detUnit]
  congr 2
  funext l
  exact GlobalTheory.Twist.app_resM _ _ _

theorem cls_div_eq_of_iso : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Z : GlobalTheory.Vert.Model O) (L L' M M' : Z.X.Modules) (r : ℕ) (hL : GlobalTheory.VB.IsVB L r)
    (hL' : GlobalTheory.VB.IsVB L' r) (hM : GlobalTheory.VB.IsVB M r) (hM' : GlobalTheory.VB.IsVB M' r)
    (φ : Z.GenIso L L') (χ : Z.GenIso M M') (e : L ≅ M) (e' : L' ≅ M'),
    φ.hom ≫ Z.genRes.map e'.hom = Z.genRes.map e.hom ≫ χ.hom →
    (GlobalTheory.Vert.Model.GenIso.div φ hL hL').cls = (GlobalTheory.Vert.Model.GenIso.div χ hM hM').cls := by
  intro O _ _ _ Z L L' M M' r hL hL' hM hM' φ χ e e' hcomm
  have hχ : χ = (Z.genRes.mapIso e).symm ≪≫ φ ≪≫ Z.genRes.mapIso e' := by
    refine Iso.ext ?_
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, hcomm]
    rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  subst hχ
  rw [cls_div_trans _ hM hL hM', cls_div_trans _ hL hL' hM',
    cls_div_of_isIso hM hL (ψ := e.hom) rfl, cls_div_of_isIso hL' hM' (ψ := e'.inv) rfl,
    zero_add, add_zero]

end GlobalTheory.Vert.Model.GenIso
