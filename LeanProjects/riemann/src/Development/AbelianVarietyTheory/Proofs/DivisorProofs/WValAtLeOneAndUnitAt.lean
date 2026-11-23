import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicPointSpecializing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtPointsOverPrimeBound
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.WholeFlag GlobalTheory.ShFam.Pad

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.NormExt

theorem w_valAt_le_one_and_unitAt {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (e : TrueGeo.Ext v) {Z : Scheme.{0}} [IsIntegral Z] (yt : Sp e.O ⟶ Z) {f : Z.functionField}
    (hf : RegAt (yt (IsLocalRing.closedPoint e.O)) f) :
    e.w (valAt (spMap e.O.subtype ≫ yt) f) ≤ 1 ∧
      (e.w (valAt (spMap e.O.subtype ≫ yt) f) = 1 → UnitAt (yt (IsLocalRing.closedPoint e.O)) f) := by
  obtain ⟨W₀, hW₀, s, hs⟩ := hf.exists_fnOf
  have ht : ⊤ ≤ yt ⁻¹ᵁ W₀ := HtGen.IntPt.top_le_of_closedPoint yt hW₀
  have ht' : ⊤ ≤ (spMap e.O.subtype ≫ yt) ⁻¹ᵁ W₀ := fun q _ => ht (x := spMap e.O.subtype q) trivial
  have hb : below (spMap e.O.subtype ≫ yt) ∈ W₀ := ht' trivial
  have hev := OfModel.eval_pull e.O.subtype (𝟙 Z) (spMap e.O.subtype ≫ yt) yt (Category.comp_id _).symm
    (U := W₀) (W := W₀) le_rfl ht' ht s
  have hid : ((𝟙 Z : Z ⟶ Z).appLE W₀ W₀ le_rfl).hom s = s := by
    have : (𝟙 Z : Z ⟶ Z).appLE W₀ W₀ le_rfl = 𝟙 _ := (Category.id_comp _).trans (Z.presheaf.map_id _)
    rw [this]
    rfl
  rw [hid] at hev
  rw [← hs, OfModel.valAt_fnOf _ hb ht', hev]
  set c : e.O := (Scheme.Hom.appLE yt W₀ ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of e.O)).hom).hom s with hc
  change e.w (c : AlgebraicClosure F) ≤ 1 ∧ (e.w (c : AlgebraicClosure F) = 1 → _)
  refine ⟨(e.mem_O _).1 c.2, fun h1 => ?_⟩
  rw [HtGen.IntPt.w_eq_one_iff, hc, RegCrit.isUnit_eval_iff yt ht s] at h1
  exact (unitAt_fnOf_iff hW₀ (gen_mem hW₀) s).2 h1

end GlobalTheory.NormExt
