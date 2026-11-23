import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleNsmul
open NumberField CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O.Cover

theorem isAmpleLB_pull_of_induces : ∀ {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} (V : Cover Y)
    (A : Adl C Y) (L : HermLB V.p) (k : ℕ), 0 < k → V.Induces A L k → Y.ample A.D → IsAmpleLB (L.B.pull V.j) := by
  intro F _ _ C Y V A L k hk hI hA
  obtain ⟨r, hr, hu, -⟩ := hI
  have hL : (L.B.pull V.j).IsLB := LB.isLB_pull L.isLB V.j
  have hφ : V.φ = GlobalTheory.functionFieldMap V.π := by
    obtain ⟨hη, e⟩ := V.φ_eq_fnMap
    exact e
  have hP : GlobalTheory.Cartier.Presents (GlobalTheory.Cartier.DomPull.pullback V.π (k • A.D)) (L.B.pull V.j) r := by
    refine ⟨hL, hr, fun i x hx => ?_⟩
    have h₁ := GlobalTheory.Cartier.DomPull.isEqn_pullback V.π (k • A.D) ((Base.isEqn_eqn A.D (V.π x)).nsmul k)
    refine h₁.iff_unitAt.2 ?_
    have h₂ := hu i x hx
    rw [hφ] at h₂
    convert h₂ using 1
    simp only [genAt, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val, map_pow, map_inv₀, inv_pow, div_eq_inv_mul]
  have hk' : IsAmpleLB (GlobalTheory.Cartier.toLB (k • A.D)) := Var.ample_nsmul F Y A.D k hk hA
  exact (hk'.pull_of_isFinite V.π).of_lbIso hL (hP.lbIso (GlobalTheory.Cartier.DomPull.presents_pullback V.π _))

end GlobalTheory.Mean4O.Cover
