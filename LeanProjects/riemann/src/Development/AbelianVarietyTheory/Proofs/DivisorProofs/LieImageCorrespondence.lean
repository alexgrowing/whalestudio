import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.RealMult.Obj

theorem lieCorr_of_isLieImage (P : GlobalTheory.Published.AbelianDeRham) {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (hX : X'.IsPullBy X (spMap σ) φ)
    (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) φ) {x : HdR X.A} {x' : HdR X'.A}
    (hx : m.Corr x x') {v : X.Lie} {v' : X'.Lie} (hv : IsLieImage x v.hom) (hv' : IsLieImage x' v'.hom) :
    Obj.LieCorr σ φ v v' := by
  letI : Algebra R R' := σ.toAlgebra
  obtain ⟨-, PH, PB, -, -⟩ := P
  have hφ : IsGrpPullback X'.A X.A (spMap (algebraMap R R')) φ := hX.grp
  obtain ⟨-, hF⟩ := PB R X.A _ X.ab X.dim R' X'.A φ hφ
  have hL := (PH R' X'.A _ X'.ab X'.dim).1
  have hc : (Chart.dualMapR σ).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp σ := by
    ext r <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have w : (spMap (Chart.dualMapR σ) ≫ v.hom.left) ≫ X.A.hom = (epsR R').hom ≫ spMap σ := by
    rw [Category.assoc, Over.w v.hom]
    change spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [← Cris.spMap_comp, ← Cris.spMap_comp, hc]
  let u : epsR R' ⟶ X'.A := Over.homMk (hφ.1.lift _ _ w) (hφ.1.lift_snd _ _ w)
  have hu : u.left ≫ φ = spMap (Chart.dualMapR σ) ≫ v.hom.left := hφ.1.lift_fst _ _ w
  have e : (GlobalTheory.Published.AbelianDeRham.bcMor hφ).Corr x x' := hx
  have hiu : IsLieImage x' u := IsLieImage.baseChange (hφ := hφ) hF hL e hu hv
  have : u = v'.hom := (hL.1 x').unique hiu hv'
  unfold Obj.LieCorr
  rw [← this]
  exact hu

end GlobalTheory.RealMult.Obj
