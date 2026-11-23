import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option autoImplicit false
open CartesianMonoidalCategory MonObj
noncomputable section

namespace GlobalTheory.TorsSpec

theorem etaSecL_smul_geom {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V₀ TF.Y Z) (a : LevelMod Dw l)
    (r : 𝓞 E) (A B : Over.mk (x ≫ ℓ) ⟶ GlobalTheory.EqvAct.pullG TF Z φ) (hA : A.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ a)
    (hB : B.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ (r • a)) : B = A ≫ (GlobalTheory.EqvAct.pullAct TF Z φ).act r := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  have key : x ≫ i₀ TF.Y Z ≫ (TF.Y.oF.eta (r • b)).left =
      x ≫ i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ (TF.Y.oF.t.act.act r).left := by
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) from
      l.coprime ▸ Submodule.mem_top)
    have ev : ∀ d : Dw.La, TF.Y.oF.eta d = TF.Y.oF.eta (v • d) := fun d => by
      conv_lhs => rw [← one_smul (𝓞 E) d, ← huv, add_smul, TF.Y.oF.eta_add,
        TF.Y.oF.eta_ker _ (Submodule.smul_mem_smul hu Submodule.mem_top), _root_.one_mul]
    obtain ⟨-, I, -, -, hη⟩ := TF.Y.oF.geom Ω (x ≫ i₀ TF.Y Z)
      (Spec.preimage ((x ≫ i₀ TF.Y Z) ≫ (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s))).hom
      (Spec.map_preimage _).symm
    have e : toUnit (Over.mk (x ≫ i₀ TF.Y Z)) ≫ TF.Y.oF.eta (r • b) =
        (toUnit (Over.mk (x ≫ i₀ TF.Y Z)) ≫ TF.Y.oF.eta b) ≫ TF.Y.oF.t.act.act r := by
      rw [ev (r • b), ev b, hη _ (Submodule.smul_mem_smul hv Submodule.mem_top),
        hη _ (Submodule.smul_mem_smul hv Submodule.mem_top), smul_comm v r b, I.lin]
    have ht : (toUnit (Over.mk (x ≫ i₀ TF.Y Z))).left = x ≫ i₀ TF.Y Z := by
      simpa using Over.w (toUnit (Over.mk (x ≫ i₀ TF.Y Z)))
    have e' := congrArg (fun q => q.left) e
    simp only [Over.comp_left, ht] at e'
    simpa only [Category.assoc] using e'
  apply Over.OverMorphism.ext
  rw [hB, Over.comp_left, hA, ← Submodule.Quotient.mk_smul]
  apply pullback.hom_ext
  · have h1 := etaSecL_ψ TF Z φ ℓ hℓ b
    have h2 := etaSecL_ψ TF Z φ ℓ hℓ (r • b)
    simp only [Category.assoc]
    rw [GlobalTheory.EqvAct.pullAct_pullψ, reassoc_of% h1, h2, ← TF.Y.m.act r, reassoc_of% key]
  · have w1 := etaSecL_w TF Z φ ℓ hℓ (Submodule.Quotient.mk b)
    have w2 := etaSecL_w TF Z φ ℓ hℓ (Submodule.Quotient.mk (r • b))
    have w3 := Over.w ((GlobalTheory.EqvAct.pullAct TF Z φ).act r)
    simp only [Category.assoc]
    erw [w2, w3, w1]

end GlobalTheory.TorsSpec
