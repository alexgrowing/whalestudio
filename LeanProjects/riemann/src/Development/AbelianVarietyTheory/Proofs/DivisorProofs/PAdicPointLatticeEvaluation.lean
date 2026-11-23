import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.ModelPointWeil

theorem weil_eq_of_weilIs_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ → ∀ (a : Dw.La) (tt : P.T),
    (tt.lev n).left ≫ ψ = yy ≫ (Y.oF.etaA a).left → ∀ (z : GlobalTheory.ChTor.Pts P.A.A) (e σ : Over.mk yy ⟶ Y.oF.t.G),
    e.left = yy ≫ (Y.oF.etaA a).left → σ.left = z.left ≫ ψ → σ ^ (p ^ n) = 1 → ∀ c : ℂ_[p]ˣ,
    Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ (unitOn c) → (c : ℂ_[p]) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ yb yy P π ψ hP a tt hlev z e σ he hσ hσp c hW
  obtain ⟨-, -, -, hpb, -, hL⟩ := hP
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨r, hr, ⟨cu⟩⟩ := GlobalTheory.PolAV_exists_cubical hLaws.cube P.A
  obtain ⟨w, hw⟩ := hL
  have hx : Tate.lev tt n ^ p ^ n = 1 := Tate.lev_pow tt n
  let T : Over (Sp ℂ_[p]) := Over.mk (𝟙 (Sp ℂ_[p]))
  have inj : ∀ {x y : T ⟶ P.A.A}, x.left ≫ ψ = y.left ≫ ψ → x = y := fun {x y} h =>
    Over.OverMorphism.ext (hpb.1.hom_ext h (by rw [Over.w, Over.w]))
  let U : Over.mk yy ⟶ Over.mk (T.hom ≫ yy) := Over.homMk (𝟙 _) (by simp [T])
  have hUz : U ≫ pushHom hpb T z = σ := Over.OverMorphism.ext (by
    show 𝟙 _ ≫ (z.left ≫ ψ) = σ.left
    rw [Category.id_comp, hσ])
  have hz : z ^ p ^ n = 1 := by
    apply inj
    have h1 : U ≫ pushHom hpb T (z ^ p ^ n) = U ≫ pushHom hpb T 1 := by
      rw [map_pow, map_one, MonObj.comp_pow, MonObj.comp_one, hUz, hσp]
    have h2 := congrArg (fun q => q.left) h1
    simpa using (show 𝟙 _ ≫ ((z ^ p ^ n).left ≫ ψ) = 𝟙 _ ≫ ((1 : T ⟶ P.A.A).left ≫ ψ) from h2)
  have hk : 1 ≤ p ^ n := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have h := GlobalTheory.WeilCube.weilIs_pull cu hLaws.globalFns P.A.isAb Y.oF.t.PP.isLB hpb w hw
    (T := T) (T₀ := Over.mk yy) (𝟙 _) (by rw [Category.id_comp]; exact (Category.id_comp yy).symm) hx hz
    (x₀ := e) (y₀ := σ) (by simp [he, hlev]) (by simp [hσ]) hW
  have hu : ∀ u : Γ(Sp ℂ_[p], ⊤)ˣ, Units.map (Scheme.Hom.appTop (𝟙 (Sp ℂ_[p]))).hom.toMonoidHom u = u := by
    intro u; ext; simp
  erw [hu] at h
  exact_mod_cast (GlobalTheory.HTLat.weilIs_iff hk hx hz c).1 h

end GlobalTheory.ModelPointWeil
