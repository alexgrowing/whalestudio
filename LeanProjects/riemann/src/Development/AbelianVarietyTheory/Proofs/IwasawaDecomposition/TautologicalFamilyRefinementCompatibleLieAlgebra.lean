import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRingStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.TieUp

theorem exists_lift {ι : Type} {m k : ι → ℕ} {R K : Type} [CommRing R] [Field K] (a : R →+* K)
    (ha : Function.Injective a) {O : Subring K} (hO : ∀ x ∈ O, ∃ r, a r = x) {G : Mat m K} (hG : Par k O G) :
    ∃ G' : Mat m R, G'.map a = G ∧ ∀ τ, IsUnit (G' τ).det := by
  have h1 : ∀ τ i j, ∃ r, a r = G τ i j := fun τ i j => hO _ ((hG τ).1 i j)
  choose G' hG' using h1
  let G'' : Mat m R := fun τ => Matrix.of (G' τ)
  have e : G''.map a = G := by
    funext τ; ext i j; exact hG' τ i j
  refine ⟨G'', e, fun τ => ?_⟩
  obtain ⟨r, hr⟩ := hO _ (hG τ).2.2.1
  have hd : a (G'' τ).det = (G τ).det := by
    rw [← e]; exact a.map_det (G'' τ)
  refine IsUnit.of_mul_eq_one r (ha ?_)
  rw [map_mul, hd, hr, map_one, mul_inv_cancel₀ (hG.det_ne τ)]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B Y : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (k : (E →+* ℂ) → ℕ) (S' : Fr (ratOf Y) Dw.mult k) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X), Tied e B j f₀ S A₀ → Refines S S' φ f → ∃ (g₀ : EigFrame Z (constF e Y) (genericPt Y ≫ (f ≫ j) ≫ genι Z)) (A₁ : Mat Dw.mult Y.Fn), Tied e Y (f ≫ j) g₀ S' A₁ ∧ f₀.Coord (φ : B.Fn →+* Y.Fn) g₀ (A₁ * (A₀.map φ)⁻¹) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e B Y j f₀ S A₀ k S' φ f hT hR
  obtain ⟨A₁, hA₁⟩ := S'.nonempty (genericPoint Y.X)
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := Fr.det_ne hA₁
  have hmapd : ∀ {A : Mat Dw.mult B.Fn}, (∀ τ, (A τ).det ≠ 0) →
      ∀ τ, (A.map (φ : B.Fn →+* Y.Fn) τ).det ≠ 0 := fun {A} hA τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hA τ)
  have hgen : genericPt Y ≫ f = spMap (φ : B.Fn →+* Y.Fn) ≫ genericPt B := hR.hom
  have hx : genericPt Y ≫ (f ≫ j) ≫ genι Z = spMap (φ : B.Fn →+* Y.Fn) ≫ genericPt B ≫ j ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, hgen, Category.assoc]
  have hc : constF e Y = (φ : B.Fn →+* Y.Fn).comp (constF e B) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hst₀ : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f₀ inferInstance
  obtain ⟨g₀, hg₀⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f₀ Y.Fn (constF e Y)
    (genericPt Y ≫ (f ≫ j) ≫ genι Z) (φ : B.Fn →+* Y.Fn) inferInstance hst₀ hx hc).2
    (A₁ * (A₀.map (φ : B.Fn →+* Y.Fn))⁻¹) fun τ => by
      rw [Pi.mul_apply, Matrix.det_mul, Pi.inv_apply, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact Ne.isUnit (mul_ne_zero (hA₁d τ) (inv_ne_zero (hmapd hA₀d τ)))
  refine ⟨g₀, A₁, ⟨hA₁, fun y A' hA' => ?_⟩, hg₀⟩
  obtain ⟨A, hA⟩ := S.nonempty (f y)
  obtain ⟨φ₁, fA, hfA⟩ := hT.2 (f y) A hA
  have hAd : ∀ τ, (A τ).det ≠ 0 := Fr.det_ne hA
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  let aY : Y.X.presheaf.stalk y →+* Y.Fn := algebraMap (Y.X.presheaf.stalk y) Y.X.functionField
  let aB : B.X.presheaf.stalk (f y) →+* B.Fn := algebraMap (B.X.presheaf.stalk (f y)) B.X.functionField
  let σ : B.X.presheaf.stalk (f y) →+* Y.X.presheaf.stalk y := (f.stalkMap y).hom
  have hcomp : (φ : B.Fn →+* Y.Fn).comp aB = aY.comp σ :=
    RingHom.ext fun a => map_algebraMap_stalk hR.hom y a
  obtain ⟨G, hG, hGd⟩ := exists_lift aY (IsFractionRing.injective (Y.X.presheaf.stalk y) Y.X.functionField)
    (fun x hx => mem_O_ratOf.1 hx) (hR.sub y A' hA' A hA)
  have hstA : fA.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ fA inferInstance
  have hσ : spMap σ ≫ stalkPt B (f y) = stalkPt Y y ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hx' : stalkPt Y y ≫ (f ≫ j) ≫ genι Z = spMap σ ≫ stalkPt B (f y) ≫ j ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, ← hσ, Category.assoc]
  obtain ⟨f', hf'⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA (Y.X.presheaf.stalk y) (σ.comp φ₁)
    (stalkPt Y y ≫ (f ≫ j) ≫ genι Z) σ inferInstance hstA hx' rfl).2 G hGd
  have hst' : f'.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f' inferInstance
  have haY : spMap aY ≫ stalkPt Y y = genericPt Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)
  have hx'' : genericPt Y ≫ (f ≫ j) ≫ genι Z = spMap aY ≫ stalkPt Y y ≫ (f ≫ j) ≫ genι Z := by
    rw [← haY, Category.assoc]
  have hc' : constF e Y = aY.comp (σ.comp φ₁) := by
    rw [← RingHom.comp_assoc, ← hcomp, RingHom.comp_assoc, hc, hfA.2.1]
  obtain ⟨T, hTc, -⟩ := ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f' Y.Fn (constF e Y)
    (genericPt Y ≫ (f ≫ j) ≫ genι Z) aY inferInstance hst' hx'' hc').1 g₀).1
  have h1 := GlobalTheory.ShFam.CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f' _ _ _ g₀ σ aY G T inferInstance hf' hTc
  have h2 := GlobalTheory.ShFam.CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f₀ _ _ _ g₀ aB (φ : B.Fn →+* Y.Fn) _ _
    inferInstance hfA hg₀
  rw [hcomp] at h2
  have hu := ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA Y.Fn (constF e Y)
    (genericPt Y ≫ (f ≫ j) ≫ genι Z) (aY.comp σ) inferInstance hstA h1.1 h1.2.1).1 g₀).1.unique h1 h2
  have hG' : G.map aY = A' * (A.map (φ : B.Fn →+* Y.Fn))⁻¹ := hG
  rw [hG', Mat.map_mul, Mat.map_inv, ← mul_assoc, ← mul_assoc, mul_assoc A₁, Mat.inv_mul (hmapd hA₀d), mul_one] at hu
  have hT' : T = A₁ * A'⁻¹ := by
    have h3 := congrArg (fun M => M * A.map (φ : B.Fn →+* Y.Fn) * A'⁻¹) hu
    rwa [mul_assoc (T * A'), mul_assoc A₁, Mat.inv_mul (hmapd hAd), mul_one, mul_one, mul_assoc,
      Mat.mul_inv hA'd, mul_one] at h3
  exact ⟨σ.comp φ₁, f', hT' ▸ hTc⟩

end GlobalTheory.ShFam.TieUp
