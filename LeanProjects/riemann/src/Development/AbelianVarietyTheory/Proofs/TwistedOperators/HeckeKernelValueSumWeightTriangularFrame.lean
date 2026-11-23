import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HkRelFrOfTransportIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeckeWeight
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeckePointLaw (scaleAt tanMap tanMap_scale scaleAt_comm isCombAt_iff tanMap_left)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem comp_listProd {X Y : Over Xo.X} (f : X ⟶ Y) (L : List (Y ⟶ Xo.univ.t.G)) :
    f ≫ L.prod = (L.map (f ≫ ·)).prod := by
  induction L with
  | nil => simp [MonObj.comp_one]
  | cons b L ih => simp [List.prod_cons, MonObj.comp_mul, ih]

theorem isLieImg_comb {Ω : Type} [Field Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'} (h : IsLinHom ψ) (p : ℕ)
    {m : ℕ} {v v' : Fin m → (Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left)} (hv : ∀ k, IsLieImg p ψ (v k) (v' k))
    {cf : Fin m → Ω} {w w' : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left} (hw : IsCombAt x v cf w)
    (hw' : IsCombAt x' v' cf w') (ht : IsTanAt x w) (ht' : IsTanAt x' w') : IsLieImg p ψ w w' := by
  choose a ha hpa using fun k => (hv k).2.2
  let b : Fin m → (tEps x' ⟶ Xo.univ.t.G) := fun k => Over.homMk (v' k) (hv k).2.1.1
  have hb : ∀ k, tanMap h (a k) = scaleAt x' p ≫ b k := fun k => Over.OverMorphism.ext (by
    rw [tanMap_left, Over.comp_left, ← hpa k]; rfl)
  let W : tEps x ⟶ Xo.univ.t.G := Over.homMk w ht.1
  let W' : tEps x' ⟶ Xo.univ.t.G := Over.homMk w' ht'.1
  have eW : (List.ofFn fun k => scaleAt x (cf k) ≫ a k).prod = W := by
    rw [← isCombAt_iff]
    have : v = fun k => (a k).left := funext fun k => (ha k).symm
    subst this
    exact hw
  have eW' : (List.ofFn fun k => scaleAt x' (cf k) ≫ b k).prod = W' := (isCombAt_iff b cf W').1 hw'
  refine ⟨ht, ht', W, rfl, ?_⟩
  have key : scaleAt x' p ≫ W' = tanMap h W := by
    rw [← eW, ← eW', comp_listProd, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 2
    funext k
    simp only [Function.comp_apply]
    rw [tanMap_scale, hb, ← Category.assoc, ← Category.assoc, scaleAt_comm]
  have := congrArg (·.left) key
  simp only [Over.comp_left, tanMap_left] at this
  exact this

open GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection (TotalAt FunAt) in

theorem hkVal_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), admitted l P p → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.TotalAt Xo c P p i → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.FunAt Xo c P p i → ∀ f ∈ sec Xo c a n, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (y y' : FrPt Xo c Ω), FrBor t y y' → hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y' = wchar (ex Dw a n) t * hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y := by
  intro E _ _ _ H Dw l Xo c P p i a n hA hT hF f hf Ω _ _ _ t y y' hB
  have hS : GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.IsSplitOff l P p := hA
  obtain ⟨g, hgt, hgd, hch⟩ := (frBor_iff_frChg y y' t).1 hB
  have hdet : ∀ τ, IsUnit (g τ).det := fun τ => by
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hgt τ i j hij)]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun j _ => by rw [hgd]; exact Units.ne_zero _)
  obtain ⟨x', xo', u', tan', eig', bas', s', gen'⟩ := y'
  obtain rfl : x' = y.x := hch.1
  have hw0 : wchar (ex Dw a n) t ≠ (0 : Ω) := by
    unfold wchar
    exact Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (t j).ne_zero
  have key : ∀ C : hkKer (Xo := Xo) P p i Ω y,
      hkTerm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
        (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)
        f (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C =
      wchar (ex Dw a n) t * hkTerm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
        (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)
        f y C := by
    intro C
    have ex' := hT Ω (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C
    have ex := hT Ω y C
    unfold hkTerm
    rw [dif_pos ex', dif_pos ex]
    have hz' := ex'.choose_spec
    have hz := ex.choose_spec
    generalize ex'.choose = z' at hz' ⊢
    generalize ex.choose = z at hz ⊢
    obtain ⟨ψ, hψ, hL, hθ⟩ := (GlobalTheory.HeckeFrCompare.hkPt_iff hS _ y C.1 z).1 hz
    rw [hkTr, Equiv.apply_symm_apply] at hθ
    obtain ⟨z'', hz'', -⟩ := existsUnique_frChg E H Dw l Xo c Ω z g (t none) hdet
    have hB' : FrBor t z z'' := (frBor_iff_frChg _ _ t).2 ⟨g, hgt, hgd, hz''⟩
    obtain ⟨x'', xo'', u'', tan'', eig'', bas'', s'', gen''⟩ := z''
    obtain rfl : x'' = z.x := hz''.1
    have hP : hkRelFr P p i (hkTr Xo c p) Ω (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C
        ⟨z.x, xo'', u'', tan'', eig'', bas'', s'', gen''⟩ := by
      show HkPt p (hkTr Xo c p Ω) (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C.1
        ⟨z.x, xo'', u'', tan'', eig'', bas'', s'', gen''⟩
      refine (GlobalTheory.HeckeFrCompare.hkPt_iff hS (hkTr Xo c p Ω) (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C.1
        ⟨z.x, xo'', u'', tan'', eig'', bas'', s'', gen''⟩).2 ⟨ψ, hψ, fun τ j => ?_, ?_⟩
      · exact GlobalTheory.HeckeWeight.isLieImg_comb hψ.2.1 p (hL τ) (hch.2.1 τ j) (hz''.2.1 τ j) (tan' τ j) (tan'' τ j)
      · rw [hkTr, Equiv.apply_symm_apply]
        exact hθ.smul (toΓ Ω (t none : Ω)) ((ChgOf.secBC_id_iff _ _ _ _).1 hch.2.2)
          ((ChgOf.secBC_id_iff _ _ _ _).1 hz''.2.2)
    obtain rfl := (frMap_unique_refl_iff E H Dw l Xo c Ω Ω (AlgHom.id c.F Ω) z').1 _ _
      (frMap_unique_refl_iff E H Dw l Xo c Ω Ω (AlgHom.id c.F Ω) z').2.1 (hF Ω (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C z' _ hz' hP)
    exact (algebraic_laws lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 Ω inferInstance a n f hf t z _ hB'
  unfold hkVal
  refine (finsum_congr key).trans ?_
  exact (mul_finsum _ _).symm

end GlobalTheory.HeckeWeight
