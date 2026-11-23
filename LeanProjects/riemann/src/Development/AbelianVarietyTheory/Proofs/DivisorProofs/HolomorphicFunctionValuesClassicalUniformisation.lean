import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
open ReciprocityTheory.ChartRestriction.G.PullbackSections

noncomputable section

namespace GlobalTheory.MBLow.Cl.HolB

variable {X Y : Scheme.{0}}

theorem valF_comp_app (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valF x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valF (x ≫ φ) U f := by
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [valF, valF, dif_pos h', dif_pos h]
    simp only [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [valF, valF, dif_neg h', dif_neg h]

theorem valF_eq_valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valF x U f = valAt' x U f := rfl

def psiB (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left)
    (hw : φ ≫ D.P.A.hom = x.P.A.hom ≫ spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) :
    x.P.A.left ⟶ (DegPre.BF D ℂ).left :=
  (lift (Over.homMk x.P.A.hom rfl : Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ TF (R := R) ℂ)
    (Over.homMk φ (by
      rw [hw]; simp only [Over.mk_hom, TF, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) :
      Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ D.P.A)).left

theorem hol_ptB : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (N : NumD ℂ)
    (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (φ : x.P.A.left ⟶ D.P.A.left),
    IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ → (∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ) →
    ∀ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)), IsOpen {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valF (ptB ν d z) U f) {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} := by
  intro R _ _ _ D N ν g d x u φ hφ hE U f
  have hw := hφ.1.w
  have key : ∀ z, ptB ν d z = (u.ex z).left ≫ psiB R D x φ hw := by
    intro z
    have h0 : (u.ex z).left ≫ x.P.A.hom = 𝟙 _ := Over.w (u.ex z)
    let e : TF (R := R) ℂ ⟶ Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) :=
      Over.homMk (u.ex z).left (by simp only [Over.mk_hom]; rw [← Category.assoc, h0]; exact Category.id_comp _)
    have he : e ≫ lift (Over.homMk x.P.A.hom rfl : Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ TF (R := R) ℂ)
        (Over.homMk φ (by
          rw [hw]; simp only [Over.mk_hom, TF, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) :
          Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ D.P.A) = lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)) := by
      rw [comp_lift]
      congr 1
      · ext; simp [e, h0]
      · ext; simp [e, hE z]
    rw [ptB, ← he]
    rfl
  have hs : {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (psiB R D x φ hw ⁻¹ᵁ U)} := by
    ext z
    simp only [Set.mem_setOf_eq, key z, Scheme.Hom.comp_preimage]
  obtain ⟨ho, hd⟩ := u.hol (psiB R D x φ hw ⁻¹ᵁ U) ((psiB R D x φ hw).app U |>.hom f)
  rw [hs]
  refine ⟨ho, hd.congr fun z _ => ?_⟩
  rw [← valF_eq_valAt', valF_comp_app, key z]

end GlobalTheory.MBLow.Cl.HolB

end
