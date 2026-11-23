import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory OnePoint
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real ComplexOrder
open GlobalTheory.HermFrame

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BcUnique

theorem re_dens_ofValues_one (β : V 1 → V 1 → ℂ) :
    (dens (ofValues β : Alt 1)).re = 2 * diagVal β (EuclideanSpace.single 0 1) := by
  obtain ⟨c, hc, e⟩ := vol_eq 1
  have hv : (vol 1 : Alt 1) = (Complex.I / 2) • ((sym (0, 0) : Ev 1) : Alt 1) := by
    simp [vol, Fin.prod_univ_one]
  have ho : (ofValues β : Alt 1) = β (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) • ((sym (0, 0) : Ev 1) : Alt 1) := by
    simp [ofValues, Fin.sum_univ_one, GlobalTheory.GoodMetric.coordVec]
  have hr : (bas 1).repr (vol 1 : Alt 1) Finset.univ = c := by simp [e]
  rw [hv, _root_.map_smul, Finsupp.smul_apply, smul_eq_mul] at hr
  have hr0 : (bas 1).repr ((sym (0, 0) : Ev 1) : Alt 1) Finset.univ ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hr; exact hc hr.symm
  rw [dens, ho, hv, _root_.map_smul, _root_.map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
    mul_div_mul_right _ _ hr0, div_div_eq_mul_div, Complex.div_I, diagVal]
  simp [Complex.mul_re]
  ring

end GlobalTheory.BcUnique

namespace GlobalTheory.BcUnique

theorem integral_bcFld_seq (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (h : IsRegVar p 1)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (r s : ℕ) (g : VMetric p S.X₂ (r + s)) (G : g.IsCInf)
    (hi : VB.IsSubbundle S.f) (h₁ : VB.IsVB S.X₁ r) (h₃ : VB.IsVB S.X₃ s) (σ : k →+* ℂ)
    (_ : (g.met σ).bcMeas hS h₁ h₃ univ ≠ ⊤) :
    (h.atlas σ).integral (bcFld (h.seq hS (G.restrict hi h₁) G (G.quot hS h₁ h₃) σ)) =
      ((g.met σ).bcMeas hS h₁ h₃ univ).toReal := by
  set T := h.seq hS (G.restrict hi h₁) G (G.quot hS h₁ h₃) σ
  have key : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source,
      (dens ((h.atlas σ).loc (bcFld T) c (c.e y))).re = (g.met σ).bcDens hS h₁ h₃ c y := by
    intro c y hy
    have hl : (h.atlas σ).loc (bcFld T) c (c.e y) = bcFld T ⟨(c, y), hy⟩ := (h.atlas σ).loc_crd _ ⟨(c, y), hy⟩
    rw [hl]
    exact re_dens_ofValues_one _
  have e₁ : (h.atlas σ).part (bcFld T) 1 = CurveDens.part fun c y => (g.met σ).bcDens hS h₁ h₃ c y := by
    refine (CurveDens.part_congr
      (ρ := fun c y => (((1 : ℤˣ) : ℤ) : ℝ) * (dens ((h.atlas σ).loc (bcFld T) c (c.e y))).re) ?_ : _)
    intro c y hy
    simp only [Units.val_one, Int.cast_one, one_mul, key c y hy]
  have e₂ : (h.atlas σ).part (bcFld T) (-1) = CurveDens.part fun c y => -(g.met σ).bcDens hS h₁ h₃ c y := by
    refine (CurveDens.part_congr
      (ρ := fun c y => (((-1 : ℤˣ) : ℤ) : ℝ) * (dens ((h.atlas σ).loc (bcFld T) c (c.e y))).re) ?_ : _)
    intro c y hy
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul, key c y hy]
  rw [HolAtlas.integral, e₁, e₂, ← CurveDens.total_bcDens hS h₁ h₃ (G σ)]
  rfl

end GlobalTheory.BcUnique
