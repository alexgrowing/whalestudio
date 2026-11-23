import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.VtfValPullGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl.CubeVal

theorem prod_three' {M : Type} [CommMonoid M] (F : Finset (Fin 3) → M) :
    ∏ s, F s = F ∅ * F {0} * F {1} * F {2} * F {0, 1} * F {0, 2} * F {1, 2} * F {0, 1, 2} := by
  rw [show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  ac_rfl

theorem prod_three {M : Type} [CommMonoid M] (F : thK.{0} → M) :
    ∏ I, F I = F ⟨∅⟩ * F ⟨{0}⟩ * F ⟨{1}⟩ * F ⟨{2}⟩ * F ⟨{0, 1}⟩ * F ⟨{0, 2}⟩ * F ⟨{1, 2}⟩ * F ⟨{0, 1, 2}⟩ :=
  (Equiv.prod_comp (Equiv.ulift.symm : Finset (Fin 3) ≃ thK.{0}) F).symm.trans (prod_three' fun s => F ⟨s⟩)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem ex_sum (d : AB N.toNumB g) {κ : Type} (s : Finset κ) (v : κ → Fin g → ℂ) :
    d.ex (∑ i ∈ s, v i) = ∏ i ∈ s, d.ex (v i) := by
  classical
  have h0 : d.ex 0 = 1 := by
    have e := d.ex_add 0 0
    rw [add_zero] at e
    exact (mul_eq_left.1 e.symm)
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, d.ex_add, ih]

theorem pt_thφ (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (I : thK.{0}) :
    (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left ≫ thφ D.P.A (x3 D.P.A) I =
      (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left := by
  show _ ≫ (psum D.P.A (x3 D.P.A) I.down).left = _
  rw [← Over.comp_left, CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.comp_prod, ex_sum, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  fin_cases i <;> simp [x3]

end GlobalTheory.MBLow.Cl.CubeVal

namespace GlobalTheory.MBLow.Cl.CubeVal

theorem thε_vals : thε ⟨(∅ : Finset (Fin 3))⟩ = -1 ∧ thε ⟨({0} : Finset (Fin 3))⟩ = 1 ∧ thε ⟨({1} : Finset (Fin 3))⟩ = 1 ∧
    thε ⟨({2} : Finset (Fin 3))⟩ = 1 ∧ thε ⟨({0, 1} : Finset (Fin 3))⟩ = -1 ∧ thε ⟨({0, 2} : Finset (Fin 3))⟩ = -1 ∧
    thε ⟨({1, 2} : Finset (Fin 3))⟩ = -1 ∧ thε ⟨({0, 1, 2} : Finset (Fin 3))⟩ = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem prod_const_zpow (r : ℂ) (hr : r ≠ 0) : ∏ I : thK.{0}, r ^ thε I = 1 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := thε_vals
  rw [prod_three, e0, e1, e2, e3, e4, e5, e6, e7]
  field_simp

theorem alg (a b f : thK.{0} → ℂ) (r θ V : ℂ) (hr : r ≠ 0) (hf : ∀ I, f I ≠ 0) (h : ∀ I, f I * r = a I * b I)
    (h1 : θ = (∏ I, a I ^ thε I) * V) (h2 : θ = ∏ I, f I ^ thε I) : V = ∏ I, b I ^ thε I := by
  have ha : ∀ I, a I ≠ 0 := fun I => left_ne_zero_of_mul (h I ▸ mul_ne_zero (hf I) hr)
  have hA : (∏ I, a I ^ thε I) ≠ 0 := Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (ha I)
  have hAB : (∏ I, a I ^ thε I) * ∏ I, b I ^ thε I = ∏ I, f I ^ thε I := by
    rw [← Finset.prod_mul_distrib]
    have e : ∀ I, a I ^ thε I * b I ^ thε I = f I ^ thε I * r ^ thε I := fun I => by
      rw [← mul_zpow, ← mul_zpow, h I]
    simp only [e, Finset.prod_mul_distrib, prod_const_zpow r hr, _root_.mul_one]
  rw [h1] at h2
  exact mul_left_cancel₀ hA (h2.trans hAB.symm)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem theta_eq_prod (d : AB N.toNumB g) (hc : d.Cub) (x y z : Fin g → ℂ) :
    (N.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) = ∏ I : thK.{0}, (d.fr (∑ i ∈ I.down, ![x, y, z] i) : ℂ) ^ thε I := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := thε_vals
  have h := congrArg Units.val (hc x y z)
  simp only [Units.val_mul] at h
  rw [prod_three, e0, e1, e2, e3, e4, e5, e6, e7]
  simp [Finset.sum_insert, d.fr_zero, ← add_assoc]
  have := (d.fr (x + y)).ne_zero
  have := (d.fr (x + z)).ne_zero
  have := (d.fr (y + z)).ne_zero
  field_simp
  linear_combination h

end GlobalTheory.MBLow.Cl.CubeVal

namespace GlobalTheory.MBLow.Cl

open CubeVal in

theorem cube_val_frame : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g), d.Cub → ∀ (G : Geo ν d) (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
    (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
    valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
      (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I := by
  intro R _ _ D _ N g ν d hc G x y z j hj
  have hpt := pt_thφ ν d x y z
  set p := (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left with hp
  have htr : ∀ I : thK.{0}, (d.fr (∑ i ∈ I.down, ![x, y, z] i) : ℂ) * ν.rg =
      valF (p ≫ thφ D.P.A (x3 D.P.A) I) (D.P.L.U (ν.J (p ≫ thφ D.P.A (x3 D.P.A) I)) ⊓ D.P.L.U (j I))
        (D.P.L.g (ν.J (p ≫ thφ D.P.A (x3 D.P.A) I)) (j I)).val * G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) := by
    intro I
    rw [hpt I, G.fr_eq]
    exact G.fr_compat _ _ _ fun q _ => ⟨ν.good _ (x := q) trivial, hj I (x := q) trivial⟩
  have hin : ⊤ ≤ p ⁻¹ᵁ (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) (fun I => ν.J (p ≫ thφ D.P.A (x3 D.P.A) I)) ⊓
      LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j) := fun q _ =>
    ⟨Set.mem_iInter.2 fun I => ν.good (p ≫ thφ D.P.A (x3 D.P.A) I) (x := q) trivial,
      Set.mem_iInter.2 fun I => by
        have h := hj I
        rw [← hpt I] at h
        exact h (x := q) trivial⟩
  have e1 := PullbackSections.vtf_isGen_val D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t D.cub.isGen p _ j hin
  have e2 := ν.θ_eq (d.ex x) (d.ex y) (d.ex z)
  exact alg _ _ (fun I => (d.fr (∑ i ∈ I.down, ![x, y, z] i) : ℂ)) ν.rg _ _ (SymFrame.rg_ne ν) (fun I => Units.ne_zero _)
    htr (e2.trans e1) (theta_eq_prod d hc x y z)

end GlobalTheory.MBLow.Cl

end
