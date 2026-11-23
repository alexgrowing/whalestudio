import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.IsomT

variable {X : Scheme.{0}}

theorem res_twice {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u := by
  apply Units.ext
  show (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom (u : Γ(X, U))) =
    (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom (u : Γ(X, U))
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem units_ext_cover {ι : Type} (V : ι → X.Opens) (hc : ⨆ i, V i = ⊤) {W : X.Opens}
    {f g : Γ(X, W)ˣ} (h : ∀ i, res (inf_le_left : W ⊓ V i ≤ W) f = res inf_le_left g) : f = g := by
  apply Units.ext
  have hcov : W ≤ ⨆ i, W ⊓ V i := by
    rw [← inf_iSup_eq, hc, inf_top_eq]
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i => W ⊓ V i) W (fun i => homOfLE inf_le_left) hcov _ _
    fun i => ?_
  exact congrArg Units.val (h i)

theorem exists_glue {ι : Type} (V : ι → X.Opens) (hc : ⨆ i, V i = ⊤) (W : X.Opens)
    (f : ∀ i, Γ(X, W ⊓ V i)ˣ)
    (hf : ∀ i j, res (inf_le_left : (W ⊓ V i) ⊓ (W ⊓ V j) ≤ W ⊓ V i) (f i) =
      res inf_le_right (f j)) :
    ∃ u : Γ(X, W)ˣ, ∀ i, res inf_le_left u = f i := by
  have hcov : W ≤ ⨆ i, W ⊓ V i := by
    rw [← inf_iSup_eq, hc, inf_top_eq]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i => W ⊓ V i) W
    (fun i => homOfLE inf_le_left) hcov (fun i => ((f i : Γ(X, W ⊓ V i))))
    (fun i j => congrArg Units.val (hf i j))
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i => W ⊓ V i) W
    (fun i => homOfLE inf_le_left) hcov (fun i => (((f i)⁻¹ : Γ(X, W ⊓ V i)ˣ) : Γ(X, W ⊓ V i)))
    (fun i j => by
      have := congrArg Units.val (congrArg (·⁻¹) (hf i j))
      rw [← map_inv, ← map_inv] at this
      exact this)
  have hst : s * t = 1 := by
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i => W ⊓ V i) W (fun i => homOfLE inf_le_left) hcov _ _
      fun i => ?_
    rw [map_mul, map_one, hs i, ht i]
    exact (f i).mul_inv
  refine ⟨⟨s, t, hst, by show (t : Γ(X, W)) * s = 1; rw [mul_comm]; exact hst⟩, fun i => Units.ext ?_⟩
  exact hs i

theorem ofMem {V U : X.Opens} (h : ∀ x, x ∈ V → x ∈ U) : V ≤ U := by
  intro x hx
  exact h x hx

def wu {B C : LB X} (w : LB.Iso B C) (a : C.ι) (b : B.ι) : Γ(X, C.U a ⊓ B.U b)ˣ := w.s (a, b)

theorem cg₁ {G : Type*} [CommGroup G] {x y g p q : G} (h : x * g = y) (h' : q = g * p) :
    x⁻¹ * p = y⁻¹ * q := by
  subst h
  subst h'
  rw [mul_inv, mul_assoc, inv_mul_cancel_left]

theorem cg₂ {G : Type*} [CommGroup G] {x y g p : G} (h : x = g * y) :
    y⁻¹ * p = g * (x⁻¹ * p) := by
  subst h
  rw [mul_inv, mul_assoc g⁻¹, mul_inv_cancel_left]

end GlobalTheory.CompanionTheory.MPDict.IsomT

namespace GlobalTheory.CompanionTheory.MPDict

open IsomT

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k)
    {W W' : (MP ℤ m n).Opens} (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (h' : W' ≤ W) :
    res h' (blockUnit i j h) = blockUnit i j (h'.trans h) := by
  unfold blockUnit
  exact res_twice _ _ _

theorem res_mul_prod (c c' : ∀ k, Bk n k) (e : Fin (m + 1) → ℤ)
    {W W' : (MP ℤ m n).Opens} (x : Γ(MP ℤ m n, W)ˣ)
    (H : ∀ k, W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) (h' : W' ≤ W) :
    res h' (x * ∏ k, blockUnit (c k) (c' k) (H k) ^ e k) =
      res h' x * ∏ k, blockUnit (c k) (c' k) (h'.trans (H k)) ^ e k := by
  rw [map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, res_blockUnit]

end GlobalTheory.CompanionTheory.MPDict
