import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev grK (K : Type) [Field K] (N : ℕ) := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K

theorem xv_mem (K : Type) [Field K] (N : ℕ) (j : Fin (N + 1)) : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) K) ∈ grK K N 1 :=
  MvPolynomial.isHomogeneous_X K j

def evV {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (g : MvPolynomial (Fin (N + 1)) K)
    (V : X.Opens) (h : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) : HomogeneousLocalization.Away (grK K N) g →+* Γ(X, V) :=
  (i.appLE _ V h).hom.comp (Proj.awayToSection (grK K N) g).hom

def homIdeal {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) : Ideal (MvPolynomial (Fin (N + 1)) K) :=
  Ideal.span {f | ∃ (d : ℕ) (hf : f ∈ grK K N (d • 1)), ∀ j : Fin (N + 1),
    evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf) = 0}

def yS {K : Type} [Field K] {N m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (S : Finset (Fin m)) :
    MvPolynomial (Fin (N + 1)) K :=
  ∏ k ∈ S, y k

theorem yS_mem {K : Type} [Field K] {N m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (S : Finset (Fin m)) : yS y S ∈ grK K N (S.card * e) := by
  have h := MvPolynomial.IsHomogeneous.prod S y (fun _ => e) (fun k _ => hy k)
  simpa [yS, Finset.sum_const, smul_eq_mul] using h

theorem aeval_mem {K : Type} [Field K] {N m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (S : Finset (Fin m)) {j : ℕ} (c : MvPolynomial (Fin m) K)
    (hc : c.IsHomogeneous (j * S.card)) : MvPolynomial.aeval y c ∈ grK K N (j • (S.card * e)) := by
  have h := hc.aeval y hy
  rw [MvPolynomial.mem_homogeneousSubmodule, smul_eq_mul]
  convert h using 1
  ring

def yRatio {K : Type} [Field K] {N e d : ℕ} (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (k : Fin d) : Γ(PSpace K N, Proj.basicOpen _ (y 0)) :=
  (Proj.awayToSection _ (y 0)).hom
    (HomogeneousLocalization.Away.mk _ ((MvPolynomial.mem_homogeneousSubmodule e (y 0)).2 (hy 0)) 1 (y k.succ)
      (by simpa using (MvPolynomial.mem_homogeneousSubmodule e (y k.succ)).2 (hy k.succ)))

def tV {K : Type} [Field K] {X : Scheme.{0}} {N e d : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (V : X.Opens)
    (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) (k : Fin d) : Γ(X, V) :=
  (i.appLE _ V (hV.trans (iInf_le (fun k => i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) 0))).hom (yRatio y hy k)

abbrev resO {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) : Γ(X, W) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom

theorem le_biInf_of_le {X : Scheme.{0}} {m : ℕ} {U : Fin m → X.Opens} {V : X.Opens} (hV : V ≤ ⨅ k, U k)
    (S : Finset (Fin m)) : V ≤ ⨅ k ∈ S, U k :=
  hV.trans (le_iInf₂ fun k _ => iInf_le U k)

theorem strV_res {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V W : X.Opens}
    (h : V ≤ W) : strV q V = (resO h).comp (strV q W) := by
  change _ = CommRingCat.Hom.hom (((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appLE ⊤ W le_top) ≫
      X.presheaf.map (homOfLE h).op)
  rw [Category.assoc, Scheme.Hom.appLE_map]
  rfl

end CrystallineSemistableComparison.Pb
