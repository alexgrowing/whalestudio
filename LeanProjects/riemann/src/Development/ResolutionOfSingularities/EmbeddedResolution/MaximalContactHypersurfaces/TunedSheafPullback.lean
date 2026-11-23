import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupDerivativeIdealBound
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.le_of_pow_mul_le_pow_mul {Y : Scheme.{u}}
    {F B B' : Y.IdealSheafData} (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (n : ℕ)
    (h : F ^ n * B ≤ F ^ n * B') : B ≤ B' :=
  (hF.pow n).le_of_mul_le_mul h

theorem comap_prod_map_range {X Y : Scheme.{u}} (π : Y ⟶ X) (f : ℕ → X.IdealSheafData) (m : ℕ) :
    (((List.range m).map f).prod).comap π =
      ((List.range m).map (fun j => (f j).comap π)).prod := by
  induction m with
  | zero =>
    simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_append, List.prod_append,
      AlgebraicGeometry.Scheme.IdealSheafData.comap_mul, ih]
    simp

private theorem prod_map_range_le {X : Scheme.{u}} (f g : ℕ → X.IdealSheafData) :
    ∀ m : ℕ, (∀ j, j < m → f j ≤ g j) →
      ((List.range m).map f).prod ≤ ((List.range m).map g).prod := fun _ h =>
  List.prod_le_prod' fun j hj => h j (List.mem_range.mp hj)

private theorem prod_map_range_congr {X : Scheme.{u}} (f g : ℕ → X.IdealSheafData) :
    ∀ m : ℕ, (∀ j, j < m → f j = g j) →
      ((List.range m).map f).prod = ((List.range m).map g).prod := fun _ h =>
  congrArg List.prod (List.map_congr_left fun j hj => h j (List.mem_range.mp hj))

private theorem prod_map_pow_mul_pow_eq {X : Scheme.{u}} (F : X.IdealSheafData)
    (G : ℕ → X.IdealSheafData) (w c : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map (fun j => (F ^ (w j) * G j) ^ (c j))).prod =
      F ^ (∑ j ∈ Finset.range n, w j * c j) *
        ((List.range n).map (fun j => G j ^ (c j))).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_append, List.prod_append,
      ih, Finset.sum_range_succ, pow_add]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_pow,
      ← pow_mul]
    rw [mul_mul_mul_comm]

theorem comap_tunedSheaf_le_exceptionalIdeal_pow_mul (k : Type u) [Field k] [CharZero k]
    [IsNoetherianRing k] {P P₁ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p] [IsLocallyNoetherian P₁]
    (π : P₁ ⟶ P) [LocallyOfFiniteType (π ≫ p)] (p₁ : P₁ ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p₁] (hp₁ : p₁ = π ≫ p)
    (Z : P.IdealSheafData) (E : List P.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (A : P.IdealSheafData) (m : ℕ) (hA : A ≤ Z ^ m) (u : ℕ) :
    (tunedSheaf k p A m u).comap π ≤
      Blowup.exceptionalIdeal π Z ^ u *
        tunedSheaf k p₁ (controlledTransform π Z A m hπ hA) m u := by
  subst hp₁
  refine le_trans (Scheme.IdealSheafData.comap_iSup π
    (fun c : {c : ℕ → ℕ // u ≤ ∑ j ∈ Finset.range m, (m - j) * c j} =>
      ((List.range m).map (fun j => derivIdealSheafIterate k p j A ^ (c.1 j))).prod)).le
    (iSup_le ?_)
  rintro ⟨c, hc⟩
  refine le_trans (le_of_eq (comap_prod_map_range π
    (fun j => derivIdealSheafIterate k p j A ^ c j) m)) ?_
  refine le_trans (prod_map_range_le _
    (fun j => (Blowup.exceptionalIdeal π Z ^ (m - j) *
      derivIdealSheafIterate k (π ≫ p) j (controlledTransform π Z A m hπ hA)) ^ c j) m ?_) ?_
  · intro j hj
    refine le_trans (le_of_eq (AlgebraicGeometry.Scheme.IdealSheafData.comap_pow
      (derivIdealSheafIterate k p j A) π (c j))) ?_
    exact pow_le_pow_left'
      (comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z E hZ hπ A m hA j
        (Nat.le_of_lt hj)) (c j)
  · refine le_trans (le_of_eq (prod_map_pow_mul_pow_eq (Blowup.exceptionalIdeal π Z)
      (fun j => derivIdealSheafIterate k (π ≫ p) j (controlledTransform π Z A m hπ hA))
      (fun j => m - j) c m)) ?_
    refine mul_le_mul' (pow_le_pow_right_of_le_one' le_top hc) ?_
    exact le_iSup (fun d : {c : ℕ → ℕ // u ≤ ∑ j ∈ Finset.range m, (m - j) * c j} =>
      ((List.range m).map (fun j => derivIdealSheafIterate k (π ≫ p) j
        (controlledTransform π Z A m hπ hA) ^ (d.1 j))).prod) ⟨c, hc⟩

theorem comap_tunedSheaf_of_smooth (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k]
    {P Y : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [LocallyOfFiniteType p] (h : Y ⟶ P) [AlgebraicGeometry.Smooth h]
    (q : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q] (hq : q = h ≫ p)
    (A : P.IdealSheafData) (m u : ℕ) :
    (tunedSheaf k p A m u).comap h = tunedSheaf k q (A.comap h) m u := by
  subst hq
  refine le_antisymm ?_ ?_
  · refine le_trans (Scheme.IdealSheafData.comap_iSup h
      (fun c : {c : ℕ → ℕ // u ≤ ∑ j ∈ Finset.range m, (m - j) * c j} =>
        ((List.range m).map (fun j => derivIdealSheafIterate k p j A ^ (c.1 j))).prod)).le
      (iSup_le ?_)
    rintro ⟨c, hc⟩
    refine le_trans (le_of_eq (comap_prod_map_range h
      (fun j => derivIdealSheafIterate k p j A ^ c j) m)) ?_
    refine le_trans (prod_map_range_le _
      (fun j => derivIdealSheafIterate k (h ≫ p) j (A.comap h) ^ c j) m ?_) ?_
    · intro j _
      refine le_of_eq ?_
      show (derivIdealSheafIterate k p j A ^ c j).comap h
          = derivIdealSheafIterate k (h ≫ p) j (A.comap h) ^ c j
      rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_pow,
        derivIdealSheafIterate_comap k p h j A]
    · exact le_iSup (fun d : {c : ℕ → ℕ // u ≤ ∑ j ∈ Finset.range m, (m - j) * c j} =>
        ((List.range m).map (fun j =>
          derivIdealSheafIterate k (h ≫ p) j (A.comap h) ^ (d.1 j))).prod) ⟨c, hc⟩
  · refine le_trans (le_of_eq (tunedSheaf_eq_iSup k (h ≫ p) (A.comap h) m u)) (iSup_le ?_)
    rintro ⟨c, hc⟩
    refine le_trans (le_of_eq ?_) (AlgebraicGeometry.Scheme.IdealSheafData.comap_mono h
      (le_iSup (fun d : {c : ℕ → ℕ // u ≤ ∑ j ∈ Finset.range m, (m - j) * c j} =>
        ((List.range m).map (fun j => derivIdealSheafIterate k p j A ^ (d.1 j))).prod) ⟨c, hc⟩))
    refine Eq.trans (prod_map_range_congr _
      (fun j => (derivIdealSheafIterate k p j A ^ c j).comap h) m ?_)
      (comap_prod_map_range h (fun j => derivIdealSheafIterate k p j A ^ c j) m).symm
    intro j _
    show derivIdealSheafIterate k (h ≫ p) j (A.comap h) ^ c j
        = (derivIdealSheafIterate k p j A ^ c j).comap h
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_pow, derivIdealSheafIterate_comap k p h j A]

end FunctorialResolution.EmbeddedResolution
