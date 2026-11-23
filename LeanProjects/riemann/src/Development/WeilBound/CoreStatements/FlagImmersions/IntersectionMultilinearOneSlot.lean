import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.WeilBound.CoreStatements.FlagImmersions.CombLineSmoothConjInvariant

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

namespace Ii

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in
theorem hermLine_ext {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  simp only at ha hh
  subst ha hh
  rfl

open Classical in

noncomputable def indLine (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι where
  a := 0
  h z := if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then 1 else 0
  pos z hz := by rw [if_pos hz]; exact one_pos
  smul c z hc := by
    have : (∀ k, ∃ i, c k * z ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
      simp [hc]
    simp only [this]
    simp

theorem indLine_smooth : IsSmoothHerm (indLine ι) :=
  (contDiffOn_const (c := (1 : ℝ))).congr fun _ hz => if_pos hz

theorem tensor_indLine {A B : HermLine ι} (ha : A.a = B.a)
    (hh : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A.h z = B.h z) :
    A.tensor (indLine ι) = B.tensor (indLine ι) := by
  refine hermLine_ext (by simp [HermLine.tensor, ha]) (funext fun z => ?_)
  by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · show A.h z * _ = B.h z * _
    rw [hh z hz]
  · have : (indLine ι).h z = 0 := if_neg hz
    show A.h z * _ = B.h z * _
    rw [this, mul_zero, mul_zero]

theorem additive_congr (φ : HermLine ι → ℝ)
    (hφ : ∀ A B, IsSmoothHerm A → IsSmoothHerm B → φ (A.tensor B) = φ A + φ B)
    {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (ha : A.a = B.a)
    (hh : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A.h z = B.h z) : φ A = φ B := by
  have h1 := hφ A _ hA indLine_smooth
  have h2 := hφ B _ hB indLine_smooth
  rw [tensor_indLine ha hh] at h1
  linarith

theorem combLine_single {J : Type} [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (j : J) :
    combLine ℓ (Pi.single j 1) = ℓ j := by
  refine hermLine_ext ?_ (funext fun z => ?_)
  · show ∑ i, (Pi.single j 1 : J → ℤ) i • (ℓ i).a = _
    rw [Finset.sum_eq_single j] <;> simp +contextual
  · show ∏ i, (ℓ i).h z ^ (Pi.single j 1 : J → ℤ) i = _
    rw [Finset.prod_eq_single j] <;> simp +contextual

theorem tensor_smooth {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) := ContDiffOn.mul hA hB

theorem additive_comb (φ : HermLine ι → ℝ)
    (hφ : ∀ A B, IsSmoothHerm A → IsSmoothHerm B → φ (A.tensor B) = φ A + φ B)
    {J : Type} [Fintype J] (ℓ : J → HermLine ι) (hℓ : ∀ j, IsSmoothHerm (ℓ j)) (n : J → ℤ) :
    φ (combLine ℓ n) = ∑ j, (n j : ℝ) * φ (ℓ j) := by
  classical
  have hs : ∀ m, IsSmoothHerm (combLine ℓ m) := fun m => (combLine_smooth_conj_invariant K ι J ℓ m).1 hℓ
  let ψ : (J → ℤ) →+ ℝ := AddMonoidHom.mk' (fun m => φ (combLine ℓ m)) (fun m m' => by
    show φ _ = φ _ + φ _
    rw [← hφ _ _ (hs m) (hs m')]
    refine additive_congr φ hφ (hs _) (tensor_smooth (hs m) (hs m')) ?_ fun z hz => ?_
    · show ∑ i, (m + m') i • (ℓ i).a = ∑ i, m i • (ℓ i).a + ∑ i, m' i • (ℓ i).a
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    · show ∏ i, (ℓ i).h z ^ (m + m') i = (∏ i, (ℓ i).h z ^ m i) * ∏ i, (ℓ i).h z ^ m' i
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => zpow_add₀ ((ℓ i).pos z hz).ne' _ _)
  have hn : n = ∑ j, n j • (Pi.single j 1 : J → ℤ) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  show ψ n = _
  conv_lhs => rw [hn]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, zsmul_eq_mul]
  show _ * φ (combLine ℓ (Pi.single j 1)) = _
  rw [combLine_single]

end

end Ii

open Ii in
theorem intersection_multilinear_one_position : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (L : Fin d → HermLine ι) (k : Fin d) (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), IsArithVar P d → (∀ i, IsSmoothHerm (L i)) → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (Function.update L k (combLine ℓ n)) = ∑ j, (n j : ℝ) * II K ι P d (Function.update L k (ℓ j)) := by
  intro II hII K _ ι _ P d L k J _ ℓ n hP hL hℓ
  exact additive_comb (fun A => II K ι P d (Function.update L k A))
    (fun A B hA hB => hII.2.1 K ι P d L k A B hP hL hA hB) ℓ hℓ n

end RootFieldNumerics
