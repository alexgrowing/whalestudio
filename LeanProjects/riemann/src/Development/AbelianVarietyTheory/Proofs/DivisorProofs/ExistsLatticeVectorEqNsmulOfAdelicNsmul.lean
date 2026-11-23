import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.LatDvd

variable {p : ℕ} [Fact p.Prime]

def adBasis {D : Datum p} {J : Type} (b : Module.Basis J ℤ D.La) : Module.Basis J (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (b.baseChange ℚ).baseChange (AfP p)

theorem adBasis_repr_inAf {D : Datum p} {J : Type} (b : Module.Basis J ℤ D.La) (z : D.La) (i : J) :
    (adBasis b).repr (inAf D z) i = algebraMap ℚ (AfP p) ((b.repr z i : ℤ) : ℚ) := by
  simp only [adBasis, inAf, Module.Basis.baseChange_repr_tmul]
  rw [Algebra.algebraMap_eq_smul_one]
  simp

theorem isIntAf_adBasis_repr {D : Datum p} {J : Type} (b : Module.Basis J ℤ D.La) (i : J) {w : AfP p ⊗[ℚ] VQ D}
    (hw : w ∈ LaHat D) : IsIntAf ((adBasis b).repr w i) := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    have e : (adBasis b).repr (c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D)) i = ((b.repr x i : ℤ) : AfP p) * c := by
      simp [adBasis, Algebra.smul_def]
    rw [e]
    intro v
    rw [map_mul, map_intCast]
    exact mul_mem (intCast_mem _ _) (hc v)
  | zero =>
    intro v
    rw [map_zero, Finsupp.zero_apply, map_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    intro v
    rw [map_add, Finsupp.add_apply, map_add]
    exact add_mem (hx v) (hy v)
  | neg x _ hx =>
    intro v
    rw [map_neg, Finsupp.neg_apply, map_neg]
    exact neg_mem (hx v)

theorem exists_eq_nsmul_of_inAf (p : ℕ) [Fact p.Prime] (D : Datum p) (n : ℕ) (_hn : 0 < n) (_hc : n.Coprime p)
    (h : ∀ (c : ℤ) (a : AfP p), IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c)
    (z : D.La) (hz : ∃ w ∈ LaHat D, inAf D z = n • w) : ∃ u : D.La, z = n • u := by
  obtain ⟨w, hw, e⟩ := hz
  have := D.freeLa
  have := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  have hd : ∀ i, (n : ℤ) ∣ b.repr z i := by
    intro i
    refine h _ _ (isIntAf_adBasis_repr b i hw) ?_
    rw [← adBasis_repr_inAf, e, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  choose d hd using hd
  refine ⟨∑ i, d i • b i, ?_⟩
  conv_lhs => rw [← b.sum_repr z]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd i, mul_smul, Nat.cast_smul_eq_nsmul]

end GlobalTheory.LKGeo.LatDvd
