import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedDualRegularFormsFiniteCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosureProperties
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem ext_comm_one {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (v : M) (q : ℕ)
    (w : ExteriorAlgebra R M) (hw : w ∈ ⋀[R]^q M) :
    ExteriorAlgebra.ι R v * w = ((-1 : ℤ) ^ q) • (w * ExteriorAlgebra.ι R v) := by
  induction hw using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [Algebra.commutes]
  | add x y i _ _ hx hy => rw [mul_add, add_mul, hx, hy, smul_add]
  | mem_mul m hm i x _ hx =>
    obtain ⟨u, rfl⟩ := hm
    have h := ExteriorAlgebra.ι_add_mul_swap (R := R) v u
    have h' : ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u = -(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) :=
      eq_neg_of_add_eq_zero_left h
    rw [← mul_assoc, h', neg_mul, mul_assoc, hx, mul_smul_comm]
    simp only [pow_succ, mul_neg, mul_one, neg_smul, mul_assoc]

private theorem ext_comm {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (p q : ℕ)
    (y w : ExteriorAlgebra R M) (hy : y ∈ ⋀[R]^p M) (hw : w ∈ ⋀[R]^q M) :
    y * w = ((-1 : ℤ) ^ (p * q)) • (w * y) := by
  induction hy using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [Algebra.commutes]
  | add x y i _ _ hx hy => rw [add_mul, mul_add, hx, hy, smul_add]
  | mem_mul m hm i x _ hx =>
    obtain ⟨u, rfl⟩ := hm
    rw [mul_assoc, hx, mul_smul_comm, ← mul_assoc, ext_comm_one u q w hw, smul_mul_assoc, smul_smul,
      mul_assoc, Nat.succ_mul, pow_add]

theorem UpperTheory.Gal.productCup_of_system.idJ_of :
    LatOm → LatA → DualForm → IdJ := by
  intro hOm hA hD F K _ _ _ _ _ _ d x hc τ hτ a ha j
  obtain ⟨⟨_, n, v, φ, hv, hφ, hdec⟩, hsp⟩ := hOm F K d x hc a {j} (by simp)
  have hdec' : ∀ z ∈ Submodule.span F (omB ℂ K (rB ℂ K (xv x) {j}) a : Set (DR ℂ K)), z = ∑ k, φ k z • v k := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact hdec z hz
    | zero => simp
    | add p q _ _ hp hq =>
      simp only [map_add, add_smul, Finset.sum_add_distrib]
      rw [← hp, ← hq]
    | smul c p _ hp =>
      simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
      rw [← hp]
  have hG : omG x j ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun l _ => div_ne_zero (x l).ne_zero (x j).ne_zero
  choose w hwm hwt using fun k => (hD F K d x hc τ hτ a ha (omG x j • φ k)).2
  have hwB : ∀ k, w k ∈ omB ℂ K (rB ℂ K (xv x) {j}) (d - a) := by
    intro k
    refine (GlobalTheory.T.twistedDual_regularForms_finiteCover ℂ F K d (xv x) hc τ hτ {j} (by simp) a (d - a) (by omega) (w k) (hwm k)).1 ?_
    intro y hy
    have hy' : y ∈ ⋀[K]^a Ω[K⁄ℂ] := GlobalTheory.PD.mem_deg_of_mem_omB _ _ _ hy
    rw [ext_comm a (d - a) y (w k) hy' (hwm k), map_zsmul, map_zsmul]
    refine zsmul_mem ?_ _
    rw [← hwt k y hy']
    refine ((hA F d x hc.pd {j} j (by simp)).2.1 _).2 ?_
    simpa [hG] using hφ k y hy
  refine ⟨∑ k, w k ⊗ₜ[ℂ] v k, ?_, ?_⟩
  · show _ ∈ MZ F K (xv x) a {j} {j}
    exact Submodule.sum_mem _ fun k _ => Submodule.apply_mem_map₂ _ (hwB k) (hv k)
  · intro y hy
    conv_rhs => rw [hdec' y (hsp y hy)]
    simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : muP F K τ (w k ⊗ₜ[ℂ] v k) y = (Algebra.trace F K (τ (w k * y))) ⊗ₜ[ℂ] v k := by
      simp [muP]
    rw [this, ← hwt k y hy]
    simp [mulP]
