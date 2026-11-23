import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.FilZeroEqRangeCDAndCDInjective
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsPrimePowSmulMemLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem span_abs {Q Z O D B V κ : Type} [CommRing Q] [CommRing Z] [CommRing O] [CommRing D]
    [CommRing B] [Algebra Z O] [Algebra Z D] [Algebra Q B] [AddCommGroup V] [Module Q V] [Module O V]
    [Fintype κ] (T : Submodule O V) (b : Module.Basis κ O T) (F : Submodule Q B) (c : D →+* B)
    (act : O ⊗[Z] D →+ (V ⊗[Q] B →+ V ⊗[Q] B))
    (hact : ∀ (o : O) (d : D) (v : V) (e : B),
      act (o ⊗ₜ[Z] d) (v ⊗ₜ[Q] e) = (o • v) ⊗ₜ[Q] (c d * e))
    (hF : ∀ x ∈ F, ∃ y, x = c y)
    (hT : ∀ (v : V) (y : D), ∃ (q : Q) (x : T) (y1 : D), (x : V) = q • v ∧ c y = q • c y1)
    (f : V ⊗[Q] F →+ V ⊗[Q] B) (hf : ∀ (v : V) (x : F), f (v ⊗ₜ[Q] x) = v ⊗ₜ[Q] (x : B))
    (y : V ⊗[Q] F) :
    ∃ d : κ → O ⊗[Z] D, f y = ∑ k, act (d k) (((b k : T) : V) ⊗ₜ[Q] (1 : B)) := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add a a' ha ha' =>
    obtain ⟨d, hd⟩ := ha
    obtain ⟨d', hd'⟩ := ha'
    refine ⟨d + d', ?_⟩
    rw [map_add, hd, hd', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.add_apply, map_add, AddMonoidHom.add_apply]
  | tmul v x =>
    obtain ⟨y0, hy0⟩ := hF x x.2
    obtain ⟨q, t, y1, ht, hy⟩ := hT v y0
    refine ⟨fun k => b.repr t k ⊗ₜ[Z] y1, ?_⟩
    have h1 : (t : V) = ∑ k, b.repr t k • ((b k : T) : V) := by
      have h2 := congrArg T.subtype (b.sum_repr t).symm
      rw [map_sum] at h2
      simpa only [map_smul, Submodule.subtype_apply] using h2
    rw [hf, hy0, hy, ← TensorProduct.smul_tmul, ← ht, h1, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hact, mul_one]

theorem _root_.UpperTheory.KN.exists_BdRPlus_coeffs_of_mem_filZero_deRham :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (κ : Type) [Fintype κ] (b : Module.Basis κ ↥(OL LL) ↥T.L.T), ∀ v : T.V ⊗[ℚ_[l]] Pl.R.BdR, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) → ∃ d : κ → OD l ↥(OL LL), v = ∑ k, act (d k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) := by
  intro l _ LL T Pl AI Td act hact κ _ b v hv
  obtain ⟨y, rfl⟩ := hv
  refine span_abs (Q := ℚ_[l]) (Z := ℤ_[l]) T.L.T b
    (((Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).Fil 0).restrictScalars ℚ_[l]) (GlobalTheory.BKGal.JumpDR.cD Td) act
    ?_ ?_ ?_ (AlgebraTensorModule.map (LinearMap.id : T.V →ₗ[↥LL.1] T.V)
      (((Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).Fil 0).restrictScalars ℚ_[l]).subtype).toAddMonoidHom ?_ y
  · intro o d v e
    refine (hact o d v e).trans ?_
    congr 1
    first | done | rfl | exact (algebraMap_smul (↥LL.1) o v)
  · intro x hx
    exact ((UpperTheory.KN.fil_zero_eq_range_cD_and_cD_injective l Pl AI Td (Formalism.MainNotions.ElementDenominator.qlExt l)).1 x).1 hx
  · intro v y
    obtain ⟨n, x, hx⟩ := UpperTheory.KN.exists_prime_pow_smul_mem_lattice l LL T v
    obtain ⟨z, hz⟩ := ((GlobalTheory.MemLoc.isUnit_l_BdRp l).pow n).exists_right_inv
    refine ⟨(l : ℚ_[l]) ^ n, x, z * y, hx, ?_⟩
    have h : y = ((l : ℕ) : Per.BdRp l) ^ n * (z * y) := by rw [← mul_assoc, hz, one_mul]
    conv_lhs => rw [h]
    rw [map_mul, map_pow, map_natCast, Algebra.smul_def, map_pow, map_natCast]
  · intro v x
    rfl
