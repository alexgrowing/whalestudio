import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPointsGenericFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedFiniteFreePointsSeparateStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartSep

theorem eq_one_of_tangent_pow {R k : Type} [CommRing R] [CommRing k] [Algebra R k] {G : Over (Sp R)} [GrpObj G]
    {N : ℕ} (hN : IsUnit (N : k)) (y : ReciprocityTheory.ChartRestriction.G.Pdiv.specO R (DualNumber k) ⟶ G)
    (hy : ReciprocityTheory.ChartRestriction.G.Pdiv.ptMap (TrivSqZeroExt.fstHom R k k) ≫ y = 1) (hyN : y ^ N = 1) : y = 1 := by
  obtain ⟨u, hu⟩ := hN
  have h1 := GlobalTheory.TangentPow.pow_eq_scale_comp hy N
  rw [hyN] at h1
  have hs : GlobalTheory.TangentPow.scale R (↑u⁻¹ : k) ≫ GlobalTheory.TangentPow.scale R (N : k) = 𝟙 _ := by
    rw [← GlobalTheory.TangentPow.scale_one (O := R) (R := k), GlobalTheory.TangentPow.scale, GlobalTheory.TangentPow.scale,
      GlobalTheory.TangentPow.ptMap_comp_ptMap, GlobalTheory.TangentPow.scale]
    congr 1
    refine AlgHom.ext fun x => ?_
    have : (↑u⁻¹ : k) * ((N : k) * x.snd) = x.snd := by
      rw [← _root_.mul_assoc, ← hu, Units.inv_mul, _root_.one_mul]
    ext <;> simp [this]
  calc y = (GlobalTheory.TangentPow.scale R (↑u⁻¹ : k) ≫ GlobalTheory.TangentPow.scale R (N : k)) ≫ y := by rw [hs, Category.id_comp]
    _ = 1 := by rw [Category.assoc, ← h1, MonObj.comp_one]

end GlobalTheory.ChartSep

namespace GlobalTheory.ChartSep

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ} {q : PrimeSpectrum R}

theorem dual_eq_const (c : PreChart G N q) {k : Type} [CommRing k] [Algebra R k] (hN : IsUnit (N : k))
    (ψ : c.C →ₐ[R] DualNumber k) :
    ψ = ((TrivSqZeroExt.inlAlgHom R k k).comp (TrivSqZeroExt.fstHom R k k)).comp ψ := by
  set ψ' := ((TrivSqZeroExt.inlAlgHom R k k).comp (TrivSqZeroExt.fstHom R k k)).comp ψ
  have hf : (TrivSqZeroExt.fstHom R k k).comp ψ' = (TrivSqZeroExt.fstHom R k k).comp ψ := by
    ext a; simp [ψ']
  let z : Tors G N (DualNumber k) := torsMap ψ c.j * (torsMap ψ' c.j)⁻¹
  have hred : ReciprocityTheory.ChartRestriction.G.Pdiv.ptMap (TrivSqZeroExt.fstHom R k k) ≫ z.1 = 1 := by
    have e : ∀ φ : c.C →ₐ[R] DualNumber k, ReciprocityTheory.ChartRestriction.G.Pdiv.ptMap (TrivSqZeroExt.fstHom R k k) ≫ (torsMap φ c.j).1
        = spOver ((TrivSqZeroExt.fstHom R k k).comp φ) ≫ c.j.1 := fun φ => by
      rw [torsMap_val, ← Category.assoc, ← spOver_comp]; rfl
    show ReciprocityTheory.ChartRestriction.G.Pdiv.ptMap (TrivSqZeroExt.fstHom R k k) ≫ ((torsMap ψ c.j).1 * ((torsMap ψ' c.j).1)⁻¹) = 1
    rw [MonObj.comp_mul, GrpObj.comp_inv, e, e, hf, mul_inv_cancel]
  have hz : z = 1 := Subtype.ext (eq_one_of_tangent_pow hN z.1 hred z.2)
  have key : torsMap ψ c.j = torsMap ψ' c.j := mul_inv_eq_one.1 hz
  exact (c.bij (DualNumber k)).injOn trivial trivial key

end GlobalTheory.ChartSep

namespace GlobalTheory.ChartSep

theorem chart_finite_separating : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (q : PrimeSpectrum R) (c : PreChart G N q), Finite (c.C →ₐ[R] K) ∧ ∀ a : c.C, (∀ ψ : c.C →ₐ[R] K, ψ a = 0) → a = 0 := by
  intro R K _ _ _ _ _ _ _ _ G _ _ _ N hN q c
  have hr : c.r ≠ 0 := fun h => c.hr (h ▸ q.asIdeal.zero_mem)
  have hred : IsReduced c.C := GlobalTheory.T.dual_points_generic_finite R K c.r hr c.C fun k _ _ _ _ ψ => by
    refine dual_eq_const c ?_ ψ
    have h : IsUnit (N : K) := (Nat.cast_ne_zero.2 hN).isUnit
    simpa using h.map (algebraMap K k)
  exact GlobalTheory.T.reduced_finite_free_points_separate R K c.r hr c.C hred

end GlobalTheory.ChartSep
