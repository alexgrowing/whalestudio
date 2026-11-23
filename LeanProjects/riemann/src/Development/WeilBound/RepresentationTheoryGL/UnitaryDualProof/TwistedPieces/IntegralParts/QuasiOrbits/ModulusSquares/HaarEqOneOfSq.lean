import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.DetEqOfSurj
import GroundTheory.AutomorphicForms.GLnLocal

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.TP.Nil.Orb.Mod

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil.Orb.BModbound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def IsTau (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k) : Prop :=
  (∀ x ∈ Bz Z, ∀ y ∈ Bz Z, τ (x * y) = τ (y * x)) ∧ (∀ x ∈ Bz Z, (∀ y ∈ Bz Z, τ (x * y) = 0) → x = 0)

theorem mem_C_iff' (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (y : Matrix (Fin n) (Fin n) k) :
    y ∈ (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule ↔ y ∈ Bz Z := by
  show y ∈ Subalgebra.centralizer k _ ↔ _
  rw [Subalgebra.mem_centralizer_iff]
  rfl

theorem det_C_sq (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k)
    (hτ : IsTau Z τ) (g : GL (Fin n) k) (hg : g ∈ Gz Z) :
    LinearMap.det ((adL g).restrict (cC_inv Z g hg)) ^ 2 = 1 := by
  classical
  have memB : ∀ x : (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule,
      (x : Matrix (Fin n) (Fin n) k) ∈ Bz Z := fun x => (mem_C_iff' Z x).1 x.2
  have mulB : ∀ x y : Matrix (Fin n) (Fin n) k, x ∈ Bz Z → y ∈ Bz Z → x * y ∈ Bz Z :=
    fun x y hx hy => (mem_C_iff' Z _).1
      (Subalgebra.mul_mem _ ((mem_C_iff' Z x).2 hx) ((mem_C_iff' Z y).2 hy))
  have hgB : ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ Bz Z := fun a ha => hg a ha
  have hgB' : ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ Bz Z := fun a ha => by
    have e := hg a ha
    calc a * ↑g⁻¹ = (↑g⁻¹ * ↑g) * a * ↑g⁻¹ := by rw [Units.inv_mul, one_mul]
      _ = ↑g⁻¹ * (↑g * a) * ↑g⁻¹ := by simp only [mul_assoc]
      _ = ↑g⁻¹ * (a * ↑g) * ↑g⁻¹ := by rw [e]
      _ = ↑g⁻¹ * a * (↑g * ↑g⁻¹) := by simp only [mul_assoc]
      _ = ↑g⁻¹ * a := by rw [Units.mul_inv, mul_one]
  let ψ : (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule →ₗ[k]
      Module.Dual k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule :=
    LinearMap.mk₂ k (fun x y => τ ((x : Matrix (Fin n) (Fin n) k) * (y : Matrix (Fin n) (Fin n) k)))
      (fun x x' y => by simp [add_mul]) (fun c x y => by simp [smul_mul_assoc])
      (fun x y y' => by simp [mul_add]) (fun c x y => by simp [mul_smul_comm])
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : ∀ y ∈ Bz Z, τ ((x : Matrix (Fin n) (Fin n) k) * y) = 0 := fun y hy => by
      have := LinearMap.congr_fun hx ⟨y, (mem_C_iff' Z y).2 hy⟩
      simpa [ψ] using this
    exact Subtype.ext (hτ.2 _ (memB x) h0)
  have hψs : Function.Surjective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hψ
  let e := LinearEquiv.ofBijective ψ ⟨hψ, hψs⟩
  have hpres : ((adL g).restrict (cC_inv Z g hg)).dualMap ∘ₗ ψ ∘ₗ (adL g).restrict (cC_inv Z g hg)
      = ψ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change τ (((g : Matrix (Fin n) (Fin n) k) * ((x : Matrix (Fin n) (Fin n) k) *
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) *
        ((g : Matrix (Fin n) (Fin n) k) * ((y : Matrix (Fin n) (Fin n) k) *
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)))) =
      τ ((x : Matrix (Fin n) (Fin n) k) * (y : Matrix (Fin n) (Fin n) k))
    have hxy : ((g : Matrix (Fin n) (Fin n) k) * ((x : Matrix (Fin n) (Fin n) k) *
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) *
        ((g : Matrix (Fin n) (Fin n) k) * ((y : Matrix (Fin n) (Fin n) k) *
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) =
        (g : Matrix (Fin n) (Fin n) k) *
          ((x : Matrix (Fin n) (Fin n) k) * (y : Matrix (Fin n) (Fin n) k) *
            ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) := by
      simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [hxy, hτ.1 _ hgB _ (mulB _ _ (mulB _ _ (memB x) (memB y)) hgB')]
    simp only [mul_assoc, Units.inv_mul, mul_one]
  have h1 : (e.symm.toLinearMap ∘ₗ ((adL g).restrict (cC_inv Z g hg)).dualMap ∘ₗ e.toLinearMap) ∘ₗ
      (adL g).restrict (cC_inv Z g hg) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hpres x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearEquiv.coe_coe] at hx ⊢
    rw [LinearEquiv.symm_apply_eq]
    exact hx
  have h2 := congrArg LinearMap.det h1
  have hc := LinearMap.det_conj ((adL g).restrict (cC_inv Z g hg)).dualMap e.symm
  rw [LinearEquiv.symm_symm] at hc
  rw [LinearMap.det_comp, LinearMap.det_id, hc, LinearMap.det_dualMap] at h2
  rw [sq]
  exact h2

theorem haar_eq_one_of_sq (u : kˣ) (hu : u ^ 2 = 1) : MeasureTheory.distribHaarChar k u = 1 := by
  have h := congrArg (MeasureTheory.distribHaarChar k) hu
  rw [map_pow, map_one] at h
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h

theorem infinite_local : Infinite k := by
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hs : StrictAnti (fun m : ℕ => valuation k r ^ m) :=
    pow_right_strictAnti₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hr0)) hr1
  exact Infinite.of_injective (fun m : ℕ => r ^ m)
    (fun a b hab => hs.injective (by simp only [← map_pow, hab]))

end PositivityTheory.RgUd.TP.Nil.Orb.Mod
