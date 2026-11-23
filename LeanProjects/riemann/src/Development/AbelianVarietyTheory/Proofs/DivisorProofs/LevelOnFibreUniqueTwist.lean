import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliWithSymplecticLevelRepresentab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLevelFamily
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.UPel.TensorTorsionNsmul

open scoped TensorProduct

variable {L : Type} [AddCommGroup L]

theorem tmul_surjective (n : ℕ) (x : ZMod n ⊗[ℤ] L) : ∃ a : L, (1 : ZMod n) ⊗ₜ[ℤ] a = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul r a =>
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective r
    refine ⟨m • a, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul, _root_.mul_one]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, TensorProduct.tmul_add _ _ _⟩

theorem eq_nsmul_of_tmul_eq_zero {n : ℕ} {a : L} (h : (1 : ZMod n) ⊗ₜ[ℤ] a = 0) : ∃ d, a = n • d := by
  let e : ZMod n ≃ₗ[ℤ] (ℤ ⧸ Ideal.span {(n : ℤ)}) :=
    (Int.quotientSpanNatEquivZMod n).symm.toAddEquiv.toIntLinearEquiv
  have he : e 1 = 1 := map_one (Int.quotientSpanNatEquivZMod n).symm
  have h1 := congrArg (fun y => TensorProduct.quotTensorEquivQuotSMul L (Ideal.span {(n : ℤ)})
    (LinearMap.rTensor L e.toLinearMap y)) h
  simp only [LinearMap.rTensor_tmul, map_zero, LinearEquiv.coe_coe, he,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h1
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨d, -, hd⟩ := h1
  exact ⟨d, by rw [← hd, natCast_zsmul]⟩

theorem tmul_nsmul_eq_zero (n : ℕ) (d : L) : (1 : ZMod n) ⊗ₜ[ℤ] (n • d) = 0 := by
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', nsmul_eq_mul, _root_.mul_one, ZMod.natCast_self,
    TensorProduct.zero_tmul]

variable {G : Type} [Group G]

theorem map_nsmul_of_add {φ : L → G} (hφ : ∀ a c, φ (a + c) = φ a * φ c) (m : ℕ) (a : L) :
    φ (m • a) = φ a ^ m := by
  have h0 : φ 0 = 1 := by
    have := hφ 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction m with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ m ih => rw [succ_nsmul, hφ, ih, pow_succ]

theorem tmul_eq_tmul_iff {n : ℕ} {φ : L → G} (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b) (a c : L) :
    (1 : ZMod n) ⊗ₜ[ℤ] a = 1 ⊗ₜ c ↔ φ a = φ c := by
  have e : φ a = φ (a - c) * φ c := by rw [← hφ, sub_add_cancel]
  rw [e, mul_eq_right, hk, ← sub_eq_zero, ← TensorProduct.tmul_sub]
  constructor
  · exact eq_nsmul_of_tmul_eq_zero
  · rintro ⟨d, hd⟩
    rw [hd]
    exact tmul_nsmul_eq_zero n d

def matchMap (n : ℕ) (φ φ' : L → G) (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c) (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b)
    (hr : ∀ b, ∃ c, φ c = φ' b) : (ZMod n ⊗[ℤ] L) →ₗ[ZMod n] (ZMod n ⊗[ℤ] L) :=
  LinearMap.liftBaseChange (ZMod n)
    (AddMonoidHom.mk' (fun b => (1 : ZMod n) ⊗ₜ[ℤ] Classical.choose (hr b)) (fun b b' => by
      rw [← TensorProduct.tmul_add, tmul_eq_tmul_iff hφ hk, hφ, Classical.choose_spec (hr _),
        Classical.choose_spec (hr _), Classical.choose_spec (hr _), hφ']) : L →+ ZMod n ⊗[ℤ] L).toIntLinearMap

theorem matchMap_tmul (n : ℕ) (φ φ' : L → G) (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c) (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b)
    (hr : ∀ b, ∃ c, φ c = φ' b) (b c : L) :
    matchMap n φ φ' hφ hφ' hk hr ((1 : ZMod n) ⊗ₜ b) = 1 ⊗ₜ c ↔ φ c = φ' b := by
  rw [matchMap, LinearMap.liftBaseChange_tmul, one_smul]
  change (1 : ZMod n) ⊗ₜ[ℤ] Classical.choose (hr b) = _ ↔ _
  rw [tmul_eq_tmul_iff hφ hk, Classical.choose_spec (hr b), eq_comm]

theorem exists_equiv (n : ℕ) (φ φ' : L → G) (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c) (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b)
    (hk' : ∀ a, φ' a = 1 ↔ ∃ b, a = n • b) (hr : ∀ b, ∃ c, φ c = φ' b) (hr' : ∀ c, ∃ b, φ' b = φ c) :
    ∃ e : (ZMod n ⊗[ℤ] L) ≃ₗ[ZMod n] (ZMod n ⊗[ℤ] L), ∀ b c, e (1 ⊗ₜ b) = 1 ⊗ₜ c ↔ φ c = φ' b := by
  let f := matchMap n φ φ' hφ hφ' hk hr
  let g := matchMap n φ' φ hφ' hφ hk' hr'
  have hfg : ∀ x, g (f x) = x := by
    intro x
    obtain ⟨b, rfl⟩ := tmul_surjective n x
    obtain ⟨c, hc⟩ := hr b
    obtain ⟨d, hd⟩ := hr' c
    rw [(matchMap_tmul n φ φ' hφ hφ' hk hr b c).2 hc, (matchMap_tmul n φ' φ hφ' hφ hk' hr' c d).2 hd,
      tmul_eq_tmul_iff hφ' hk', hd, hc]
  have hgf : ∀ x, f (g x) = x := by
    intro x
    obtain ⟨b, rfl⟩ := tmul_surjective n x
    obtain ⟨c, hc⟩ := hr' b
    obtain ⟨d, hd⟩ := hr c
    rw [(matchMap_tmul n φ' φ hφ' hφ hk' hr' b c).2 hc, (matchMap_tmul n φ φ' hφ hφ' hk hr c d).2 hd,
      tmul_eq_tmul_iff hφ hk, hd, hc]
  refine ⟨LinearEquiv.ofLinear f g (LinearMap.ext hgf) (LinearMap.ext hfg), fun b c => ?_⟩
  exact matchMap_tmul n φ φ' hφ hφ' hk hr b c

end GlobalTheory.UPel.TensorTorsionNsmul

namespace GlobalTheory.UPel

open scoped TensorProduct

end GlobalTheory.UPel
