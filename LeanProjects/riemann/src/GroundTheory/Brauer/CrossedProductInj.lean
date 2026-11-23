import Mathlib
import GroundTheory.Brauer.CrossedProduct
import GroundTheory.Brauer.CrossedProductSimple
import GroundTheory.Brauer.CrossedProductMaps
import GroundTheory.Brauer.SkolemNoether
import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv
import GroundTheory.Brauer.MulDistribMulActionQuotientFixedPoints
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open groupCohomology

universe u v

namespace CrossedProduct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} {hf : IsMulCocycle₂ f}

theorem eq_single_of_mul_incl (σ : L ≃ₐ[K] L) (x : CrossedProduct hf)
    (hx : ∀ b : L, x * incl b = incl (σ b) * x) : x = single σ (x.coeff σ) := by
  have hzero : ∀ τ, τ ≠ σ → x.coeff τ = 0 := by
    intro τ hτ
    obtain ⟨b, hb⟩ : ∃ b, σ b ≠ τ b := by
      by_contra h
      push Not at h
      exact hτ (AlgEquiv.ext fun b => (h b).symm)
    have h : (incl (σ b) * x - x * incl b).coeff τ = 0 := by
      rw [hx b, sub_self]
      rfl
    rw [coeff_incl_mul_sub_mul_incl] at h
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hb)
  rw [← incl_mul_u]
  exact eq_incl_mul_u_of_coeff_eq_zero x σ hzero

variable [FiniteDimensional K L] [IsGalois K L]

theorem isMulCoboundary₂_div_of_algEquiv {g : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
    (hf : IsMulCocycle₂ f) (hg : IsMulCocycle₂ g) (e : CrossedProduct hf ≃ₐ[K] CrossedProduct hg) :
    IsMulCoboundary₂ (f / g) := by
  obtain ⟨a, ha⟩ := exists_unit_conj
    ((e : CrossedProduct hf →ₐ[K] CrossedProduct hg).comp incl) (incl : L →ₐ[K] CrossedProduct hg)

  set φ : CrossedProduct hf → CrossedProduct hg := fun y => (a : CrossedProduct hg) * e y * ↑a⁻¹
    with hφ
  have φmul : ∀ y z, φ (y * z) = φ y * φ z := by
    intro y z
    simp only [hφ, map_mul, mul_assoc, Units.inv_mul_cancel_left]
  have φone : φ 1 = 1 := by
    simp only [hφ, map_one, mul_one, Units.mul_inv]
  have φincl : ∀ b, φ (incl b) = incl b := fun b => (ha b).symm
  obtain ⟨c, hw⟩ : ∃ c : (L ≃ₐ[K] L) → L, ∀ σ, φ (u σ) = single σ (c σ) :=
    ⟨fun σ => (φ (u σ)).coeff σ, fun σ =>
      eq_single_of_mul_incl σ _ fun b => by rw [← φincl, ← φmul, u_mul_incl, φmul, φincl]⟩
  have hc0 : ∀ σ, c σ ≠ 0 := by
    intro σ h0
    obtain ⟨w, hw'⟩ := (isUnit_u σ (hf := hf)).exists_right_inv
    have h := congrArg φ hw'
    rw [φmul, φone, hw σ, h0, single_zero, zero_mul] at h
    exact zero_ne_one h
  have key : ∀ σ τ, c σ * σ (c τ) * g (σ, τ) = f (σ, τ) * c (σ * τ) := by
    intro σ τ
    have h := congrArg φ (u_mul_u (hf := hf) σ τ)
    simp only [φmul, φincl] at h
    rw [hw σ, hw τ, hw (σ * τ), single_mul_single, incl_mul_single] at h
    exact single_injective _ h
  refine ⟨fun σ => Units.mk0 (c σ) (hc0 σ), fun σ τ => ?_⟩
  ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, val_smul_units, Units.val_mk0, Pi.div_apply]
  rw [div_mul_eq_mul_div, div_eq_div_iff (hc0 _) (g (σ, τ)).ne_zero]
  linear_combination key σ τ

theorem isMulCoboundary₂_of_algEquiv_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hf : IsMulCocycle₂ f) (e : CrossedProduct hf ≃ₐ[K] Matrix ι ι K) : IsMulCoboundary₂ f := by
  have hcard : Fintype.card ι = Module.finrank K L := by
    have h1 := e.toLinearEquiv.finrank_eq
    rw [finrank_eq_sq, Module.finrank_matrix, Module.finrank_self, mul_one, ← sq] at h1
    exact (Nat.pow_left_injective two_ne_zero h1).symm
  have h := isMulCoboundary₂_div_of_algEquiv hf isMulCocycle₂_one
    (e.trans ((Matrix.reindexAlgEquiv K K (Fintype.equivFinOfCardEq hcard)).trans
      (matrixEquiv isMulCocycle₂_one).symm))
  rwa [div_one] at h

end CrossedProduct

theorem nonempty_algEquiv_of_isBrauerEquivalent {K : Type u} [Field K] {A B : CSA.{u, v} K}
    (h : IsBrauerEquivalent A B) (hd : Module.finrank K A = Module.finrank K B) :
    Nonempty (A ≃ₐ[K] B) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  obtain ⟨n, hn, D, _, _, _, ⟨eA⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  obtain ⟨m, hm, D', _, _, _, ⟨eB⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K B
  obtain ⟨φ⟩ := (isBrauerEquivalent_iff_nonempty_algEquiv eA eB).1 h
  have hdA := eA.toLinearEquiv.finrank_eq
  have hdB := eB.toLinearEquiv.finrank_eq
  rw [Module.finrank_matrix, Fintype.card_fin] at hdA hdB
  have hDD : Module.finrank K D = Module.finrank K D' := φ.toLinearEquiv.finrank_eq
  have hD0 : 0 < Module.finrank K D := Module.finrank_pos
  obtain rfl : n = m := by
    rw [hdA, hdB, ← hDD] at hd
    exact Nat.mul_self_inj.1 (Nat.eq_of_mul_eq_mul_right hD0 hd)
  exact ⟨eA.trans (φ.mapMatrix.trans eB.symm)⟩

namespace CrossedProduct

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}

theorem isBrauerEquivalent_one_one :
    IsBrauerEquivalent (csaOf K (CrossedProduct (isMulCocycle₂_one (K := K) (L := L))))
      (oneCSA K) := by
  have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  exact isBrauerEquivalent_of_algEquiv_matrix (C := K) (matrixEquiv isMulCocycle₂_one)
    (matrixFinOneAlgEquiv K).symm

theorem nonempty_algEquiv_of_isBrauerEquivalent {g : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
    (hf : IsMulCocycle₂ f) (hg : IsMulCocycle₂ g)
    (h : IsBrauerEquivalent (csaOf K (CrossedProduct hf)) (csaOf K (CrossedProduct hg))) :
    Nonempty (CrossedProduct hf ≃ₐ[K] CrossedProduct hg) :=
  GroundTheory.Brauer.nonempty_algEquiv_of_isBrauerEquivalent h
    (show Module.finrank K (CrossedProduct hf) = Module.finrank K (CrossedProduct hg) by
      rw [finrank_eq_sq, finrank_eq_sq])

theorem isMulCoboundary₂_of_isBrauerEquivalent_one (hf : IsMulCocycle₂ f)
    (h : IsBrauerEquivalent (csaOf K (CrossedProduct hf)) (oneCSA K)) : IsMulCoboundary₂ f := by
  obtain ⟨e⟩ := nonempty_algEquiv_of_isBrauerEquivalent hf isMulCocycle₂_one
    (h.trans (isBrauerEquivalent_one_one (L := L)).symm)
  have h' := isMulCoboundary₂_div_of_algEquiv hf isMulCocycle₂_one e
  rwa [div_one] at h'

theorem isMulCoboundary₂_of_mk_eq_one (hf : IsMulCocycle₂ f)
    (h : (⟦csaOf K (CrossedProduct hf)⟧ : BrauerGroup.{u, u} K) = 1) : IsMulCoboundary₂ f :=
  isMulCoboundary₂_of_isBrauerEquivalent_one hf (Quotient.exact (h.trans BrauerGroup.one_def))

theorem mk_eq_one_of_isMulCoboundary₂ (hf : IsMulCocycle₂ f) (h : IsMulCoboundary₂ f) :
    (⟦csaOf K (CrossedProduct hf)⟧ : BrauerGroup.{u, u} K) = 1 := by
  rw [BrauerGroup.one_def]
  refine Quotient.sound (IsBrauerEquivalent.trans ?_ (isBrauerEquivalent_one_one (L := L)))
  refine isBrauerEquivalent_of_algEquiv
    (A := csaOf K (CrossedProduct hf)) (B := csaOf K (CrossedProduct (isMulCocycle₂_one (K := K)
      (L := L)))) (equivOfIsMulCoboundary₂ hf isMulCocycle₂_one ?_)
  rw [one_div]
  exact isMulCoboundary₂_inv h

end CrossedProduct

theorem isMulCocycle₂_of_mem {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (c : mulCocycles₂ G M) : IsMulCocycle₂ (c : G × G → M) := c.2

namespace H2mul

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

def toBrauer : H2mul (L ≃ₐ[K] L) Lˣ → BrauerGroup.{u, u} K :=
  Quotient.lift (fun c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ => ⟦csaOf K (CrossedProduct (isMulCocycle₂_of_mem c))⟧)
    (fun c c' h => by
      have h' : mk _ _ c = mk _ _ c' := Quotient.sound h
      rw [mk_eq_mk_iff] at h'
      exact Quotient.sound (isBrauerEquivalent_of_algEquiv
        (A := csaOf K (CrossedProduct (isMulCocycle₂_of_mem c))) (B := csaOf K (CrossedProduct (isMulCocycle₂_of_mem c')))
        (CrossedProduct.equivOfIsMulCoboundary₂ (isMulCocycle₂_of_mem c') (isMulCocycle₂_of_mem c) h').symm))

variable {K L}

@[simp]
theorem toBrauer_mk (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    toBrauer K L (mk _ _ c) = ⟦csaOf K (CrossedProduct (isMulCocycle₂_of_mem c))⟧ := rfl

theorem toBrauer_injective : Function.Injective (toBrauer K L) := by
  intro x y hxy
  induction x using H2mul.induction_on with
  | h c =>
  induction y using H2mul.induction_on with
  | h c' =>
  rw [toBrauer_mk, toBrauer_mk] at hxy
  obtain ⟨e⟩ := CrossedProduct.nonempty_algEquiv_of_isBrauerEquivalent
    (isMulCocycle₂_of_mem c) (isMulCocycle₂_of_mem c') (Quotient.exact hxy)
  exact (mk_eq_mk_iff c c').2 (CrossedProduct.isMulCoboundary₂_div_of_algEquiv _ _ e)

theorem toBrauer_eq_one_iff (x : H2mul (L ≃ₐ[K] L) Lˣ) : toBrauer K L x = 1 ↔ x = 1 := by
  induction x using H2mul.induction_on with
  | h c =>
  rw [toBrauer_mk, mk_eq_one_iff]
  exact ⟨CrossedProduct.isMulCoboundary₂_of_mk_eq_one (isMulCocycle₂_of_mem c),
    CrossedProduct.mk_eq_one_of_isMulCoboundary₂ (isMulCocycle₂_of_mem c)⟩

theorem toBrauer_one : toBrauer K L (1 : H2mul (L ≃ₐ[K] L) Lˣ) = 1 :=
  (toBrauer_eq_one_iff _).2 rfl

end H2mul

end GroundTheory.Brauer

end
