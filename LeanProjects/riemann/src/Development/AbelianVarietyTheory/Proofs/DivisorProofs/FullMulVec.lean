import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharEntireNeZeroAutomorphy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl.TwistExp

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X}

theorem full_mulVec (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    d.full σ S *ᵥ x = d.full σ 0 *ᵥ x + fun i => Sum.elim (0 : Fin g' → ℂ) (S *ᵥ tP σ x) (σ i) := by
  ext i
  simp only [CD.full, Matrix.submatrix_mulVec_equiv, Function.comp_apply, Pi.add_apply, Matrix.fromBlocks_mulVec]
  rcases h : σ i with j | j
  · simp [tP]
  · simp [tP, Matrix.add_mulVec, add_assoc]
    rfl

theorem leftComponent_fullMatrix_mulVec (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    zP σ (d.full σ S *ᵥ x) = zP σ (d.full σ 0 *ᵥ x) := by
  rw [full_mulVec]; ext i; simp [zP]

theorem secondBlock_full_mulVec (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    tP σ (d.full σ S *ᵥ x) = tP σ (d.full σ 0 *ᵥ x) + S *ᵥ tP σ x := by
  rw [full_mulVec]; ext i; simp [tP]

theorem dot_full (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    x ⬝ᵥ d.full σ S *ᵥ x = x ⬝ᵥ d.full σ 0 *ᵥ x + tP σ x ⬝ᵥ S *ᵥ tP σ x := by
  rw [full_mulVec, dotProduct_add]
  congr 1
  simp only [dotProduct]
  rw [← σ.symm.sum_comp, Fintype.sum_sum_type]
  simp [tP]

theorem co_form {k : ℕ} (β : N.Form k) (x y : N.X) :
    co bX x ⬝ᵥ bmat bX β *ᵥ co bX y = (β.be x y : ℂ) := by
  conv_rhs => rw [← bX.sum_repr x, ← bX.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec, co, bmat,
    Matrix.of_apply, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  ring

theorem co_sum (σ : Fin g ≃ Fin g' ⊕ Fin r) (Nn : Fin g → ℤ) :
    co bX (∑ l, tP σ Nn l • bX l) = tP σ (cv Nn) := by
  ext l; simp [co, tP, cv, Finsupp.single_apply]

end GlobalTheory.MBLow.Cl.TwistExp

namespace GlobalTheory.MBLow.Cl.TwistExp
open GlobalTheory.MBLow.Cl.TwistExp

theorem main_eq {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) (k m : ℕ) (β : N.Form k) (hm : 1 ≤ m) (hk : m ^ 2 ∣ k) (w : ℂ) (M Nn : Fin g → ℤ)
    (χ : N.X) (Z : Fin g → ℂ) :
    d.term σ (w • bmat bX β) m M Nn χ Z = d.term σ 0 m M Nn χ Z * Complex.exp ((2 * Real.pi * Complex.I : ℂ) * w) ^
      (β.be ((∑ l, tP σ Nn l • bX l) + m • χ) ((∑ l, tP σ Nn l • bX l) + m • χ) / (2 * m ^ 2)).toNat := by
  set S := w • bmat bX β with hS
  have hz : ∀ S' : Matrix (Fin r) (Fin r) ℂ, zP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ S') M Nn) =
      zP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ 0) M Nn) := fun S' => by
    ext i
    have := congrFun (leftComponent_fullMatrix_mulVec d σ S' (cv Nn)) i
    simp only [zP, perV, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]
  have ht : tP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ S) M Nn) =
      tP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ 0) M Nn) + (m:ℂ)⁻¹ • (S *ᵥ tP σ (cv Nn)) := by
    ext i
    have := congrFun (secondBlock_full_mulVec d σ S (cv Nn)) i
    simp only [tP, perV, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]; ring
  unfold CD.term trFac CD.fj
  rw [hz S, ht, dot_full d σ S (cv Nn)]

  set y : N.X := ∑ l, tP σ Nn l • bX l with hy
  have hn : tP σ (cv Nn) = co bX y := (co_sum σ Nn).symm
  have hSv : ∀ u v : Fin r → ℂ, ∀ x x' : N.X, u = co bX x → v = co bX x' → u ⬝ᵥ S *ᵥ v = w * (β.be x x' : ℂ) := by
    intro u v x x' hu hv
    rw [hS, Matrix.smul_mulVec, dotProduct_smul, hu, hv, co_form, smul_eq_mul]
  have h1 := hSv _ _ y y hn hn
  have h2 := hSv _ _ χ χ rfl rfl
  have h3 := hSv _ _ χ y rfl hn
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hsymm : β.be y χ = β.be χ y := β.symm y χ
  have hα : β.be (y + m • χ) (y + m • χ) = β.be y y + 2 * m * β.be χ y + m ^ 2 * β.be χ χ := by
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hsymm]; ring
  have hdvd : (2 * m ^ 2 : ℤ) ∣ β.be (y + m • χ) (y + m • χ) :=
    (mul_dvd_mul_left 2 (by exact_mod_cast hk)).trans (β.dvd _ _)
  have hnn : 0 ≤ β.be (y + m • χ) (y + m • χ) := by
    by_cases h0 : y + m • χ = 0
    · rw [h0]; simp
    · exact (β.pos _ h0).le
  have hK : (((β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2)).toNat : ℕ) : ℂ) =
      ((β.be y y : ℂ) + 2 * m * β.be χ y + m ^ 2 * β.be χ χ) / (2 * m ^ 2) := by
    obtain ⟨q, hq⟩ := hdvd
    have hm2 : (2 * m ^ 2 : ℤ) ≠ 0 := by positivity
    have hq0 : 0 ≤ q := by
      rw [hq] at hnn
      have hp : (0:ℤ) < 2 * m ^ 2 := by positivity
      by_contra hc; push_neg at hc
      have := mul_neg_of_pos_of_neg hp hc; linarith
    rw [hq, Int.mul_ediv_cancel_left _ hm2]
    have : ((q.toNat : ℕ) : ℂ) = (q : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hq0
    rw [this, eq_div_iff (by simpa using hm0)]
    have hc : ((β.be (y + m • χ) (y + m • χ) : ℤ) : ℂ) = ((2 * m ^ 2 * q : ℤ) : ℂ) := by rw [hq]
    rw [hα] at hc; push_cast at hc; linear_combination -hc
  have key : ∀ a b a' b' f t : ℂ, a + b = a' + b' + f →
      Complex.exp a * (Complex.exp b * t) = Complex.exp a' * (Complex.exp b' * t) * Complex.exp f := by
    intro a b a' b' f t h
    have : Complex.exp a * Complex.exp b = Complex.exp a' * Complex.exp b' * Complex.exp f := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, h]
    linear_combination t * this
  rw [← Complex.exp_nat_mul]
  refine key _ _ _ _ _ _ ?_
  simp only [Matrix.add_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, add_zero, Matrix.zero_mulVec,
    dotProduct_zero, h1, h2, h3, hK]
  field_simp
  ring

end GlobalTheory.MBLow.Cl.TwistExp

namespace GlobalTheory.MBLow.Cl.TwistExp

theorem term_differentiable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (m : ℕ) (M Nn : Fin g → ℤ) (χ : N.X) :
    Differentiable ℂ (d.term σ S m M Nn χ) := by
  have hθ := (thetaChar_entire_ne_zero_automorphy g' d.τ d.a d.b d.symm d.pos d.ha d.hb).1
  have hzP : Differentiable ℂ (fun Z : Fin g → ℂ => zP σ Z) := differentiable_pi.2 fun i => differentiable_apply _
  have htP : Differentiable ℂ (fun Z : Fin g → ℂ => tP σ Z) := differentiable_pi.2 fun i => differentiable_apply _
  have hdot : ∀ {n : Type} [Fintype n] (v : n → ℂ), Differentiable ℂ (fun Z : n → ℂ => v ⬝ᵥ Z) := by
    intro n _ v
    simp only [dotProduct]
    fun_prop
  have haff : Differentiable ℂ (fun Z : Fin g → ℂ => (m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ S) M Nn) := by fun_prop
  unfold CD.term trFac CD.fj
  have e1 : Differentiable ℂ (fun Z : Fin g → ℂ => thetaChar d.τ d.a d.b
      (zP σ ((m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ S) M Nn) + d.t12 *ᵥ co bX χ)) :=
    hθ.comp ((hzP.comp haff).add_const _)
  have e2 : Differentiable ℂ (fun Z : Fin g → ℂ => co bX χ ⬝ᵥ (tP σ ((m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ S) M Nn) + d.b2)) :=
    by have := (hdot (co bX χ)).comp ((htP.comp haff).add_const d.b2); exact this
  have e3 : Differentiable ℂ (fun Z : Fin g → ℂ => cv Nn ⬝ᵥ Z) := hdot _
  refine Differentiable.mul ?_ (Differentiable.mul ?_ e1)
  · fun_prop
  · fun_prop
end GlobalTheory.MBLow.Cl.TwistExp

namespace GlobalTheory.MBLow.Cl

theorem term_smul_bmat : AllCD fun {N} {g'} {r} {g} {bX} d σ => (∀ S m M Nn χ, Differentiable ℂ (d.term σ S m M Nn χ)) ∧ ∀ (k m : ℕ) (β : N.Form k), 1 ≤ m → m ^ 2 ∣ k → ∀ (w : ℂ) (M Nn : Fin g → ℤ) (χ : N.X) (Z : Fin g → ℂ), d.term σ (w • bmat bX β) m M Nn χ Z = d.term σ 0 m M Nn χ Z * Complex.exp ((2 * Real.pi * Complex.I : ℂ) * w) ^ (β.be ((∑ l, tP σ Nn l • bX l) + m • χ) ((∑ l, tP σ Nn l • bX l) + m • χ) / (2 * m ^ 2)).toNat := by
  intro N g' r g bX d σ
  exact ⟨fun S m M Nn χ => TwistExp.term_differentiable d σ S m M Nn χ,
    fun k m β hm hk w M Nn χ Z => TwistExp.main_eq d σ k m β hm hk w M Nn χ Z⟩

end GlobalTheory.MBLow.Cl
