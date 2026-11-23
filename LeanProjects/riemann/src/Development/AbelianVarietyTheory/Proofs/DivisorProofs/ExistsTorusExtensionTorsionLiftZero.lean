import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.QkExtExistsG
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsLiftRoot

open ReciprocityTheory.ChartRestriction.G.DVR

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h

theorem cubN_succ' (k : ℕ) (a m x : A) : cubN θ (k + 1) a m x = cubN θ k a m x * θ (a * m ^ k) m x :=
  Finset.prod_range_succ _ _

theorem ex_pow (c x : A) (w : U) (k : ℕ) :
    (⟨x, w⟩ : Ex h c) ^ k = ⟨x ^ k, w ^ k * (cubN θ k 1 x c)⁻¹⟩ := by
  induction k with
  | zero => exact Ex.ext (pow_zero x).symm (by simp [cubN]; rfl)
  | succ k ih =>
    rw [pow_succ, ih]
    refine Ex.ext (pow_succ x k).symm ?_
    rw [Ex.mul_u, cubN_succ' h]
    show _ = _ * (_ * θ (1 * x ^ k) x c)⁻¹
    rw [_root_.one_mul, h.s01 c, h.s12 (x ^ k) c x, pow_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem cubN_pow (a x : A) (n k : ℕ) :
    cubN θ n 1 a (x ^ k) * cubN θ k 1 x a ^ n = cubN θ n 1 a x ^ k * cubN θ k 1 x (a ^ n) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, h.N_one]; simp [cubN]
  | succ k ih =>
    have e := h.N_add n 1 a (x ^ k) x
    rw [h.face, _root_.mul_one, _root_.one_mul] at e
    rw [cubN_succ' h, cubN_succ' h, _root_.one_mul, pow_succ x k, h.s12 (x ^ k) x a, h.s01 (x ^ k) a x,
      h.s12 (x ^ k) x (a ^ n), h.s01 (x ^ k) (a ^ n) x]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    have ih' := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ih' ⊢
    simp only [add_nsmul, one_nsmul, nsmul_add]
    linear_combination (norm := abel) e' + ih'

end Alg

section Key

variable {A U X : Type} [CommGroup A] [CommGroup U] [AddCommGroup X] [Module.Free ℤ X] {θ : A → A → A → U}
  (h : IsCub θ)
include h

theorem exists_mult_pow_eq_one {c : X → A} (hc : ∀ χ χ', c (χ + χ') = c χ * c χ') {n : ℕ} (c' : X → A)
    (hc' : ∀ χ, c' χ ^ n = c χ) {b : A} (hb : b ^ n = 1) :
    ∃ v, Mult θ c b v ∧ ∀ χ, ((⟨b, v χ⟩ : Ex h (c χ)) ^ n).u = 1 := by
  let e := Module.Free.chooseBasis ℤ X
  let f : X →ₗ[ℤ] Additive (Ex h b) := e.constr ℤ fun i => Additive.ofMul ⟨c' (e i), 1⟩
  let p : Additive (Ex h b) →+ Additive A := AddMonoidHom.mk' (fun x => Additive.ofMul x.toMul.b) fun _ _ => rfl
  have fb : ∀ χ, (f χ).toMul.b ^ n = c χ := fun χ => by
    have := LinearMap.congr_fun (e.ext (f₁ := n • (p.toIntLinearMap ∘ₗ f))
      (f₂ := (AddMonoidHom.mk' (fun χ => Additive.ofMul (c χ)) hc).toIntLinearMap) fun i => by
        show n • p (f (e i)) = Additive.ofMul (c (e i))
        rw [show f (e i) = Additive.ofMul ⟨c' (e i), 1⟩ from e.constr_basis ℤ _ i, ← hc', ofMul_pow]; rfl) χ
    exact Additive.ofMul.injective (by rw [ofMul_pow]; exact this)
  have fadd : ∀ χ χ', (f (χ + χ')).toMul = (f χ).toMul * (f χ').toMul := fun χ χ' => by rw [map_add]; rfl
  let g : X → Ex h b := fun χ => (f χ).toMul ^ n
  have gadd : ∀ χ χ', g (χ + χ') = g χ * g χ' := fun χ χ' => by simp only [g, fadd, mul_pow]
  have gb : ∀ χ, (g χ).b = c χ := fun χ => (Ex.pow_b _ _).trans (fb χ)
  have m : Mult θ c b fun χ => (g χ).u := by
    refine ⟨?_, fun χ χ' => ?_⟩
    · show ((f 0).toMul ^ n).u = 1
      rw [map_zero, toMul_zero, one_pow]; rfl
    · show (g (χ + χ')).u * _ = _
      rw [gadd, Ex.mul_u, gb, gb, h.s01 b, h.s12 (c χ) b, inv_mul_cancel_right]
  have mp := m.pow (h := h) hc n
  have wadd : ∀ χ χ', ((⟨b, (g (χ + χ')).u⟩ : Ex h (c (χ + χ'))) ^ n).u =
      ((⟨b, (g χ).u⟩ : Ex h (c χ)) ^ n).u * ((⟨b, (g χ').u⟩ : Ex h (c χ')) ^ n).u := fun χ χ' => by
    have := mp.2 χ χ'
    rwa [hb, h.face₃, _root_.mul_one] at this
  have wroot : ∀ χ, ∃ r : U, r ^ n = ((⟨b, (g χ).u⟩ : Ex h (c χ)) ^ n).u := fun χ => by
    refine ⟨(f χ).toMul.u ^ n * (cubN θ n 1 b (f χ).toMul.b)⁻¹, ?_⟩
    have e₁ : (g χ).u = (f χ).toMul.u ^ n * (cubN θ n 1 (f χ).toMul.b b)⁻¹ := by
      show ((f χ).toMul ^ n).u = _
      rw [show (f χ).toMul = ⟨(f χ).toMul.b, (f χ).toMul.u⟩ from rfl, ex_pow h]
    rw [ex_pow h, ← fb χ]
    show _ = (g χ).u ^ n * (cubN θ n 1 b ((f χ).toMul.b ^ n))⁻¹
    have e₂ := cubN_pow h (f χ).toMul.b b n n
    rw [hb, h.N_one, _root_.one_mul] at e₂
    rw [e₁]
    apply Additive.ofMul.injective
    have e₂' := congrArg Additive.ofMul e₂
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, nsmul_add, nsmul_neg] at e₂' ⊢
    rw [smul_neg, smul_neg, e₂']
    abel
  choose r hr using wroot
  let W : X →ₗ[ℤ] Additive U := (AddMonoidHom.mk' (fun χ => Additive.ofMul ((⟨b, (g χ).u⟩ : Ex h (c χ)) ^ n).u)
    wadd).toIntLinearMap
  let ro : X →ₗ[ℤ] Additive U := e.constr ℤ fun i => Additive.ofMul (r (e i))⁻¹
  have roW : ∀ χ, (ro χ).toMul ^ n * ((⟨b, (g χ).u⟩ : Ex h (c χ)) ^ n).u = 1 := fun χ => by
    have := LinearMap.congr_fun (e.ext (f₁ := n • ro) (f₂ := -W) fun i => by
      show n • ro (e i) = -W (e i)
      rw [show ro (e i) = Additive.ofMul (r (e i))⁻¹ from e.constr_basis ℤ _ i, ← ofMul_pow, inv_pow, hr]; rfl) χ
    apply Additive.ofMul.injective
    rw [ofMul_mul, ofMul_pow, ofMul_one]
    exact eq_neg_iff_add_eq_zero.1 this
  have roadd : ∀ χ χ', (ro (χ + χ')).toMul = (ro χ).toMul * (ro χ').toMul := fun χ χ' => by rw [map_add]; rfl
  refine ⟨fun χ => (g χ).u * (ro χ).toMul, ⟨?_, fun χ χ' => ?_⟩, fun χ => ?_⟩
  · show (g 0).u * (ro 0).toMul = 1
    rw [show (g 0).u = 1 from m.1, map_zero, toMul_zero, _root_.mul_one]
  · show (g (χ + χ')).u * (ro (χ + χ')).toMul * _ = (g χ).u * (ro χ).toMul * ((g χ').u * (ro χ').toMul)
    rw [roadd, mul_right_comm, m.2, _root_.mul_mul_mul_comm]
  · rw [ex_pow h, ← roW χ, ex_pow h, mul_pow]
    show (g χ).u ^ n * (ro χ).toMul ^ n * _ = (ro χ).toMul ^ n * ((g χ).u ^ n * _)
    rw [mul_comm ((g χ).u ^ n), _root_.mul_assoc]

end Key

section Main

theorem exists_qk_zero_of_pow_eq : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (n : ℕ), 1 ≤ n →
    ∀ (c' : D.X → (𝟙_ (Over (Sp R)) ⟶ D.P.A)), (∀ χ, c' χ ^ n = D.c χ) →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (b : TF (R := R) F ⟶ D.P.A), b ^ n = 1 →
    ∃ p : QkPt D F n, p.y = 0 ∧ p.g.b = b := by
  intro R _ _ D hB n _ c' hc' F _ _ b hb
  obtain ⟨J, hJ⟩ := good_pt D.P.isLB (default : PrimeSpectrum F)
  have C := isCub_cubV D.cub (T := TF (R := R) F) hJ
  have cpw : ∀ (x : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (k : ℕ), toUnit (TF (R := R) F) ≫ x ^ k = (toUnit _ ≫ x) ^ k :=
    fun x k => by
      induction k with
      | zero => rw [pow_zero, pow_zero]; exact MonObj.comp_one _
      | succ k ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  have cpow : ∀ χ, (toUnit (TF (R := R) F) ≫ c' χ) ^ n = cP D (TF (R := R) F) χ := fun χ => by
    rw [← cpw, hc']; rfl
  obtain ⟨v, m, hv⟩ := exists_mult_pow_eq_one C (cPoint_add D (TF (R := R) F)) (fun χ => toUnit _ ≫ c' χ) cpow hb
  have i0 : ∀ χ, ix (𝟙 _) hJ (0 : D.X) χ = 1 := fun χ => by
    have := ix_add (𝟙 (TF (R := R) F)) hJ hB 0 0 χ
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  obtain ⟨q, h₁, h₂, -⟩ := exists_qk hJ (n := n) 0 b v m fun χ => by
    rw [i0]; exact Ex.ext ((Ex.pow_b _ _).trans hb) (hv χ)
  exact ⟨q, h₁, h₂⟩

end Main

end GlobalTheory.TorsLiftRoot
