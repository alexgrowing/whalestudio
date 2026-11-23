import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulCoeEqZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.RayEv GlobalTheory.ExpUniqCh0

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetScaleTop

open MvPolynomial

variable {S : Type} [CommRing S] {ρ : Type}

abbrev scaleSub (c : S) : MvPolynomial ρ S →ₐ[S] MvPolynomial ρ S :=
  aeval fun i => C c * X i

theorem scaleSub_sub_mem_orig (c : S) (f : MvPolynomial ρ S) :
    scaleSub c f - f ∈ orig S ρ := by
  have h : (Ideal.Quotient.mkₐ S (orig S ρ)).comp (scaleSub c) = Ideal.Quotient.mkₐ S (orig S ρ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, scaleSub, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (X_mem_orig i)) (X_mem_orig i)
  have := DFunLike.congr_fun h f
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
  exact Ideal.Quotient.eq.1 this

theorem scaleSub_pow_mem (c : S) (k : ℕ) (P : MvPolynomial ρ S) (hP : P ∈ orig S ρ ^ k) :
    scaleSub c P - c ^ k • P ∈ orig S ρ ^ (k + 1) := by
  induction k generalizing P with
  | zero => simpa using scaleSub_sub_mem_orig c P
  | succ k ih =>
    rw [pow_succ] at hP
    refine Submodule.mul_induction_on hP (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    ·
      induction hb using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        have e : scaleSub c (a * X i) - c ^ (k + 1) • (a * X i) =
            (scaleSub c a - c ^ k • a) * (C c * X i) := by
          simp only [map_mul, scaleSub, aeval_X, smul_eq_C_mul, map_pow]
          ring
        rw [e, pow_succ]
        exact Ideal.mul_mem_mul (ih a ha) (Ideal.mul_mem_left _ _ (X_mem_orig i))
      | zero => simp
      | add x y _ _ hx hy =>
        have e : scaleSub c (a * (x + y)) - c ^ (k + 1) • (a * (x + y)) =
            (scaleSub c (a * x) - c ^ (k + 1) • (a * x)) + (scaleSub c (a * y) - c ^ (k + 1) • (a * y)) := by
          simp only [mul_add, map_add, smul_add]
          abel
        rw [e]
        exact Ideal.add_mem _ hx hy
      | smul f x hxm hx =>
        have e : scaleSub c (a * (f • x)) - c ^ (k + 1) • (a * (f • x)) =
            scaleSub c f * (scaleSub c (a * x) - c ^ (k + 1) • (a * x)) +
              (scaleSub c f - f) * (c ^ (k + 1) • (a * x)) := by
          simp only [smul_eq_mul, map_mul, smul_eq_C_mul]
          ring
        rw [e]
        refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) ?_
        have hax : c ^ (k + 1) • (a * x) ∈ orig S ρ ^ (k + 1) := by
          rw [pow_succ]
          rw [smul_eq_C_mul]
          exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul ha (show x ∈ orig S ρ from hxm))
        rw [pow_succ' _ (k + 1)]
        exact Ideal.mul_mem_mul (scaleSub_sub_mem_orig c f) hax
    · have e : scaleSub c (x + y) - c ^ (k + 1) • (x + y) =
          (scaleSub c x - c ^ (k + 1) • x) + (scaleSub c y - c ^ (k + 1) • y) := by
        simp only [map_add, smul_add]
        abel
      rw [e]
      exact Ideal.add_mem _ hx hy

theorem jetScale_top {S : Type} [CommRing S] {ρ : Type} (m : ℕ) (c : S) (p : Jet S ρ (m + 1))
    (hp : (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m) p = 0) :
    jetScale (fun _ => c) p = c ^ (m + 1) • p := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective p
  have hP : P ∈ orig S ρ ^ (m + 1) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [jetTrunc] using hp
  have h1 : jetScale (fun _ => c) (Ideal.Quotient.mk (orig S ρ ^ (m + 1 + 1)) P) =
      Ideal.Quotient.mk (orig S ρ ^ (m + 1 + 1)) (scaleSub c P) := by
    rfl
  have h2 : c ^ (m + 1) • Ideal.Quotient.mk (orig S ρ ^ (m + 1 + 1)) P =
      Ideal.Quotient.mk (orig S ρ ^ (m + 1 + 1)) (c ^ (m + 1) • P) :=
    (map_smul (Ideal.Quotient.mkₐ S (orig S ρ ^ (m + 1 + 1))) (c ^ (m + 1)) P).symm
  rw [h1, h2, Ideal.Quotient.eq]
  exact scaleSub_pow_mem c (m + 1) P hP

end GlobalTheory.JetScaleTop
