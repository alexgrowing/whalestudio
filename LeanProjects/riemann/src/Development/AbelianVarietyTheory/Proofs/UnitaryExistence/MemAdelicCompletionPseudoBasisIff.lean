import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

noncomputable section

namespace GlobalTheory.AdLat

open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors

section
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def adCoord (e : Module.Basis (Fin n) E (Fin n → E)) (b : Fin n) : (Fin n → RA F E) →+ RA F E where
  toFun w := ∑ i, w i * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b)
  map_zero' := by simp
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]

theorem sum_mul_repr_single (e : Module.Basis (Fin n) E (Fin n → E)) (x : Fin n → E) (b : Fin n) :
    ∑ i, x i * e.repr (Pi.single i 1) b = e.repr x b := by
  conv_rhs => rw [pi_eq_sum_univ' x]
  simp [map_sum]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.adCoord_tmul (e : Module.Basis (Fin n) E (Fin n → E)) (b : Fin n)
    (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    _root_.GlobalTheory.AdLat.adCoord F e b (fun i => a ⊗ₜ x i) = a ⊗ₜ e.repr x b := by
  have hx : e.repr x b = ∑ i, x i * e.repr (Pi.single i 1) b := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Pi.single i (x i) = x i • (Pi.single i 1 : Fin n → E) by
        ext j; by_cases h : j = i <;> simp [Pi.single_apply, h],
      map_smul, Finsupp.smul_apply, smul_eq_mul]
  change ∑ i, (a ⊗ₜ x i) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hx, TensorProduct.tmul_sum]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.adCoord_smul (e : Module.Basis (Fin n) E (Fin n → E)) (b : Fin n)
    (r : _root_.GlobalTheory.AdLat.RA F E) (w : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.adCoord F e b (r • w) = r * _root_.GlobalTheory.AdLat.adCoord F e b w := by
  change ∑ i, (r • w) i * _ = r * ∑ i, w i * _
  simp [Finset.mul_sum, mul_assoc]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.adCoord_sum (e : Module.Basis (Fin n) E (Fin n → E))
    (z : Fin n → _root_.GlobalTheory.AdLat.RA F E) (b : Fin n) :
    _root_.GlobalTheory.AdLat.adCoord F e b (∑ a, z a • _root_.GlobalTheory.AdLat.fv F (e a)) = z b := by
  have h1 : ∀ a, _root_.GlobalTheory.AdLat.adCoord F e b (_root_.GlobalTheory.AdLat.fv F (e a)) =
      if a = b then 1 else 0 := by
    intro a
    have := _root_.GlobalTheory.AdLat.adCoord_tmul F e b 1 (e a)
    unfold _root_.GlobalTheory.AdLat.fv
    rw [this, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp [Algebra.TensorProduct.one_def]
  simp only [map_sum, _root_.GlobalTheory.AdLat.adCoord_smul, h1, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
theorem _root_.GlobalTheory.AdLat.mem_hat_pseudoBasis_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (e : Module.Basis (Fin n) E (Fin n → E)) (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E), (∀ v, v ∈ L ↔ ∀ a, e.repr v a ∈ cI a) → ∀ z : Fin n → _root_.GlobalTheory.AdLat.RA F E, (∑ a, z a • _root_.GlobalTheory.AdLat.fv F (e a)) ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) ↔ ∀ a, z a ∈ _root_.GlobalTheory.AdLat.hat1 F (cI a : Set E) := by
  intro F E _ _ _ _ _ n L e cI hL z
  constructor
  · intro hz b
    rw [← _root_.GlobalTheory.AdLat.adCoord_sum F e z b]
    have key : _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) ≤
        (_root_.GlobalTheory.AdLat.hat1 F (cI b : Set E)).comap (_root_.GlobalTheory.AdLat.adCoord F e b) := by
      unfold _root_.GlobalTheory.AdLat.hat
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, x, hx, rfl⟩
      simp only [AddSubgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe]
      rw [_root_.GlobalTheory.AdLat.adCoord_tmul]
      unfold _root_.GlobalTheory.AdLat.hat1
      exact AddSubgroup.subset_closure ⟨c, hc, _, (hL x).1 hx b, rfl⟩
    exact key hz
  · intro hz
    refine AddSubgroup.sum_mem _ fun a _ => ?_
    have key : _root_.GlobalTheory.AdLat.hat1 F (cI a : Set E) ≤
        (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))).comap
          ((smulAddHom (_root_.GlobalTheory.AdLat.RA F E)
            (Fin n → _root_.GlobalTheory.AdLat.RA F E)).flip (_root_.GlobalTheory.AdLat.fv F (e a))) := by
      unfold _root_.GlobalTheory.AdLat.hat1
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, y, hy, rfl⟩
      simp only [AddSubgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe,
        AddMonoidHom.flip_apply, smulAddHom_apply]
      have hmem : y • e a ∈ L := by
        rw [hL]
        intro a'
        rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; simpa using hy
        · simpa using (cI a').zero_mem
      unfold _root_.GlobalTheory.AdLat.hat
      refine AddSubgroup.subset_closure ⟨c, hc, _, hmem, ?_⟩
      funext i
      unfold _root_.GlobalTheory.AdLat.fv
      change (c ⊗ₜ[F] y) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] e a i) = c ⊗ₜ[F] (y • e a) i
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Pi.smul_apply, smul_eq_mul]
    exact key (hz a)

end GlobalTheory.AdLat
