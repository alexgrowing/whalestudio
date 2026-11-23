import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff

set_option autoImplicit false

noncomputable section

open TensorProduct GlobalTheory.PerfdLat

namespace GlobalTheory.LatBaseChange

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {f : A} {h : ℕ}
  {N : Submodule B (Fin h → B)} {L : Submodule A (Fin h → A)}

def incl (B : Type) [CommRing B] [Algebra A B] (L : Submodule A (Fin h → A)) : L →ₗ[A] (Fin h → B) where
  toFun x j := algebraMap A B ((x : Fin h → A) j)
  map_add' x y := funext fun j => by simp
  map_smul' a x := funext fun j => by simp [Algebra.smul_def]

variable (hN : ∀ y : Fin h → B, algebraMap A B f • y ∈ N)
  (hL : ∀ x : Fin h → A, x ∈ L ↔ piMap (algebraMap A B) (Fin h) x ∈ N)
include hN hL

def fx (x : Fin h → A) : L :=
  ⟨f • x, (hL _).2 (by rw [map_smulₛₗ]; exact hN _)⟩

theorem fx_eq_sum (x : Fin h → A) : fx hN hL x = ∑ j, x j • fx hN hL (Pi.single j 1) := by
  ext k
  simp [fx, Submodule.coe_sum, Finset.sum_apply, Pi.single_apply, mul_comm]

def D (a : L) (y : Fin h → B) : B ⊗[A] L := (1 : B) ⊗ₜ a + ∑ j, y j ⊗ₜ fx hN hL (Pi.single j 1)

theorem D_add (a a' : L) (y y' : Fin h → B) : D hN hL (a + a') (y + y') = D hN hL a y + D hN hL a' y' := by
  simp only [D, tmul_add, Pi.add_apply, add_tmul, Finset.sum_add_distrib]
  abel

theorem D_eq (hreg : IsSMulRegular B (algebraMap A B f))
    (hinj : ∀ (a : A) (y : B), algebraMap A B a = algebraMap A B f * y → ∃ b, a = f * b)
    (a a' : L) (y y' : Fin h → B)
    (he : piMap (algebraMap A B) (Fin h) a + algebraMap A B f • y =
      piMap (algebraMap A B) (Fin h) a' + algebraMap A B f • y') :
    D hN hL a y = D hN hL a' y' := by
  have hc : ∀ j, algebraMap A B ((a : Fin h → A) j) + algebraMap A B f * y j =
      algebraMap A B ((a' : Fin h → A) j) + algebraMap A B f * y' j := fun j => by
    have := congrFun he j
    simp only [Pi.add_apply, piMap_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this
  choose w hw using fun j => hinj ((a : Fin h → A) j - (a' : Fin h → A) j) (y' j - y j) (by rw [map_sub, mul_sub]; linear_combination hc j)
  have hw' : ∀ j, algebraMap A B (w j) = y' j - y j := fun j => hreg (by
    change algebraMap A B f * _ = algebraMap A B f * _
    rw [← map_mul, ← hw j, map_sub, mul_sub]; linear_combination hc j)
  have ha : a = a' + fx hN hL w := by
    ext k
    simp only [fx, Submodule.coe_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hw k
  unfold D
  rw [ha, tmul_add, fx_eq_sum, tmul_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_tmul, ← Algebra.algebraMap_eq_smul_one, ← add_tmul, hw', sub_add_cancel]

omit hN hL in

theorem nonempty_tensor_equiv : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (f : A) (h : ℕ)
    (N : Submodule B (Fin h → B)) (L : Submodule A (Fin h → A)), IsSMulRegular B (algebraMap A B f) →
    (∀ x : B, ∃ (a : A) (y : B), x = algebraMap A B a + algebraMap A B f * y) →
    (∀ (a : A) (y : B), algebraMap A B a = algebraMap A B f * y → ∃ b, a = f * b) →
    (∀ y : Fin h → B, algebraMap A B f • y ∈ N) →
    (∀ x : Fin h → A, x ∈ L ↔ piMap (algebraMap A B) (Fin h) x ∈ N) → Nonempty (TensorProduct A B L ≃ₗ[B] N) := by
  intro A B _ _ _ f h N L hreg hsurj hinj hN hL
  let μ : B ⊗[A] L →ₗ[B] (Fin h → B) := (incl B L).liftBaseChange B
  have hμ : ∀ (b : B) (x : L), μ (b ⊗ₜ x) = b • piMap (algebraMap A B) (Fin h) x := fun b x =>
    LinearMap.liftBaseChange_tmul _ _ _ _
  have hrange : ∀ t, μ t ∈ N := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b x => rw [hμ]; exact N.smul_mem b ((hL _).1 x.2)
    | add s t hs ht => rw [map_add]; exact N.add_mem hs ht
  have hμD : ∀ (a : L) (y : Fin h → B),
      μ (D hN hL a y) = piMap (algebraMap A B) (Fin h) a + algebraMap A B f • y := by
    intro a y
    simp only [D, map_add, map_sum, hμ, one_smul]
    congr 1
    ext k
    simp [fx, Finset.sum_apply, Pi.single_apply, mul_comm, Algebra.smul_def]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp
  have hdec : ∀ n : N, ∃ (a : L) (y : Fin h → B),
      (n : Fin h → B) = piMap (algebraMap A B) (Fin h) a + algebraMap A B f • y := by
    intro n
    choose a y hy using fun j => hsurj ((n : Fin h → B) j)
    have hn : (n : Fin h → B) = piMap (algebraMap A B) (Fin h) a + algebraMap A B f • y := funext fun j => by
      simp only [Pi.add_apply, piMap_apply, Pi.smul_apply, smul_eq_mul]
      exact hy j
    refine ⟨⟨a, (hL a).2 ?_⟩, y, hn⟩
    rw [eq_sub_of_add_eq hn.symm]
    exact N.sub_mem n.2 (hN y)
  choose ca cy hc using hdec
  let ψ : N → B ⊗[A] L := fun n => D hN hL (ca n) (cy n)
  have hψ : ∀ (n : N) (a : L) (y : Fin h → B),
      (n : Fin h → B) = piMap (algebraMap A B) (Fin h) a + algebraMap A B f • y → ψ n = D hN hL a y :=
    fun n a y hn => D_eq hN hL hreg hinj _ _ _ _ ((hc n).symm.trans hn)
  have hψadd : ∀ m n, ψ (m + n) = ψ m + ψ n := fun m n => by
    rw [hψ (m + n) (ca m + ca n) (cy m + cy n), D_add]
    rw [Submodule.coe_add, hc m, hc n, Submodule.coe_add, map_add, smul_add]
    abel
  let μN := LinearMap.codRestrict N μ hrange
  have hleft : ∀ t, ψ (μN t) = t := fun t => by
    induction t using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, hψ 0 0 0 (by simp)]
      simp [D]
    | tmul b x =>
      obtain ⟨a0, c, rfl⟩ := hsurj b
      have he : ((μN ((algebraMap A B a0 + algebraMap A B f * c) ⊗ₜ x) : N) : Fin h → B) =
          piMap (algebraMap A B) (Fin h) (a0 • x : L) + algebraMap A B f • (c • piMap (algebraMap A B) (Fin h) x) := by
        change μ _ = _
        rw [hμ]
        ext j
        simp only [Pi.add_apply, Pi.smul_apply, piMap_apply, smul_eq_mul, Submodule.coe_smul, map_mul]
        ring
      rw [hψ _ _ _ he]
      have hfx : (f • x : L) = fx hN hL x := Subtype.ext rfl
      have h1 : (algebraMap A B a0) ⊗ₜ[A] x = (1 : B) ⊗ₜ (a0 • x) := by
        rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
      have h2 : (algebraMap A B f * c) ⊗ₜ[A] x =
          ∑ j, (c • piMap (algebraMap A B) (Fin h) x) j ⊗ₜ fx hN hL (Pi.single j 1) := by
        rw [← Algebra.smul_def, smul_tmul, hfx, fx_eq_sum, tmul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← smul_tmul]
        congr 1
        simp [Algebra.smul_def, mul_comm]
      rw [add_tmul, h1, h2]
      rfl
    | add s t hs ht => rw [map_add, hψadd, hs, ht]
  refine ⟨LinearEquiv.ofBijective μN ⟨Function.LeftInverse.injective hleft, fun n => ?_⟩⟩
  exact ⟨D hN hL (ca n) (cy n), Subtype.ext ((hμD _ _).trans (hc n).symm)⟩

end GlobalTheory.LatBaseChange
