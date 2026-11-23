import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem eq_zero_of_sum_smul_matrix {G : Type} [AddCommGroup G] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ)
    (hM : IsUnit M.det) (f : Fin r → G) (h : ∀ i, ∑ j, M i j • f j = 0) (k : Fin r) : f k = 0 := by
  have e1 : f k = ∑ j, (1 : Matrix (Fin r) (Fin r) ℤ) k j • f j := by
    simp [Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_mul M hM]
  simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, h, smul_zero, Finset.sum_const_zero]

theorem eq_one_of_prod_zpow_matrix {G : Type} [CommGroup G] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ)
    (hM : IsUnit M.det) (f : Fin r → G) (h : ∀ i, ∏ j, f j ^ M i j = 1) (k : Fin r) : f k = 1 := by
  have := eq_zero_of_sum_smul_matrix M hM (fun j => Additive.ofMul (f j)) (fun i => by
    simpa [← ofMul_zpow, ← ofMul_prod] using congrArg Additive.ofMul (h i)) k
  simpa using this

theorem gtRelV_prod_tor_mul {F : Type} [Field F] {N : NumD F} {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (x : Fin r → N.X)
    (vs : Fin r → N.Gt) (T : Fin r → (Multiplicative N.X →* Fˣ)) :
    (∏ i, ∏ j, ((N.tor (T j) * vs j).s (x i) * (N.tor (T i) * vs i).s (x j) /
        (N.θ (N.c (x j)) (N.tor (T j) * vs j).b (N.c (x i)) * N.θ (N.c (x j)) (N.tor (T j) * vs j).b
            (N.tor (T i) * vs i).b *
          N.θ (N.c (x i)) (N.tor (T i) * vs i).b (N.c (x j) * (N.tor (T j) * vs j).b))) ^ W i j : Fˣ) =
      (∏ i, ∏ j, ((vs j).s (x i) * (vs i).s (x j) /
        (N.θ (N.c (x j)) (vs j).b (N.c (x i)) * N.θ (N.c (x j)) (vs j).b (vs i).b *
          N.θ (N.c (x i)) (vs i).b (N.c (x j) * (vs j).b))) ^ W i j) *
      ∏ i, ∏ j, (T j (Multiplicative.ofAdd (x i)) * T i (Multiplicative.ofAdd (x j))) ^ W i j := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← mul_zpow]
  congr 1
  simp only [NumD.tor_mul_s_apply, NumD.Gt.mul_b, NumD.tor_b, one_mul, div_eq_mul_inv]
  ac_rfl

theorem gtRelV_prod_single {G : Type} [CommGroup G] {A : Type} [AddCommGroup A] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Fin r → (Multiplicative A →* G)) (i : Fin r) (χ : A) :
    (∏ a, ∏ b, (T b (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) a)) *
        T a (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) b))) ^ W a b) =
      ∏ j, T j (Multiplicative.ofAdd χ) ^ (W + W.transpose) i j := by
  simp only [mul_zpow, Finset.prod_mul_distrib]
  have h1 : (∏ a, ∏ b, T b (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) a)) ^ W a b) =
      ∏ j, T j (Multiplicative.ofAdd χ) ^ W i j := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro a _ ha
      simp [Pi.single_apply, ha]
    · simp
  have h2 : (∏ a, ∏ b, T a (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) b)) ^ W a b) =
      ∏ j, T j (Multiplicative.ofAdd χ) ^ W j i := by
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Finset.prod_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Matrix.add_apply, Matrix.transpose_apply, zpow_add]

theorem gtRelV_components_unique : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F),
    TensFacts W φ e wv → IsUnit (W + W.transpose).det →
      ∀ (v' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv v' us → vs = us := by
  intro F _ N N' r W φ e wv hT hdet v' vs us hv hu
  have hb : ∀ j, (us j).b = (vs j).b := fun j => (hu.1 j).symm.trans (hv.1 j)
  have ht : ∀ j, ∃ t, N.tor t = us j / vs j := fun j =>
    (N.exists_tor_iff _).2 (by rw [div_eq_mul_inv, NumD.Gt.mul_b, NumD.Gt.inv_b, hb, mul_inv_cancel])
  choose T hT' using ht
  have hus : us = fun j => N.tor (T j) * vs j := funext fun j => by rw [hT', div_mul_cancel]
  subst hus
  have hwv : ∀ x, wv x ≠ 0 := hT.2.2.2.2.2.1
  have key : ∀ χ', (∏ i, ∏ j, (T j (Multiplicative.ofAdd (e χ' i)) * T i (Multiplicative.ofAdd (e χ' j))) ^ W i j) = 1 := by
    intro χ'
    have a := hv.2 χ'
    have b := hu.2 χ'
    rw [a, gtRelV_prod_tor_mul W (e χ') vs T] at b
    have c := mul_right_cancel₀ (hwv _) (mul_right_cancel₀ (hwv 1) b)
    have d := Units.ext c
    exact (mul_eq_left.1 d.symm)
  have hall : ∀ χ j, T j (Multiplicative.ofAdd χ) = 1 := by
    intro χ
    refine eq_one_of_prod_zpow_matrix (W + W.transpose) hdet (fun j => T j (Multiplicative.ofAdd χ)) fun i => ?_
    obtain ⟨χ', hχ'⟩ := hT.2.2.2.1.2 (Pi.single i χ)
    have := key χ'
    rw [hχ', gtRelV_prod_single W T i χ] at this
    exact this
  funext j
  have : T j = 1 := MonoidHom.ext fun m => by simpa using hall m.toAdd j
  rw [this, NumD.tor_one, _root_.one_mul]

end GlobalTheory.Mum.TensTor
