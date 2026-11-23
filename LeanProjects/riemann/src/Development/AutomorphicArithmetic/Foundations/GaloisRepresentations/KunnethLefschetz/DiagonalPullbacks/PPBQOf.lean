import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.ProjectiveBundleFormulaTorsion
import Development.EtaleCohomology.EtaleTrace.LRingPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.Di
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.Di.PPBQOf

variable {l : ℕ} [Fact l.Prime]

private def tr {X : Scheme.{0}} {a b : ℤ} (h : a = b) (x : V l X a) : V l X b := h ▸ x

private lemma tr_tr {X : Scheme.{0}} {a b c : ℤ} (h : a = b) (h' : b = c) (x : V l X a) :
    tr h' (tr h x) = tr (h.trans h') x := by
  subst h; subst h'; rfl

private lemma tr_self {X : Scheme.{0}} {a : ℤ} (h : a = a) (x : V l X a) : tr h x = x := rfl

private lemma tr_eq_zero {X : Scheme.{0}} {a b : ℤ} (h : a = b) (x : V l X a) (hx : tr h x = 0) : x = 0 := by
  subst h; exact hx

private lemma t0 (hR : Ring l) {E Z : Scheme.{0}} (r : E ⟶ Z) (hE : IsUnit (l : Γ(E, ⊤))) (ξ : V l E 2)
    {a n : ℤ} {j : ℕ} (hj : j = 0) (h : a + 2 * (j : ℤ) = n) (ha : a = n) (u : V l Z a) :
    cupV l E h (pb l r a u) (powV l ξ j) = pb l r n (tr ha u) := by
  subst hj; subst ha
  exact hR.mul_one E hE _ _

private lemma pow_one (hR : Ring l) {E : Scheme.{0}} (hE : IsUnit (l : Γ(E, ⊤))) (ξ : V l E 2) :
    (powV l ξ 1 : V l E 2) = ξ :=
  hR.one_mul E hE 2 ξ

private lemma t1 (hR : Ring l) {E Z : Scheme.{0}} (r : E ⟶ Z) (hE : IsUnit (l : Γ(E, ⊤))) (ξ : V l E 2)
    {a : ℤ} {j : ℕ} (hj : j = 1) (h : a + 2 * (j : ℤ) = 2) (ha : a = 0) (u : V l Z a) :
    cupV l E h (pb l r a u) (powV l ξ j) = cupV l E (zero_add 2) (pb l r 0 (tr ha u)) ξ := by
  subst hj; subst ha
  exact congrArg (cupV l E (zero_add 2) (pb l r 0 u)) (pow_one hR hE ξ)

private lemma tneg (hneg : ∀ (X : Scheme.{0}) (n : ℤ), n < 0 → Subsingleton (V l X n)) {E Z : Scheme.{0}} (r : E ⟶ Z)
    {a m n : ℤ} (ha : a < 0) (h : a + m = n) (u : V l Z a) (w : V l E m) :
    cupV l E h (pb l r a u) w = 0 := by
  haveI := hneg Z a ha
  rw [Subsingleton.elim u 0, map_zero, map_zero, LinearMap.zero_apply]

private lemma sum2 {A : Type*} [AddCommMonoid A] (M : ℕ) (f : Fin (M + 2) → A)
    (h : ∀ j : Fin (M + 2), 2 ≤ (j : ℕ) → f j = 0) : ∑ j, f j = f 0 + f 1 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.succ_zero_eq_one]
  have hz : ∑ i : Fin M, f i.succ.succ = 0 := Finset.sum_eq_zero fun i _ => h _ (by simp)
  rw [hz, add_zero]

end UpperTheory.Gal.KunnethLefschetz.Di.PPBQOf

open UpperTheory.Gal.KunnethLefschetz.Di.PPBQOf in
theorem UpperTheory.Gal.KunnethLefschetz.Di.pBQOf_holds :
    UpperTheory.Gal.KunnethLefschetz.Di.PBQOf := by
  intro l _ hR hneg N hN E Z r hZ ξ hPBV
  have hE := LateralTheory.EtaleTrace.LRingPf.unit_pull l r hZ
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  have key : ∀ (n : ℤ) (a : ∀ j : Fin (M + 2), V l Z (n - 2 * ((j : ℕ) : ℤ))), n ≤ 3 →
      (∑ j : Fin (M + 2), cupV l E (sub_add_cancel n (2 * ((j : ℕ) : ℤ)))
          (pb l r (n - 2 * ((j : ℕ) : ℤ)) (a j)) (powV l ξ (j : ℕ))) =
        cupV l E (sub_add_cancel n (2 * (((0 : Fin (M + 2)) : ℕ) : ℤ)))
          (pb l r (n - 2 * (((0 : Fin (M + 2)) : ℕ) : ℤ)) (a 0)) (powV l ξ ((0 : Fin (M + 2)) : ℕ)) +
        cupV l E (sub_add_cancel n (2 * (((1 : Fin (M + 2)) : ℕ) : ℤ)))
          (pb l r (n - 2 * (((1 : Fin (M + 2)) : ℕ) : ℤ)) (a 1)) (powV l ξ ((1 : Fin (M + 2)) : ℕ)) :=
    fun n a hn => sum2 M _ fun j hj => tneg hneg r (by omega) _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    rw [eq_top_iff]
    rintro z -
    obtain ⟨a, ha⟩ := (hPBV n).2 z
    rw [← ha]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.subset_span ⟨(j : ℕ), n - 2 * ((j : ℕ) : ℤ), sub_add_cancel _ _, a j, rfl⟩
  · intro z
    obtain ⟨a, ha⟩ := (hPBV 0).2 z
    have hz := ha.symm.trans (key 0 a (by norm_num))
    rw [tneg (a := 0 - 2 * (((1 : Fin (M + 2)) : ℕ) : ℤ)) hneg r (by norm_num [Fin.val_one]) _ _ _, add_zero,
      t0 (j := ((0 : Fin (M + 2)) : ℕ)) (a := 0 - 2 * (((0 : Fin (M + 2)) : ℕ) : ℤ)) (n := 0)
        hR r hE ξ (by simp) _ (by simp)] at hz
    exact ⟨_, hz⟩
  · intro z
    obtain ⟨a, ha⟩ := (hPBV 2).2 z
    have hz := ha.symm.trans (key 2 a (by norm_num))
    rw [t0 (j := ((0 : Fin (M + 2)) : ℕ)) (a := 2 - 2 * (((0 : Fin (M + 2)) : ℕ) : ℤ)) (n := 2)
        hR r hE ξ (by simp) _ (by simp),
      t1 (j := ((1 : Fin (M + 2)) : ℕ)) (a := 2 - 2 * (((1 : Fin (M + 2)) : ℕ) : ℤ))
        hR r hE ξ (by simp [Fin.val_one]) _ (by norm_num [Fin.val_one])] at hz
    exact ⟨_, _, hz⟩
  · intro u v huv
    let a : ∀ j : Fin (M + 2), V l Z (2 - 2 * ((j : ℕ) : ℤ)) := fun j =>
      if h0 : (j : ℕ) = 0 then tr (by rw [h0]; norm_num) u
      else if h1 : (j : ℕ) = 1 then tr (by rw [h1]; norm_num) v else 0
    have ha0 : a 0 = tr (by simp) u := by simp [a]
    have ha1 : a 1 = tr (by norm_num [Fin.val_one]) v := by simp [a, Fin.val_one]
    have hzero : a = 0 := by
      apply (hPBV 2).1
      beta_reduce
      rw [key 2 a (by norm_num), key 2 0 (by norm_num)]
      simp only [Pi.zero_apply, map_zero, LinearMap.zero_apply, add_zero]
      rw [ha0, ha1,
        t0 (j := ((0 : Fin (M + 2)) : ℕ)) (a := 2 - 2 * (((0 : Fin (M + 2)) : ℕ) : ℤ)) (n := 2)
          hR r hE ξ (by simp) _ (by simp),
        t1 (j := ((1 : Fin (M + 2)) : ℕ)) (a := 2 - 2 * (((1 : Fin (M + 2)) : ℕ) : ℤ))
          hR r hE ξ (by simp [Fin.val_one]) _ (by norm_num [Fin.val_one]),
        tr_tr, tr_tr, tr_self, tr_self]
      exact huv
    have h1 := congrFun hzero 1
    rw [ha1] at h1
    exact tr_eq_zero _ v h1
