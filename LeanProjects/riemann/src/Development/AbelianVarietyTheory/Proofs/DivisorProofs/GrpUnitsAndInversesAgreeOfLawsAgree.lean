import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem hom_ext_of_cartesian {S S₀ X : Scheme.{0}} {q : X ⟶ S} {s₀ : S₀ ⟶ S} {A : Over S₀}
    {i : A.left ⟶ X} (h : IsPullback i A.hom q s₀) {T : Scheme.{0}} {t₀ : T ⟶ S₀}
    (c c' : Over.mk t₀ ⟶ A) (hc : c.left ≫ i = c'.left ≫ i) : c = c' := by
  apply Over.OverMorphism.ext
  apply h.hom_ext hc
  rw [Over.w c, Over.w c']

theorem oneAgree_invAgree_of_mulAgree : ∀ (S S₀ S₁ X : Scheme.{0}) (q : X ⟶ S) (s₀ : S₀ ⟶ S) (s₁ : S₁ ⟶ S) (A : Over S₀) [GrpObj A] (G : Over S₁) [GrpObj G] (i : A.left ⟶ X) (e : G.left ⟶ X), IsPullback i A.hom q s₀ → e ≫ q = G.hom ≫ s₁ → MulAgree G A e i → OneAgree s₁ s₀ G A e i ∧ ∀ (T : Scheme.{0}) (t₁ : T ⟶ S₁) (t₀ : T ⟶ S₀) (a : Over.mk t₁ ⟶ G) (a' : Over.mk t₀ ⟶ A), a.left ≫ e = a'.left ≫ i → (a⁻¹).left ≫ e = (a'⁻¹).left ≫ i := by
  intro S S₀ S₁ X q s₀ s₁ A _ G _ i e h he hm
  have one : OneAgree s₁ s₀ G A e i := by
    intro T t₁ t₀ ht
    have hw : ((1 : Over.mk t₁ ⟶ G).left ≫ e) ≫ q = t₀ ≫ s₀ := by
      rw [Category.assoc, he, ← Category.assoc, Over.w]; exact ht
    let a' : Over.mk t₀ ⟶ A := Over.homMk (h.lift _ t₀ hw) (by simp)
    have ha' : a'.left ≫ i = (1 : Over.mk t₁ ⟶ G).left ≫ e := h.lift_fst _ _ _
    have hmm := hm T t₁ t₀ 1 1 a' a' ha'.symm ha'.symm
    rw [_root_.mul_one] at hmm
    have h2 : a' * a' = a' := hom_ext_of_cartesian h _ _ (by rw [← hmm, ha'])
    have h3 : a' = 1 := by simpa using h2
    rw [← ha', h3]
  refine ⟨one, ?_⟩
  intro T t₁ t₀ a a' haa
  have ht : t₁ ≫ s₁ = t₀ ≫ s₀ := by
    have w1 : a.left ≫ G.hom = t₁ := Over.w a
    have w0 : a'.left ≫ A.hom = t₀ := Over.w a'
    calc t₁ ≫ s₁ = (a.left ≫ G.hom) ≫ s₁ := by rw [w1]
      _ = (a.left ≫ e) ≫ q := by rw [Category.assoc, Category.assoc, he]
      _ = (a'.left ≫ i) ≫ q := by rw [haa]
      _ = (a'.left ≫ A.hom) ≫ s₀ := by rw [Category.assoc, Category.assoc, h.w]
      _ = t₀ ≫ s₀ := by rw [w0]
  have hw : ((a⁻¹).left ≫ e) ≫ q = t₀ ≫ s₀ := by
    rw [Category.assoc, he, ← Category.assoc, Over.w]; exact ht
  let b' : Over.mk t₀ ⟶ A := Over.homMk (h.lift _ t₀ hw) (by simp)
  have hb' : b'.left ≫ i = (a⁻¹).left ≫ e := h.lift_fst _ _ _
  have hmm := hm T t₁ t₀ a a⁻¹ a' b' haa hb'.symm
  rw [_root_.mul_inv_cancel] at hmm
  have h2 : a' * b' = 1 := hom_ext_of_cartesian h _ _ (by rw [← hmm, one T t₁ t₀ ht])
  have h3 : b' = a'⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [← h3, hb']

end GlobalTheory.Desc
