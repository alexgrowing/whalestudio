import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.SqRootPairing

theorem eq_of_sq_eq_of_odd {G : Type} [CommGroup G] {k : ℕ} (hk : Odd k) {a b : G} (ha : a ^ k = 1) (hb : b ^ k = 1)
    (h : a ^ 2 = b ^ 2) : a = b := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul] at ha hb
  rw [h] at ha
  exact mul_left_cancel (ha.trans hb.symm)

theorem weilIs_down {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hp : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f)
    (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (c : Γ(T.left, ⊤)ˣ) (ex : x₀.left = x.left ≫ φ)
    (ey : y₀.left = y.left ≫ φ) (h : Out.WeilIs G L k x₀ y₀ c) : Out.WeilIs G' L' k x y c := by
  subst hg
  exact (weilIs_grpPullback_of_comm _ _ _ _ _ _ _ _ hL hL' hp hw T k x y x₀ y₀ c ex ey).2 h

theorem pow_eq_one (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {k n : ℕ} {T : Over S}
    {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (H : Out.WeilIs P.A P.L k x y c) (hx : x ^ n = 1) : c ^ n = 1 := by
  have key : ∀ l : ℕ, Out.WeilIs P.A P.L k (x ^ (l + 1)) y (c ^ (l + 1)) := fun l => by
    induction l with
    | zero => rw [zero_add, pow_one, pow_one]; exact H
    | succ l ih => rw [pow_succ, pow_succ c]; exact (hL.weil S P k T).2.1 _ _ _ _ _ ih H
  have := key n
  rw [pow_succ, hx, _root_.one_mul] at this
  have e := CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB this H
  rwa [pow_succ, mul_eq_right] at e

theorem weilIs_lev_of_sqOf : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp K) (c : SiegPre h k ζ s) (p : Sp ℂ ⟶ S) (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ c.A.left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → p ≫ s = spMap σ → SqOf P c p φ → (∀ a, (lev a).left ≫ φ = p ≫ (c.lev a).left) → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → ∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e) := by
  intro h k K _ ζ σ S s c p P φ lev hk3 hk hζ hp hsq hlev _ tors a b e he
  obtain ⟨hpb, -, φ₂, sq, iso⟩ := hsq
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let z : ℂˣ := Units.mk0 (σ ζ) (by rw [hζ]; exact Complex.exp_ne_zero _)
  have hz : (z : ℂ) = σ ζ := rfl
  have hzk : z ^ k = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hz, hζ, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hk0, Complex.exp_neg,
      Complex.exp_two_pi_mul_I, inv_one, Units.val_one])
  have hez : e = z ^ omegaStd a b := Units.ext (by
    rw [Units.val_zpow_eq_zpow_val, hz, hζ, ← Complex.exp_int_mul, he]
    congr 1
    ring)
  have lam : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have dg : ((abelian₂ P.A P.L).pull (lift (𝟙 P.A) (𝟙 P.A)).left).IsLB := LB.isLB_linComb lam _ _
  have dc : (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left).IsLB := LB.isLB_linComb c.isLB _ _
  have w₀ := (c.geom ℂ p σ z hp hz).2.2 a b
  have pt : ∀ a, (toUnit (Over.mk p) ≫ c.lev a).left = (lev a).left ≫ φ := fun a => by
    rw [hlev, Over.comp_left, Over.toUnit_left]
    rfl
  have w₁ := weilIs_down dc dg hpb (SiegelPull.diag_iso sq iso) (𝟙_ (Over (Sp ℂ))) p (Category.id_comp p).symm k
    (lev a) (lev b) _ _ _ (pt a) (pt b) w₀
  obtain ⟨c₀, hc₀, -⟩ := (hL.weil _ P k (𝟙_ (Over (Sp ℂ)))).1 (lev a) (lev b) (tors a) (tors b)
  have w₂ := SiegelOfPolarised.weilIs_of_lbIso_pow hL.globalFns P.isAb P.isLB dg
    (SiegelOfPolarised.lbIso_diag hL P) hc₀
  have e₂ := CommutatorPairing.weilIs_unique hL.globalFns P.isAb dg w₂ w₁
  have up : ∀ (u : ℂˣ) (n : ℕ), unitOn (u ^ n) = unitOn u ^ n := fun u n => map_pow _ _ _
  have e₁ : c₀ = unitOn e := by
    refine eq_of_sq_eq_of_odd hk (pow_eq_one hL P hc₀ (tors a)) ?_ (e₂.trans ?_)
    · refine (up e k).symm.trans ?_
      rw [hez, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzk, one_zpow]
      exact map_one _
    · refine Eq.trans ?_ (up e 2)
      rw [hez, mul_comm, zpow_mul, zpow_ofNat]
  exact e₁ ▸ hc₀

end GlobalTheory.SqRootPairing
