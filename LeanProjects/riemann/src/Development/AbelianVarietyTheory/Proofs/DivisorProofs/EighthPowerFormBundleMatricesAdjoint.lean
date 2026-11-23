import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.E8AdjointPairing

open GlobalTheory.CechPic

section Pairing

variable {S : Scheme.{0}} {G G' T : Over S} [GrpObj G] [GrpObj G']

def lamC (x y : T ⟶ G) : Pic G.left →+ Pic T.left where
  toFun c := lam c x y
  map_zero' := by simp only [lam, map_zero]; abel
  map_add' c d := by simp only [lam, map_add]; abel

theorem lamC_apply (c : Pic G.left) (x y : T ⟶ G) : lamC x y c = lam c x y := rfl

theorem lam_pull_of (g : G' ⟶ G) (c : Pic G.left) (u v : T ⟶ G')
    (hm : (u * v) ≫ g = (u ≫ g) * (v ≫ g)) (h1 : (1 : T ⟶ G') ≫ g = 1) :
    lam (pull g.left c) u v = lam c (u ≫ g) (v ≫ g) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, hm, h1]

end Pairing

end GlobalTheory.E8AdjointPairing

namespace GlobalTheory.E8AdjointPairing

open GlobalTheory.CechPic

section Bilinear

variable {S : Scheme.{0}} {G G' T : Over S} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
  {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

theorem lam_mul_right' (x y z : T ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm, lam_comm _ z]

def lamHom (z : T ⟶ G) : (T ⟶ G) →* Multiplicative (Pic T.left) where
  toFun x := Multiplicative.ofAdd (lam (cls L hL) x z)
  map_one' := by rw [lam_one_left]; rfl
  map_mul' x y := by rw [lam_mul_left hL hΘ]; rfl

theorem lam_zpow_left (x z : T ⟶ G) (k : ℤ) :
    lam (cls L hL) (x ^ k) z = k • lam (cls L hL) x z := by
  have h := map_zpow (lamHom hL hΘ z) x k
  exact congrArg Multiplicative.toAdd h

theorem lam_prod_left : ∀ (n : ℕ) (x : Fin n → (T ⟶ G)) (e : Fin n → ℤ) (z : T ⟶ G),
    lam (cls L hL) (List.ofFn fun v => x v ^ e v).prod z = ∑ v, e v • lam (cls L hL) (x v) z
  | 0, x, e, z => by simp [lam_one_left]
  | n + 1, x, e, z => by
    rw [List.ofFn_succ, List.prod_cons, lam_mul_left hL hΘ, lam_zpow_left hL hΘ,
      lam_prod_left n (fun v => x v.succ) (fun v => e v.succ) z, Fin.sum_univ_succ]

theorem lam_prod_right (n : ℕ) (x : Fin n → (T ⟶ G)) (e : Fin n → ℤ) (z : T ⟶ G) :
    lam (cls L hL) z (List.ofFn fun v => x v ^ e v).prod = ∑ v, e v • lam (cls L hL) z (x v) := by
  rw [lam_comm, lam_prod_left hL hΘ]
  simp only [lam_comm _ z]

theorem lam_lam (p q : G' ⟶ G) [IsMonHom p] [IsMonHom q] (u v : T ⟶ G') :
    lam (lam (cls L hL) p q) u v = lam (cls L hL) (u ≫ p) (v ≫ q) + lam (cls L hL) (u ≫ q) (v ≫ p) := by
  have e : lam (lam (cls L hL) p q) u v = lamC u v (lam (cls L hL) p q) := rfl
  rw [e, show lam (cls L hL) p q = pull (p * q).left (cls L hL) - pull p.left (cls L hL) - pull q.left (cls L hL)
      + pull (1 : G' ⟶ G).left (cls L hL) from rfl, map_add, map_sub, map_sub]
  simp only [lamC_apply]
  rw [lam_pull_of (p * q) _ u v (by rw [MonObj.comp_mul, MonObj.mul_comp, MonObj.mul_comp, MonObj.comp_mul,
      MonObj.comp_mul, _root_.mul_mul_mul_comm]) (by rw [MonObj.comp_mul, MonObj.one_comp, MonObj.one_comp, _root_.mul_one]),
    lam_pull_of p _ u v (MonObj.mul_comp _ _ _) (MonObj.one_comp _),
    lam_pull_of q _ u v (MonObj.mul_comp _ _ _) (MonObj.one_comp _),
    lam_pull_of (1 : G' ⟶ G) _ u v (by rw [MonObj.comp_one, MonObj.comp_one, MonObj.comp_one, _root_.mul_one])
      (MonObj.comp_one _)]
  rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_one, MonObj.comp_one, lam_one_left,
    lam_mul_left hL hΘ, lam_mul_right' hL hΘ, lam_mul_right' hL hΘ]
  abel

end Bilinear

end GlobalTheory.E8AdjointPairing

namespace GlobalTheory.E8AdjointPairing

open GlobalTheory.CechPic

theorem alg_left {M : Type*} [AddCommGroup M] (S a : Matrix (Fin 8) (Fin 8) ℤ) (B : Fin 8 → Fin 8 → M) :
    ∑ i, ∑ j, S i j • ∑ v, a i v • B v j = ∑ v, ∑ j, (a.transpose * S) v j • B v j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  simp_rw [smul_comm (S _ _) (a _ _)]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

theorem alg_right {M : Type*} [AddCommGroup M] (S a' : Matrix (Fin 8) (Fin 8) ℤ) (B : Fin 8 → Fin 8 → M) :
    ∑ i, ∑ j, S i j • ∑ v, a' j v • B i v = ∑ i, ∑ v, (S * a') i v • B i v := by
  simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_comm

def precomp {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (h : T ⟶ T') : (T' ⟶ G) →* (T ⟶ G) where
  toFun y := h ≫ y
  map_one' := MonObj.comp_one h
  map_mul' := MonObj.comp_mul h

theorem comp_prod {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (h : T ⟶ T') :
    ∀ (n : ℕ) (x : Fin n → (T' ⟶ G)) (e : Fin n → ℤ),
      h ≫ (List.ofFn fun v => x v ^ e v).prod = (List.ofFn fun v => (h ≫ x v) ^ e v).prod
  | 0, x, e => by simp [MonObj.comp_one]
  | n + 1, x, e => by
    rw [List.ofFn_succ, List.prod_cons, MonObj.comp_mul, comp_prod h n, List.ofFn_succ, List.prod_cons]
    congr 1
    exact map_zpow (precomp (G := G) h) (x 0) (e 0)

theorem lbIso_cubeLB_adjoint : ∀ (K : Type) [Field K] (A A' : PolAV (Sp K)) (W : Matrix (Fin 8) (Fin 8) ℤ) (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (a a' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ (f f' : A'.A ⟶ A'.A), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → (∀ u, f' ≫ pr u = (List.ofFn fun v => pr v ^ a' u v).prod) → LBIso (cubeLB A'.A ![fst A'.A A'.A ≫ f, snd A'.A A'.A] A'.L) (cubeLB A'.A ![fst A'.A A'.A, snd A'.A A'.A ≫ f'] A'.L) := by
  intro K _ A A' W pr hpr hiso a a' hS f f' hf hf'
  haveI := A.isAb.comm
  obtain ⟨r, hr⟩ := A.rigid
  obtain ⟨cs⟩ := (GlobalTheory.firstFiveLaws.1.cube (Sp K) A ⟨A.L, r, A.isLB, hr⟩ rfl).1
  have hΘ : ∃ t : LB.Gen (Theta A.A A.L), t.IsGen := ⟨cs.t, cs.isGen⟩
  have hL := A.isLB
  have hL' := A'.isLB
  have hLam : (abelian₂ A.A A.L).IsLB := LB.isLB_linComb hL _ _
  have hLC := LB.isLB_linComb hLam (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2)
  have hcA : cls A'.L hL' = ∑ ab : Fin 8 × Fin 8, W ab.1 ab.2 • lam (cls A.L hL) (pr ab.1) (pr ab.2) := by
    rw [(cls_eq_iff hL' hLC).2 hiso, cls_linComb hLam]
    refine Finset.sum_congr rfl fun ab _ => ?_
    congr 1
    rw [show cls (abelian₂ A.A A.L) hLam = lam (cls A.L hL) (fst A.A A.A) (snd A.A A.A) from cls_cube_two hL _ _ _,
      pull_lam, lift_fst, lift_snd]
  have key : ∀ {T : Over (Sp K)} (u v : T ⟶ A'.A), lam (cls A'.L hL') u v =
      ∑ i, ∑ j, (W + W.transpose) i j • lam (cls A.L hL) (u ≫ pr i) (v ≫ pr j) := by
    intro T u v
    rw [← lamC_apply, hcA, map_sum]
    simp only [map_zsmul, lamC_apply, lam_lam hL hΘ, smul_add, Finset.sum_add_distrib, Matrix.add_apply,
      Matrix.transpose_apply, add_smul]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    congr 1
    exact Finset.sum_comm
  have h₁ : (cubeLB A'.A ![fst A'.A A'.A ≫ f, snd A'.A A'.A] A'.L).IsLB := LB.isLB_linComb hL' _ _
  have h₂ : (cubeLB A'.A ![fst A'.A A'.A, snd A'.A A'.A ≫ f'] A'.L).IsLB := LB.isLB_linComb hL' _ _
  refine (cls_eq_iff h₁ h₂).1 ?_
  rw [cls_cube_two hL', cls_cube_two hL', key, key]
  simp only [Category.assoc, hf, hf', comp_prod, lam_prod_left hL hΘ, lam_prod_right hL hΘ]
  refine (alg_left (W + W.transpose) a
    (fun v j => lam (cls A.L hL) (fst A'.A A'.A ≫ pr v) (snd A'.A A'.A ≫ pr j))).trans ?_
  rw [← hS]
  exact (alg_right (W + W.transpose) a'
    (fun i v => lam (cls A.L hL) (fst A'.A A'.A ≫ pr i) (snd A'.A A'.A ≫ pr v))).symm

end GlobalTheory.E8AdjointPairing
