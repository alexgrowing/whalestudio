import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.HermTensorLB

open GlobalTheory.CechPic

section Pairing

variable {S : Scheme.{0}} {G A T : Over S} [GrpObj G] [GrpObj A]

theorem lam_sum {I : Type} (s : Finset I) (c : I → Pic A.left) (x y : T ⟶ A) :
    lam (∑ i ∈ s, c i) x y = ∑ i ∈ s, lam (c i) x y := by
  simp only [lam, map_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]

variable [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

theorem lam_mul_right (x y z : T ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm _ y, lam_comm _ z]

theorem lam_lam (u v : A ⟶ G) [IsMonHom u] [IsMonHom v] (x y : T ⟶ A) :
    lam (lam (cls L hL) u v) x y =
      lam (cls L hL) (x ≫ u) (y ≫ v) + lam (cls L hL) (y ≫ u) (x ≫ v) := by
  rw [lam.eq_1 (lam (cls L hL) u v)]
  simp only [pull_lam, MonObj.mul_comp, MonObj.one_comp, lam_one_left, lam_mul_left hL hΘ,
    lam_mul_right hL hΘ]
  abel

end Pairing

theorem herm_expand {O : Type} [CommRing O] (bar : O →+* O) {M : Type} [AddCommGroup M] [Module O M]
    (h : M → M → O) (hadd : ∀ m m' n, h (m + m') n = h m n + h m' n)
    (hsmul : ∀ (c : O) m n, h (c • m) n = c * h m n) (hsym : ∀ m n, h n m = bar (h m n))
    (P : Summand O M) (m n : M) :
    h m n = ∑ i, ∑ j, P.incl m i * bar (P.incl n j) *
      h (P.proj (Pi.single i 1)) (P.proj (Pi.single j 1)) := by
  have hx : ∀ m : M, m = ∑ i, P.incl m i • P.proj (Pi.single i 1) := fun m => by
    have e : P.proj (P.incl m) = m := congr($(P.proj_incl) m)
    simp only [← map_smul, ← map_sum]
    rw [← pi_eq_sum_univ', e]
  have lin : ∀ m n : M, h m n = ∑ i, P.incl m i * h (P.proj (Pi.single i 1)) n := fun m n => by
    let f : M →+ O := AddMonoidHom.mk' (fun m => h m n) fun a b => hadd a b n
    have : f m = f (∑ i, P.incl m i • P.proj (Pi.single i 1)) := congrArg f (hx m)
    rw [map_sum] at this
    exact this.trans (Finset.sum_congr rfl fun i _ => hsmul _ _ _)
  rw [lin]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsym n, lin n, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← hsym, _root_.mul_assoc]

theorem exists_lb_hermitian : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (O : Type) [CommRing O] (bar : O →+* O) (M : Type) [AddCommGroup M] [Module O M] (h : M → M → O) [Module.Finite O M] [Module.Projective O M] (A : Over S) [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (t : IsTensor A b G a M) (w : O), L.IsLB → (∃ tθ : LB.Gen (Theta G L), tθ.IsGen) → (∀ c, LBIso (cubeLB G ![fst G G ≫ a.act c, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ a.act (bar c)] L)) → ((∀ c, bar (bar c) = c) ∧ (∀ m m' n, h (m + m') n = h m n + h m' n) ∧ (∀ (c : O) m n, h (c • m) n = c * h m n) ∧ ∀ m n, h n m = bar (h m n)) → w + bar w = 1 → ∃ N : LB A.left, N.IsLB ∧ (∃ tθ : LB.Gen (Theta A N), tθ.IsGen) ∧ (∀ m n, LBIso (cubeLB A ![fst G G ≫ t.tmul m, snd G G ≫ t.tmul n] N) (cubeLB G ![fst G G ≫ a.act (h m n), snd G G] L)) := by
  intro S G _ _ L O _ bar M _ _ h _ _ A _ _ a b t w hL hΘ hadj ⟨hbar, hadd, hsmul, hsym⟩ hw
  let P := Summand.choose O M
  let e : Fin P.n → M := fun i => P.proj (Pi.single i 1)
  let p : Fin P.n → (A ⟶ G) := fun i => t.mapLeft (IsTensor.self a) (LinearMap.proj i ∘ₗ P.incl)
  have hp : ∀ m i, t.tmul m ≫ p i = a.act (P.incl m i) := fun m i => by
    simp [p]
  have pm : ∀ i, IsMonHom (p i) := fun i => IsTensor.isMonHom_mapLeft _ _ _
  have am := a.hom
  have adj : ∀ {T : Over S} (x y : T ⟶ G) (c : O),
      lam (cls L hL) (x ≫ a.act c) y = lam (cls L hL) x (y ≫ a.act (bar c)) := by
    intro T x y c
    have h₀ := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (hadj c)
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hL _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
  obtain ⟨N, hN, hc⟩ := cls_surj
    (∑ i, ∑ j, lam (cls L hL) (p i ≫ a.act (h (e i) (e j))) (p j ≫ a.act w))
  have key : ∀ {T : Over S} (x y : T ⟶ A), lam (cls N hN) x y =
      ∑ i, ∑ j, (lam (cls L hL) (x ≫ p i ≫ a.act (h (e i) (e j))) (y ≫ p j ≫ a.act w) +
        lam (cls L hL) (y ≫ p i ≫ a.act (h (e i) (e j))) (x ≫ p j ≫ a.act w)) := by
    intro T x y
    rw [hc, lam_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lam_sum]
    exact Finset.sum_congr rfl fun j _ => lam_lam hL hΘ _ _ x y
  refine ⟨N, hN, ?_, fun m n => ?_⟩
  · refine (cls_eq_zero_iff (N := Theta A N) (LB.isLB_linComb hN _ _)).1 ?_
    refine (cls_cube_three hN (fst _ _) (snd _ _ ≫ fst _ _) (snd A (A ⊗ A) ≫ snd _ _)
      (LB.isLB_linComb hN _ _)).trans ?_
    rw [sub_sub, sub_eq_zero, key, key, key]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [MonObj.mul_comp, MonObj.mul_comp, lam_mul_left hL hΘ, lam_mul_right hL hΘ]
    abel
  · refine (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hL _ _)).1 ?_
    refine (cls_cube_two hN _ _ _).trans (Eq.trans ?_ (cls_cube_two hL _ _ _).symm)
    let φ : O →+ Pic (G ⊗ G).left := AddMonoidHom.mk'
      (fun c => lam (cls L hL) (fst G G ≫ a.act c) (snd G G)) fun c d => by
        simp only [a.add, MonObj.comp_mul, lam_mul_left hL hΘ]
    have hφ : ∀ c d, lam (cls L hL) (fst G G ≫ a.act c) (snd G G ≫ a.act d) = φ (c * bar d) := by
      intro c d
      have := adj (fst G G ≫ a.act c) (snd G G) (bar d)
      rw [hbar, Category.assoc, ← a.mul] at this
      exact this.symm
    have hq : ∀ m i c, t.tmul m ≫ p i ≫ a.act c = a.act (P.incl m i * c) := fun m i c => by
      rw [← Category.assoc, hp, a.mul]
    rw [key]
    simp only [Category.assoc, hq, lam_comm _ (snd G G ≫ _), hφ, ← map_add, ← map_sum]
    change _ = φ (h m n)
    congr 1
    have E := herm_expand bar h hadd hsmul hsym P m n
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => P.incl m j * w * bar (P.incl n i * h (e i) (e j))),
      ← _root_.mul_one (h m n), ← hw, mul_add, add_comm, E]
    simp only [Finset.sum_mul, map_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← hsym]; ring
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring

end GlobalTheory.HermTensorLB
