import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSharpBasisSharpBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.Sep.E8Fibration.Lab

def postHom {S : Scheme.{0}} (T : Over S) {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] :
    (T ⟶ A) →* (T ⟶ B) where
  toFun x := x ≫ f
  map_one' := by simp
  map_mul' x y := by simp [MonObj.mul_comp]

def preHom {S : Scheme.{0}} {T A : Over S} (x : T ⟶ A) (B : Over S) [GrpObj B] :
    (A ⟶ B) →* (T ⟶ B) where
  toFun y := x ≫ y
  map_one' := by simp
  map_mul' y z := by simp [MonObj.comp_mul]

theorem zpow_finset_sum {G J : Type} [CommGroup G] (g : G) (s : Finset J) (e : J → ℤ) :
    g ^ (∑ i ∈ s, e i) = ∏ i ∈ s, g ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

theorem prod_prod_zpow {G C J : Type} [CommGroup G] [Fintype C] [Fintype J] (b : C → G) (x : J → C → ℤ) (k : J → ℤ) :
    ∏ i, (∏ c, b c ^ x i c) ^ k i = ∏ c, b c ^ (∑ i, k i * x i c) := by
  simp only [← Finset.prod_zpow, ← zpow_mul, zpow_finset_sum]
  rw [Finset.prod_comm]
  simp only [mul_comm]

theorem pow_val_intCast {G : Type} [Group G] {N : ℕ} (hN : 0 < N) {g : G} (hg : g ^ N = 1) (k : ℤ) :
    g ^ ((k : ZMod N)).val = g ^ k := by
  haveI : NeZero N := ⟨hN.ne'⟩
  rw [← zpow_natCast, ZMod.val_intCast]
  exact (zpow_eq_zpow_emod' k hg).symm

theorem prod_zpow_pow_eq_one {G C : Type} [CommGroup G] [Fintype C] {N : ℕ} {b : C → G} (hb : ∀ c, b c ^ N = 1)
    (x : C → ℤ) : (∏ c, b c ^ x c) ^ N = 1 := by
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun c _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]

theorem sum_labMat_mul (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) (a : Fin 2)
    (i : Fin (2 * (8 * h))) (u : Fin 8) (c : Fin h ⊕ Fin h) :
    ∑ i', labMat W hW h a i' i * sharpBasis W hW h (Pi.single i' 1) u c =
      ∑ v, actMat W a u v * sharpBasis W hW h (Pi.single i 1) v c := by
  have key : ∀ y : Fin (2 * (8 * h)) → ℤ,
      ∑ i', y i' * sharpBasis W hW h (Pi.single i' 1) u c = sharpBasis W hW h y u c := by
    intro y
    conv_rhs => rw [pi_eq_sum_univ' y]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact (key _).trans (congrFun (congrFun ((sharpBasis W hW h).apply_symm_apply _) u) c)

theorem ptOf_torsion_and_act : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) (gQ : ℕ) {S : Scheme.{0}} (A B : Over S) [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)) (hP : E8Fibration.IsProd pr) (N : ℕ) {T : Over S}
  (b : Fin gQ ⊕ Fin gQ → (T ⟶ B)), (∀ c, b c ^ N = 1) → 0 < N →
  (∀ i, E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ^ N = 1) ∧
  ∀ (act : Fin 2 → (A ⟶ A)), (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) → ∀ (a : Fin 2) (i : Fin (2 * (8 * gQ))),
    E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ≫ act a =
      Out.linComb (fun i' => E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1)))
        (fun i' => ((E8Fibration.Lab.labMat W hW.2 gQ a i' i : ZMod N)).val) := by
  intro W hW gQ S A B _ _ _ _ pr hP N T b hb hN
  have ext : ∀ x y : T ⟶ A, (∀ u, x ≫ pr u = y ≫ pr u) → x = y := fun x y h =>
    (hP.2 T fun u => y ≫ pr u).unique h fun _ => rfl
  refine ⟨fun i => ext _ _ fun u => ?_, fun act hact a i => ext _ _ fun u => ?_⟩
  · haveI := hP.1 u
    have := map_pow (postHom T (pr u)) (ptOf hP b (sharpBasis W hW.2 gQ (Pi.single i 1))) N
    refine this.trans ?_
    change (ptOf hP b _ ≫ pr u) ^ N = _
    rw [ptOf_pr, prod_zpow_pow_eq_one hb]
    exact (map_one (postHom T (pr u))).symm
  · haveI := hP.1 u
    have h1 : (ptOf hP b (sharpBasis W hW.2 gQ (Pi.single i 1)) ≫ act a) ≫ pr u =
        ∏ c, b c ^ (∑ v, actMat W a u v * sharpBasis W hW.2 gQ (Pi.single i 1) v c) := by
      rw [Category.assoc, hact a u, ← prod_prod_zpow]
      refine (map_prod (preHom (ptOf hP b (sharpBasis W hW.2 gQ (Pi.single i 1))) B) _ _).trans ?_
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_zpow, ← ptOf_pr hP]
      rfl
    rw [h1, Out.linComb, List.prod_ofFn]
    refine Eq.trans ?_ (map_prod (postHom T (pr u)) _ _).symm
    simp only [← sum_labMat_mul W hW.2 gQ a i u]
    rw [← prod_prod_zpow]
    refine Finset.prod_congr rfl fun i' _ => ?_
    rw [map_pow, ← pow_val_intCast hN (prod_zpow_pow_eq_one hb _), ← ptOf_pr hP]
    rfl

end GlobalTheory.Poinc.Sep.E8Fibration.Lab
end
