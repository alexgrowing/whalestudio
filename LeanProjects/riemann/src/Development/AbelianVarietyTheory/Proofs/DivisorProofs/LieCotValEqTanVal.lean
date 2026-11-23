import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

def sqToEps {M S : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    [CommRing S] [Algebra R S] (k : M →ₗ[R] S) : TrivSqZeroExt R M →ₐ[R] DualNumber S where
  toFun z := (algebraMap R S z.fst, k z.snd)
  map_one' := TrivSqZeroExt.ext (map_one (algebraMap R S)) (map_zero k)
  map_mul' a b := TrivSqZeroExt.ext (map_mul (algebraMap R S) _ _) (by
    change k (a.fst • b.snd + MulOpposite.op b.fst • a.snd) =
      algebraMap R S a.fst * k b.snd + k a.snd * algebraMap R S b.fst
    rw [op_smul_eq_smul, map_add, map_smul, map_smul, Algebra.smul_def, Algebra.smul_def,
      mul_comm (k a.snd)])
  map_zero' := TrivSqZeroExt.ext (map_zero (algebraMap R S)) (map_zero k)
  map_add' a b := TrivSqZeroExt.ext (map_add (algebraMap R S) _ _) (map_add k _ _)
  commutes' _ := TrivSqZeroExt.ext rfl (map_zero k)

attribute [local instance] cotOp cotCentral cotTower

theorem tanDer_cotVal {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R} (t : G.TorsionTower A)
    (β : Form (A.hom ≫ 𝟙 _)) {v : epsR R ⟶ A} (hv : IsTangent v) (n : ℕ) :
    t.tanDer hv n (cotVal β.1 (t.y n)) = algebraMap R (ModPow p R n) (tanVal v β) := by
  let S := ModPow p R n
  let E : SqExt R := SqExt.ofModule R S S
  let ρ : (cotExt R (G.A n)).C →ₐ[R] DualNumber S := sqToEps (t.tanDer hv n)
  let y' : Pt A (cotExt R (G.A n)).C := spOver (cotPt R (G.A n)) ≫ t.y n
  have hρ : ρ.comp (cotPt R (G.A n)) = t.tanPt hv n := AlgHom.ext fun a ↦ by
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [t.fst_tanPt]
      exact congrArg (algebraMap R S) (add_zero _)
    · rw [← t.tanDer_d]
      exact congrArg (t.tanDer hv n) (zero_add _)
  have e : spOver ρ ≫ y' = epsRedPow p n v := by
    rw [← Category.assoc, spOver_comp, hρ, t.tanPt_y]
  have k1 := (cotExt R (G.A n)).val_map E ρ (Algebra.ofId R S) (fun _ ↦ rfl)
    (fun _ ↦ TrivSqZeroExt.ext rfl (map_zero (t.tanDer hv n))) y'.left y'.w _
    (Pt.w (epsRedPow p n v)) (congrArg Over.Hom.left e) β
  have k2 := (SqExt.dual R).val_map E (epsTo R S) (Algebra.ofId R S) (fun c ↦ (fst_epsTo S c).symm)
    (fun c ↦ TrivSqZeroExt.ext (fst_epsTo S _) ((snd_epsTo S _).trans (map_zero _))) v.left (pt_w v) _
    (Pt.w (epsRedPow p n v)) rfl β
  have h0 : fv β.1 (G.A n) (cotExt R (G.A n)).C (cotPt R (G.A n)) (t.y n) = 0 := β.2 _ rfl rfl
  have k3 := congrArg TrivSqZeroExt.snd (k1.symm.trans k2)
  rw [snd_epsTo] at k3
  refine Eq.trans ?_ k3
  change t.tanDer hv n (cotSnd R _ (_ - fv β.1 (G.A n) (cotExt R (G.A n)).C (cotPt R (G.A n)) (t.y n))) = _
  rw [h0, sub_zero]
  rfl

theorem lie_cotVal_eq_tanVal : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A), IsNilpotent (p : R) → ∀ (β : Form (A.hom ≫ 𝟙 _)) (w : G.omega), (∀ n, w.1 n = cotVal β.1 (t.y n)) → ∀ (x : G.Lie) (v : epsR R ⟶ A), t.LieCorr x v → x w = tanVal v β := by
  intro R _ A _ p G t ⟨n, hn⟩ β w hw x v h
  have h1 := (t.lieCorr_iff h.1 x).1 h n w
  rw [hw, tanDer_cotVal] at h1
  have h2 := Ideal.Quotient.eq.1 h1
  rw [hn, Ideal.mem_span_singleton, zero_dvd_iff] at h2
  exact sub_eq_zero.1 h2

end GlobalTheory.PtExt
