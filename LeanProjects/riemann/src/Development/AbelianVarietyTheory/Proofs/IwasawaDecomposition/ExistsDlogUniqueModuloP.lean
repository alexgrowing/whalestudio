import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv tv_add tv_zero tv_smul)

namespace GlobalTheory.DlogEx

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {O : Type} [CommRing O] {x : Sp O ⟶ X} (R : Type) [CommRing R] [Algebra O R]

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

variable (x) in

def redEps : Over.mk (spMap (algebraMap O (DualNumber R)) ≫ x) ⟶ overAt x (DualNumber O) :=
  Over.homMk (spMap (dualMap (algebraMap O R))) (by
    show spMap (dualMap (algebraMap O R)) ≫ spMap (algebraMap O (DualNumber O)) ≫ x =
      spMap (algebraMap O (DualNumber R)) ≫ x
    rw [← Category.assoc, sp_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl'])

def red (v : TanM x t.G) : Over.mk (spMap (algebraMap O (DualNumber R)) ≫ x) ⟶ t.G := redEps x R ≫ tv v

theorem red_left (v : TanM x t.G) : (red R v).left = spMap (dualMap (algebraMap O R)) ≫ (tv v).left := rfl

theorem red_add (v w : TanM x t.G) : red R (v + w) = red R v * red R w := MonObj.comp_mul _ _ _

theorem red_zero : red R (0 : TanM x t.G) = 1 := MonObj.comp_one _

def epsAlg (a : R) : DualNumber R →ₐ[O] DualNumber R :=
  (TrivSqZeroExt.map (a • LinearMap.id : R →ₗ[R] R)).restrictScalars O

theorem red_smul (a : O) (v : TanM x t.G) :
    (red R (a • v)).left = spMap (epsAlg (O := O) R (algebraMap O R a)).toRingHom ≫ (red R v).left := by
  show spMap (dualMap (algebraMap O R)) ≫ spMap (epsMul a) ≫ (tv v).left =
    spMap _ ≫ spMap (dualMap (algebraMap O R)) ≫ (tv v).left
  rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
  congr 2
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap, epsMul, epsAlg, -Algebra.smul_def, mul_smul]

theorem red_nsmul (k : ℕ) (v : TanM x t.G) : red R (k • v) = red R v ^ k := by
  induction k with
  | zero => rw [zero_nsmul, red_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, red_add, ih, pow_succ]

theorem red_pow {q : ℕ} (hq : (q : R) = 0) (v : TanM x t.G) : red R v ^ q = 1 := by
  rw [← red_nsmul, ← Nat.cast_smul_eq_nsmul O, ← red_zero R, ← zero_smul O v]
  refine Over.OverMorphism.ext ?_
  rw [red_smul, red_smul, map_natCast, hq, map_zero]

variable [Module.Finite O (DualNumber R)] {q : ℕ} (hq : (q : R) = 0) (c : TorsChar t x q)

include hq

theorem chi_smul (a : O) (v : TanM x t.G) :
    (c.χ _ (red R (a • v)) : DualNumber R) = epsAlg (O := O) R (algebraMap O R a) (c.χ _ (red R v)) :=
  c.nat _ _ _ _ _ (red_pow R hq v) (red_smul R a v)

theorem chi_add (v w : TanM x t.G) : c.χ _ (red R (v + w)) = c.χ _ (red R v) * c.χ _ (red R w) := by
  rw [red_add]
  exact c.mul _ _ _ (red_pow R hq v) (red_pow R hq w)

theorem chi_zero : c.χ _ (red R (0 : TanM x t.G)) = 1 := by
  have h := chi_add R hq c 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem chi_fst (v : TanM x t.G) : (c.χ _ (red R v) : DualNumber R).fst = 1 := by
  have h := congrArg TrivSqZeroExt.fst (chi_smul R hq c 0 v)
  rw [zero_smul, chi_zero R hq c] at h
  simpa [epsAlg] using h.symm

def dlog : TanM x t.G →ₗ[O] R where
  toFun v := (c.χ _ (red R v) : DualNumber R).snd
  map_add' v w := by
    rw [chi_add R hq c, Units.val_mul, TrivSqZeroExt.snd_mul, chi_fst R hq c, chi_fst R hq c]
    simp [add_comm]
  map_smul' a v := by
    rw [chi_smul R hq c]
    simp [epsAlg, Algebra.smul_def]

omit hq

theorem dlog_exists_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (O : Type) [CommRing O] (x : Sp O ⟶ X) (p n : ℕ) (c : TorsChar t x (p ^ n)) (g : ℕ) (e : Fin g → (Sp (DualNumber O) ⟶ t.G.left)), (∀ i, IsTanAtG t x (e i)) → (∃ h : Fin g → O, DlogIs t p n c e h) ∧ ∀ h h' : Fin g → O, DlogIs t p n c e h → DlogIs t p n c e h' → ∀ i, h i - h' i ∈ Ideal.span {(p : O) ^ n} := by
  intro E _ _ _ H X t O _ x p n c g e he
  classical
  have hq : ((p ^ n : ℕ) : O ⧸ Ideal.span {(p : O) ^ n}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : O) ^ n})), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.mem_span_singleton_self _
  constructor
  · choose h hh using fun i => Ideal.Quotient.mk_surjective (dlog _ hq c (LieMet.tanOf (he i)))
    refine ⟨h, fun a v hv w hw => ?_⟩
    have h1 := (LieMet.isComb_iff (fun i => LieMet.tanOf (he i)) a _).2 rfl
    have h2 : (tv (∑ i, a i • LieMet.tanOf (he i))).left = v :=
      ((isCombAtG_iff t x (fun j => ovT (he j)) a _).1 h1).symm.trans ((isCombAtG_iff t x (fun j => ovT (he j)) a _).1 hv)
    have h3 : w = red _ (∑ i, a i • LieMet.tanOf (he i)) := Over.OverMorphism.ext (by rw [hw, red_left, h2])
    rw [h3]
    show dlog _ hq c _ = _
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← hh, mul_comm]
    rfl
  · intro h h' hh hh' i
    have h1 := hh _ _ (isCombAtG_single t x he i) (red _ (LieMet.tanOf (he i))) rfl
    have h2 := hh' _ _ (isCombAtG_single t x he i) (red _ (LieMet.tanOf (he i))) rfl
    rw [← Ideal.Quotient.eq]
    simpa [Pi.single_apply] using h1.symm.trans h2

end GlobalTheory.DlogEx
