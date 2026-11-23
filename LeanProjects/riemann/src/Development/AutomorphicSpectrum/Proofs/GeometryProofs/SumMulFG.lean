import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ScaleGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

variable {X : Scheme.{0}}

structure FG (M : LB X) (Y : Scheme.{0}) where

  K : Type
  [fin : Fintype K]

  φ : K → (Y ⟶ X)

  ε : K → ℤ

  t : LB.Gen (LB.LinComb M φ ε)
  ht : t.IsGen

attribute [instance] FG.fin

namespace FG

variable {M : LB X} {Y Y' Z : Scheme.{0}}

def sum (a : FG M Y) (U : Type) [CommGroup U] (h : (Y ⟶ X) → U) : U := ∏ k, h (a.φ k) ^ a.ε k

def v (a : FG M Y) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) : (Z.presheaf.stalk z)ˣ := val a.t r z J

def one : FG M Y := ⟨PEmpty, PEmpty.elim, PEmpty.elim, LB.oneGen M, fun _ _ => (map_one _).trans
  ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm⟩

def mul (a b : FG M Y) : FG M Y :=
  ⟨a.K ⊕ b.K, Sum.elim a.φ b.φ, Sum.elim a.ε b.ε, LB.mulGen M _ _ _ _ a.t b.t,
    DVR.mulGen_isGen _ _ _ _ _ _ _ a.ht b.ht⟩

def inv (a : FG M Y) : FG M Y := ⟨a.K, a.φ, fun k => -a.ε k, LB.invGen M _ _ a.t, DVR.invGen_isGen _ _ _ _ a.ht⟩

def pull (a : FG M Y) (h : Y' ⟶ Y) : FG M Y' :=
  ⟨a.K, fun k => h ≫ a.φ k, a.ε, LB.pullGen M _ _ a.t h, DVR.pullGen_isGen _ _ _ _ a.ht h⟩

def pow (a : FG M Y) (n : ℕ) : FG M Y := Nat.rec one (fun _ b => b.mul a) n

theorem pow_zero' (a : FG M Y) : a.pow 0 = one := rfl

theorem pow_succ' (a : FG M Y) (n : ℕ) : a.pow (n + 1) = (a.pow n).mul a := rfl

variable (U : Type) [CommGroup U]

@[simp] theorem sum_one (h : (Y ⟶ X) → U) : (one : FG M Y).sum U h = 1 := by
  show ∏ k : PEmpty, _ = _
  exact Fintype.prod_empty _

@[simp] theorem sum_mul (a b : FG M Y) (h : (Y ⟶ X) → U) : (a.mul b).sum U h = a.sum U h * b.sum U h :=
  Fintype.prod_sum_type _

@[simp] theorem sum_inv (a : FG M Y) (h : (Y ⟶ X) → U) : a.inv.sum U h = (a.sum U h)⁻¹ :=
  (Finset.prod_congr rfl fun k _ => zpow_neg _ _).trans (Finset.prod_inv_distrib _)

@[simp] theorem sum_pull (a : FG M Y) (g : Y' ⟶ Y) (h : (Y' ⟶ X) → U) :
    (a.pull g).sum U h = a.sum U (fun q => h (g ≫ q)) := rfl

@[simp] theorem sum_pow (a : FG M Y) (n : ℕ) (h : (Y ⟶ X) → U) : (a.pow n).sum U h = a.sum U h ^ n := by
  induction n with
  | zero => simp [pow_zero']
  | succ n ih => simp [pow_succ', ih, pow_succ]

variable {z : Z} {J : (Z ⟶ X) → M.ι}

@[simp] theorem v_one (r : Z ⟶ Y) : (one : FG M Y).v r z J = 1 := val_one r

theorem v_mul (hJ : Good M z J) (a b : FG M Y) (r : Z ⟶ Y) : (a.mul b).v r z J = a.v r z J * b.v r z J :=
  val_mul hJ _ _ r

@[simp] theorem v_inv (a : FG M Y) (r : Z ⟶ Y) : a.inv.v r z J = (a.v r z J)⁻¹ := val_inv _ r

theorem v_pull (hJ : Good M z J) (a : FG M Y) (h : Y' ⟶ Y) (r : Z ⟶ Y') : (a.pull h).v r z J = a.v (r ≫ h) z J :=
  val_pull hJ _ h r

theorem v_pow (hJ : Good M z J) (a : FG M Y) (n : ℕ) (r : Z ⟶ Y) : (a.pow n).v r z J = a.v r z J ^ n := by
  induction n with
  | zero => simp [pow_zero']
  | succ n ih => rw [pow_succ', v_mul hJ, ih, pow_succ]

theorem exists_unit (hM : M.IsLB) (a : FG M Y) (h : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), a.sum U h = 1) :
    ∃ e : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J → a.v r z J = gm r z ⊤ e := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ := a.φ) (ε := a.ε) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ k => (h U k).trans (Fintype.prod_empty _).symm) a.t a.ht
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s (PEmpty.elim : PEmpty → M.ι)), fun Z r z J hJ => ?_⟩
  exact ((hv Z r z J hJ).symm.trans (val_of t r z J PEmpty.elim (fun k => k.elim))).trans (gm_res r z le trivial _).symm

theorem v_const (hM : M.IsLB) (a : FG M Y) (h : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), a.sum U h = 1)
    {S₀ : Scheme.{0}} (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom) {r r' : Z ⟶ Y} (e : r ≫ p = r' ≫ p)
    (hJ : Good M z J) : a.v r z J = a.v r' z J := by
  obtain ⟨c, hc⟩ := exists_unit hM a h
  obtain ⟨b, hb⟩ := hp c.val
  have key : ∀ r : Z ⟶ Y, (a.v r z J).val = gs (r ≫ p) z ⊤ b := fun r => by
    rw [hc Z r z J hJ, ← gs_unit r z ⊤ trivial, ← hb]
    exact gs_pull r p z ⊤ trivial b
  exact Units.ext ((key r).trans (by rw [e]; exact (key r').symm))

end FG

end GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

section Pts
variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem left_pow {T : Over S} (a : T ⟶ G) (N : ℕ) : a.left ≫ ((𝟙 G : G ⟶ G) ^ N).left = (a ^ N).left := by
  rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]

theorem one_left (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ eSec G := by
  have e : (1 : T ⟶ G) = toUnit T ≫ η[G] := Hom.one_def
  rw [e, Over.comp_left, eSec]
  congr 1

end Pts

def rigFG {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : RigLB G) : FG P.L (𝟙_ (Over S)).left :=
  ⟨PUnit, fun _ => eSec G, fun _ => 1, P.rig, P.rigGen⟩

@[simp] theorem sum_rigFG {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : RigLB G) (U : Type) [CommGroup U]
    (h : ((𝟙_ (Over S)).left ⟶ G.left) → U) : (rigFG P).sum U h = h (eSec G) := by
  show ∏ _k : PUnit, h (eSec G) ^ (1 : ℤ) = _
  simp

def mulFG {S : Scheme.{0}} {G : Over S} [GrpObj G] {M : LB G.left} {N : ℕ}
    (w : LB.Gen (LB.LinComb M (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)])) (hw : w.IsGen) :
    FG M G.left := ⟨Fin 2, _, _, w, hw⟩

theorem sum_mulFG {S : Scheme.{0}} {G : Over S} [GrpObj G] {M : LB G.left} {N : ℕ}
    (w : LB.Gen (LB.LinComb M (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)])) (hw : w.IsGen)
    (U : Type) [CommGroup U] (h : (G.left ⟶ G.left) → U) :
    (mulFG w hw).sum U h = h ((𝟙 G : G ⟶ G) ^ N).left * (h (𝟙 G.left) ^ (N ^ 2))⁻¹ := by
  show ∏ k : Fin 2, h ((![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] : Fin 2 → _) k) ^ (![1, -((N : ℤ) ^ 2)] : Fin 2 → ℤ) k = _
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg]
  norm_cast

end GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl
theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap (f.comp g) = spMap f ≫ spMap g := by
  show Spec.map (CommRingCat.ofHom (f.comp g)) = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem gc_spMap {R : Type} [CommRing R] {F : Type} [Field F] (g : R →+* F) (z : Sp F) (t : R) :
    GlobalTheory.TwistLoc.gc (spMap g) z t = toStk z (g t) := by
  show gs (spMap g) z ⊤ _ = _
  rw [gs_eq _ z ⊤ trivial]
  show _ = ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (g t))
  exact congrArg _ (congrArg (fun φ => φ.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))).symm

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
