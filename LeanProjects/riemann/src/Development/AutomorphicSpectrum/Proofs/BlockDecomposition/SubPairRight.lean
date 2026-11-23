import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

variable {X : Scheme.{0}}

def secMulOn {N : LB X} {a b c : ℤ} (h : a + b = c) {V : X.Opens} (x : SecOn (pw N a) V)
    (y : SecOn (pw N b) V) : SecOn (pw N c) V :=
  GlobalTheory.LB.mkSec (L := pw N c) (fun i => @HMul.hMul (Γ(X, V ⊓ N.U i)) (Γ(X, V ⊓ N.U i)) _ _ (GlobalTheory.LB.coord x i) (GlobalTheory.LB.coord y i)) (fun i j => by
    have hx := GlobalTheory.LB.coord_rel x i j (W := V ⊓ N.U i ⊓ N.U j) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    have hy := GlobalTheory.LB.coord_rel y i j (W := V ⊓ N.U i ⊓ N.U j) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    subst h
    have e : ((N.g i j ^ (a + b) : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) =
        ((N.g i j ^ a : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) *
          ((N.g i j ^ b : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) := by
      rw [zpow_add, Units.val_mul]
    erw [map_mul, map_mul]
    erw [hx, hy, e, map_mul]
    rw [show (AbLaw.pw N a).g i j = N.g i j ^ a from rfl, show (AbLaw.pw N b).g i j = N.g i j ^ b from rfl]
    exact mul_mul_mul_comm _ _ _ _)

@[simp] theorem coord_secMulOn {N : LB X} {a b c : ℤ} (h : a + b = c) {V : X.Opens}
    (x : SecOn (pw N a) V) (y : SecOn (pw N b) V) (i : N.ι) :
    GlobalTheory.LB.coord (secMulOn h x y) i =
      @HMul.hMul (Γ(X, V ⊓ N.U i)) (Γ(X, V ⊓ N.U i)) _ _ (GlobalTheory.LB.coord x i) (GlobalTheory.LB.coord y i) := rfl

end GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

variable {X : Scheme.{0}} {R : Type} [CommRing R]

def mulRight (f : X ⟶ Spec (CommRingCat.of R)) {N : LB X} {a b c : ℤ} (h : a + b = c)
    {V : X.Opens} (y : SecOn (pw N b) V) : SecOnR f (pw N a) V →ₗ[R] SecOnR f (pw N c) V where
  toFun x := SecOnR.of f _ V (secMulOn h ((SecOnR.of f _ V).symm x) y)
  map_add' x x' := GlobalTheory.LB.sec_ext fun (i : N.ι) => add_mul (R := Γ(X, V ⊓ N.U i)) _ _ _
  map_smul' r x := GlobalTheory.LB.sec_ext fun (i : N.ι) => mul_assoc (G := Γ(X, V ⊓ N.U i)) _ _ _

theorem coord_mulRight (f : X ⟶ Spec (CommRingCat.of R)) {N : LB X} {a b c : ℤ} (h : a + b = c)
    {V : X.Opens} (y : SecOn (pw N b) V) (x : SecOnR f (pw N a) V) (i : N.ι) :
    SecOnR.coord (mulRight f h y x) i =
      @HMul.hMul (Γ(X, V ⊓ N.U i)) (Γ(X, V ⊓ N.U i)) _ _ (SecOnR.coord x i) (GlobalTheory.LB.coord y i) :=
  rfl

def oneOn (N : LB X) {a : ℤ} (h : a = 0) (V : X.Opens) : SecOn (pw N a) V :=
  GlobalTheory.LB.mkSec (L := pw N a) (fun _ => 1) (fun i j => by
    subst h
    rw [map_one, map_one, show (AbLaw.pw N 0).g i j = N.g i j ^ (0 : ℤ) from rfl, zpow_zero,
      Units.val_one]
    erw [map_one, one_mul])

section Tower

variable (I : Ideal R)

abbrev toR (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (e : ℕ) :
    (Y e).left ⟶ Spec (CommRingCat.of R) :=
  (Y e).hom ≫ thick R I e

theorem toR_w (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (e : ℕ) :
    β e ≫ toR I Y (e + 1) =
      toR I Y e ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, toR, toR, ← Category.assoc, (hβ e).w,
    Category.assoc, thickTrans_comp]

variable {ι : Type} (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (N : ∀ e, LB (Y e).left) (D : ∀ e, Finset ι → (Y e).left.Opens) (d : ℤ)

abbrev Tm (e : ℕ) (t : ℤ) (S : Finset ι) : Type :=
  SecOnR (toR I Y e) (pw (N e) (d * t)) (D e S)

def resT (hD : ∀ e (S S' : Finset ι), S ⊆ S' → D e S' ≤ D e S) (e : ℕ) (t : ℤ) {S S' : Finset ι}
    (h : S ⊆ S') : Tm I Y N D d e t S →ₗ[R] Tm I Y N D d e t S' :=
  SecOnR.restrict (toR I Y e) _ (hD e S S' h)

def mulT (e : ℕ) (t : ℤ) (S : Finset ι) (σ : SecOn (pw (N e) d) (D e S)) :
    Tm I Y N D d e t S →ₗ[R] Tm I Y N D d e (t + 1) S :=
  mulRight (toR I Y e) (by ring) σ

theorem mulT_comm (e : ℕ) (t : ℤ) (S : Finset ι) (σ τ : SecOn (pw (N e) d) (D e S))
    (x : Tm I Y N D d e t S) :
    mulT I Y N D d e (t + 1) S σ (mulT I Y N D d e t S τ x) =
      mulT I Y N D d e (t + 1) S τ (mulT I Y N D d e t S σ x) := by
  refine SecOnR.ext_iff.mpr fun i => ?_
  unfold mulT
  first
  | (erw [coord_mulRight, coord_mulRight, coord_mulRight, coord_mulRight]; exact mul_right_comm _ _ _)
  | (simp only [coord_mulRight]; exact mul_right_comm _ _ _)
  | (simp only [coord_mulRight]; ring)

def oneT (e : ℕ) (S : Finset ι) : Tm I Y N D d e 0 S :=
  SecOnR.of _ _ _ (oneOn (N e) (mul_zero d) (D e S))

def redL (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
    (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V : (Y (e + 1)).left.Opens)
    (V' : (Y e).left.Opens) (h : V' ≤ β e ⁻¹ᵁ V) :
    SecOnR (toR I Y (e + 1)) (L (e + 1)) V →ₗ[R] SecOnR (toR I Y e) (L e) V' :=
  (SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 V')).symm.toLinearMap ∘ₗ SecOnR.pull (L (e + 1)) (toR_w I Y β hβ e) V V' h

def red (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e)))
    (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen)
    (hDβ : ∀ e (S : Finset ι), D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a : ℤ) (e : ℕ) (S : Finset ι) :
    SecOnR (toR I Y (e + 1)) (pw (N (e + 1)) a) (D (e + 1) S) →ₗ[R]
      SecOnR (toR I Y e) (pw (N e) a) (D e S) :=
  redL I Y β hβ (fun e => pw (N e) a) (fun e => pullPow (v e) a)
    (fun e => ⟨isLB_pw (hN e).1 a, pullPow_isGen (v e) a (hN e).2⟩) e (D (e + 1) S) (D e S) (hDβ e S)

end Tower

section Sub

variable {ι : Type} [DecidableEq ι]

theorem sub_pair_left (i j : ι) : ({i} : Finset ι) ⊆ {i, j} :=
  Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _)

theorem sub_pair_right (i j : ι) : ({j} : Finset ι) ⊆ {i, j} :=
  Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

theorem sub_triple_ij (i j k : ι) : ({i, j} : Finset ι) ⊆ {i, j, k} := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

theorem sub_triple_jk (i j k : ι) : ({j, k} : Finset ι) ⊆ {i, j, k} := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

theorem sub_triple_ik (i j k : ι) : ({i, k} : Finset ι) ⊆ {i, j, k} := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

end Sub

end GlobalTheory.CompanionTheory.FormalAlg.Lift
