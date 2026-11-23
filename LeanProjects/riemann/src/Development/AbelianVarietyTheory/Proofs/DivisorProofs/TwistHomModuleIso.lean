import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistHomMod

open GlobalTheory.LB (resG_resG resG_self isoOfLinear)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul coord mkSec coord_mkSec coord_add coord_smul
  coord_resM coord_rel coord_mem)

variable {Y : Scheme.{0}} (F G : Y.Modules) (M : LB Y)

theorem homApp_coord_rel {V : Y.Opens} (φ : Γ(twist (homMod F G) M, V)) (i j : M.ι)
    {W : Y.Opens} (hi : W ≤ V ⊓ M.U i) (hj : W ≤ V ⊓ M.U j) (hij : W ≤ M.U i ⊓ M.U j)
    (t : Γ(F, W)) :
    homApp (coord φ i) hi t = resG Y hij (M.g i j : Γ(Y, M.U i ⊓ M.U j)) • homApp (coord φ j) hj t := by
  have := congrArg (fun ψ => homApp ψ (le_refl W) t) (coord_rel φ i j hi hj hij)
  simpa only [homApp_res, homApp_smul, resG_self, LinearMap.smul_apply] using this

def fwdSec {V : Y.Opens} (φ : Γ(twist (homMod F G) M, V)) {T : Y.Opens} (hT : T ≤ V) :
    Γ(F, T) →ₗ[Γ(Y, T)] Γ(twist G M, T) where
  toFun s := mkSec (fun i => homApp (coord φ i) (inf_le_inf_right _ hT) (resM F inf_le_left s))
    fun i j => by
      simp only [← homApp_resM, resM_resM]
      exact homApp_coord_rel F G M φ i j _ _ _ _
  map_add' s t := Twist.sec_ext fun i => by
    change homApp (coord φ i) _ (resM F _ (s + t)) = _
    simp only [map_add]; rfl
  map_smul' a s := Twist.sec_ext fun i => by
    change homApp (coord φ i) _ (resM F _ (a • s)) = _
    simp only [coord_smul, resM_smul, map_smul, RingHom.id_apply]; rfl

def fwd (V : Y.Opens) : Γ(twist (homMod F G) M, V) →ₗ[Γ(Y, V)] Γ(homMod F (twist G M), V) where
  toFun φ := homMk (fun T hT => fwdSec F G M φ hT) fun T T' h h' s => Twist.sec_ext fun i => by
    change homApp (coord φ i) _ (resM F _ (resM F h' s)) =
      resM G _ (homApp (coord φ i) _ (resM F _ s))
    rw [← homApp_resM, resM_resM, resM_resM]
  map_add' φ ψ := VB.hom_ext fun T hT s => Twist.sec_ext fun i => rfl
  map_smul' a φ := VB.hom_ext fun T hT s => Twist.sec_ext fun i => by
    simp only [fwdSec, homApp_homMk, homApp_smul, LinearMap.coe_mk, AddHom.coe_mk, coord_mkSec,
      coord_smul, LinearMap.smul_apply, resG_resG, RingHom.id_apply]; rfl

def bwdSec {V : Y.Opens} (ψ : Γ(homMod F (twist G M), V)) (i : M.ι) {T : Y.Opens}
    (h : T ≤ V ⊓ M.U i) : Γ(F, T) →ₗ[Γ(Y, T)] Γ(G, T) where
  toFun s := resM G (le_inf le_rfl (h.trans inf_le_right) : T ≤ T ⊓ M.U i)
    (coord (homApp ψ (h.trans inf_le_left) s) i)
  map_add' s t := by simp only [map_add, coord_add]
  map_smul' a s := by
    simp only [map_smul, coord_smul, resM_smul, resG_resG, resG_self, RingHom.id_apply]

def bwd (V : Y.Opens) : Γ(homMod F (twist G M), V) →ₗ[Γ(Y, V)] Γ(twist (homMod F G) M, V) where
  toFun ψ := mkSec (fun i => homMk (fun T h => bwdSec F G M ψ i h) fun T T' h h' s => by
      simp only [bwdSec, LinearMap.coe_mk, AddHom.coe_mk]
      rw [homApp_resM ψ (h.trans inf_le_left) h' s, coord_resM, resM_resM, resM_resM])
    fun i j => VB.hom_ext fun W h s => by
      simp only [homApp_res, homApp_smul, homApp_homMk, LinearMap.smul_apply, bwdSec,
        LinearMap.coe_mk, AddHom.coe_mk, resG_resG]
      exact coord_rel _ i j _ _ _
  map_add' ψ ψ' := Twist.sec_ext fun i => VB.hom_ext fun W h s => by
    simp only [bwdSec, coord_mkSec, coord_add, homApp_add, homApp_homMk, LinearMap.add_apply,
      LinearMap.coe_mk, AddHom.coe_mk, map_add]
  map_smul' a ψ := Twist.sec_ext fun i => VB.hom_ext fun W h s => by
    simp only [bwdSec, coord_mkSec, coord_smul, homApp_smul, homApp_homMk, LinearMap.smul_apply,
      LinearMap.coe_mk, AddHom.coe_mk, resM_smul, resG_resG, RingHom.id_apply]

def secEquiv (V : Y.Opens) : Γ(twist (homMod F G) M, V) ≃ₗ[Γ(Y, V)] Γ(homMod F (twist G M), V) :=
  { fwd F G M V with
    invFun := bwd F G M V
    left_inv := fun φ => Twist.sec_ext fun i => VB.hom_ext fun W h s => by
      change resM G _ (homApp (coord φ i) _ (resM F _ s)) = _
      rw [← homApp_resM, resM_resM, resM_self]
    right_inv := fun ψ => VB.hom_ext fun T hT s => Twist.sec_ext fun i => by
      change resM G _ (coord (homApp ψ _ (resM F _ s)) i) = _
      rw [homApp_resM ψ hT inf_le_left s, coord_resM, resM_resM, resM_self] }

def iso : twist (homMod F G) M ≅ homMod F (twist G M) :=
  isoOfLinear (secEquiv F G M) fun {V W} h φ => VB.hom_ext fun T hT s => Twist.sec_ext fun i => rfl

end GlobalTheory.TwistHomMod

theorem GlobalTheory.TwistHomMod.nonempty_iso : ∀ (Y : Scheme.{0}) (F G : Y.Modules) (M : LB Y),
    Nonempty (twist (homMod F G) M ≅ homMod F (twist G M)) :=
  fun _ F G M => ⟨GlobalTheory.TwistHomMod.iso F G M⟩
