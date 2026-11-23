import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameGlue

variable {X : Scheme.{0}} {M M' : X.Modules} {r : ℕ}

def locMap {U : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) (φ : Fin r → Γ(M', U)) {W : X.Opens}
    (h : W ≤ U) : Γ(M, W) →ₗ[Γ(X, W)] Γ(M', W) :=
  (hf.basis h).constr Γ(X, W) fun a => Twist.resM M' h (φ a)

theorem locMap_frame {U : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) (φ : Fin r → Γ(M', U)) {W : X.Opens}
    (h : W ≤ U) (a : Fin r) : locMap hf φ h (Twist.resM M h (f a)) = Twist.resM M' h (φ a) := by
  rw [← hf.basis_apply h, locMap, Module.Basis.constr_basis]

theorem res_res {F : X.Modules} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(F, U)) :
    Twist.resM F h₂ (Twist.resM F h₁ s) = Twist.resM F (h₂.trans h₁) s :=
  LB.modRes_modRes h₁ h₂ s

theorem res_smul {F : X.Modules} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (s : Γ(F, U)) :
    Twist.resM F h (a • s) = resG X h a • Twist.resM F h s :=
  LB.modRes_smul h a s

theorem res_self {F : X.Modules} {U : X.Opens} (h : U ≤ U) (s : Γ(F, U)) : Twist.resM F h s = s :=
  LB.modRes_self h s

theorem res_locMap {U : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) (φ : Fin r → Γ(M', U)) {W W' : X.Opens}
    (h : W ≤ U) (h' : W' ≤ W) (s : Γ(M, W)) :
    Twist.resM M' h' (locMap hf φ h s) = locMap hf φ (h'.trans h) (Twist.resM M h' s) := by
  rw [← (hf.basis h).sum_repr s]
  simp only [map_sum, map_smul, res_smul, hf.basis_apply, locMap_frame, res_res]

theorem locMap_eq {U U' : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) (φ : Fin r → Γ(M', U))
    {f' : Fin r → Γ(M, U')} (hf' : VB.IsFrame f') (φ' : Fin r → Γ(M', U'))
    (H : ∀ a, Twist.resM M' (inf_le_right : U ⊓ U' ≤ U') (φ' a) =
      ∑ b, trCo hf f' b a • Twist.resM M' (inf_le_left : U ⊓ U' ≤ U) (φ b))
    {W : X.Opens} (h : W ≤ U) (h' : W ≤ U') : locMap hf φ h = locMap hf' φ' h' := by
  refine (hf'.basis h').ext fun a => ?_
  have e : locMap hf φ (inf_le_left : U ⊓ U' ≤ U) (Twist.resM M inf_le_right (f' a)) =
      Twist.resM M' (inf_le_right : U ⊓ U' ≤ U') (φ' a) := by
    rw [H a, locMap, Module.Basis.constr_apply_fintype]
    rfl
  have e' := congrArg (Twist.resM M' (le_inf h h')) e
  rw [res_locMap, res_res, res_res] at e'
  rw [hf'.basis_apply, locMap_frame]
  exact e'

theorem exists_hom_of_frames : ∀ (X : Scheme.{0}) (M M' : X.Modules) (r : ℕ) (ι : Type) (U : ι → X.Opens), (∀ x : X, ∃ i, x ∈ U i) →
    ∀ (f : ∀ i, Fin r → Γ(M, U i)) (hf : ∀ i, VB.IsFrame (f i)) (φ : ∀ i, Fin r → Γ(M', U i)),
    (∀ i j a, Twist.resM M' (inf_le_right : U i ⊓ U j ≤ U j) (φ j a) =
      ∑ b, trCo (hf i) (f j) b a • Twist.resM M' (inf_le_left : U i ⊓ U j ≤ U i) (φ i b)) →
    ∃ g : M ⟶ M', ∀ i a, g.app (U i) (f i a) = φ i a := by
  intro X M M' r ι U hU f hf φ H
  have hc (V : X.Opens) : V ≤ ⨆ i, V ⊓ U i := fun x hx => by
    obtain ⟨i, hi⟩ := hU x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, hi⟩
  have ex (V : X.Opens) (s : Γ(M, V)) : ∃ t : Γ(M', V), ∀ (i : ι) (W : X.Opens) (hV : W ≤ V) (hi : W ≤ U i),
      Twist.resM M' hV t = locMap (hf i) (φ i) hi (Twist.resM M hV s) := by
    obtain ⟨t, ht⟩ := LB.exists_modSec_of_cover (F := M') (fun i => V ⊓ U i) (fun _ => inf_le_left) (hc V)
      (fun i => locMap (hf i) (φ i) inf_le_right (Twist.resM M inf_le_left s)) fun i j => by
        change Twist.resM M' _ _ = Twist.resM M' _ _
        rw [res_locMap, res_locMap, res_res, res_res, locMap_eq (hf i) (φ i) (hf j) (φ j) (H i j)]
    refine ⟨t, fun i W hV hi => ?_⟩
    have := congrArg (Twist.resM M' (le_inf hV hi)) (ht i)
    rw [res_locMap, res_res, res_res] at this
    exact this
  choose t ht using ex
  have ext (V : X.Opens) (a b : Γ(M', V))
      (h : ∀ i, Twist.resM M' (inf_le_left : V ⊓ U i ≤ V) a = Twist.resM M' (inf_le_left : V ⊓ U i ≤ V) b) :
      a = b :=
    LB.modSec_ext_of_cover (fun i => V ⊓ U i) (fun _ => inf_le_left) (hc V) h
  refine ⟨LB.homOfLinear (fun V =>
    { toFun := t V
      map_add' := fun s s' => ext V _ _ fun i => by
        rw [map_add, ht V _ i _ _ inf_le_right, ht V _ i _ _ inf_le_right, ht V _ i _ _ inf_le_right,
          map_add, map_add]
      map_smul' := fun c s => ext V _ _ fun i => by
        rw [RingHom.id_apply, res_smul, ht V _ i _ _ inf_le_right, ht V _ i _ _ inf_le_right,
          res_smul, map_smul] }) (fun {V W} h s => ext W _ _ fun i => ?_), fun i a => ?_⟩
  · change Twist.resM M' _ (t W (Twist.resM M h s)) = Twist.resM M' _ (Twist.resM M' h (t V s))
    rw [res_res, ht W _ i _ _ inf_le_right, ht V _ i _ _ inf_le_right, res_res]
  · have := ht (U i) (f i a) i (U i) le_rfl le_rfl
    rw [locMap_frame, res_self, res_self] at this
    exact this

end GlobalTheory.FrameGlue

end
