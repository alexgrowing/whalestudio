import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechSeparated
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.VBGlue

variable {X : Scheme.{0}}

theorem rs_rs {A B C : X.Opens} (h : B ≤ A) (h' : C ≤ B) (h'' : C ≤ A) (a : Γ(X, A)) :
    rs h' (rs h a) = rs h'' a := by
  change (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op).hom a = _
  rw [← X.presheaf.map_comp]
  rfl

theorem rs_self {A : X.Opens} (h : A ≤ A) (a : Γ(X, A)) : rs h a = a := by
  change (X.presheaf.map (homOfLE h).op).hom a = a
  rw [show (homOfLE h).op = 𝟙 (op A) from rfl, X.presheaf.map_id]
  rfl

variable {ι : Type} {U : ι → X.Opens} {κ : ι → Type} [∀ α, Fintype (κ α)]
  (g : ∀ α β, κ α → κ β → Γ(X, U α ⊓ U β))

def secGroup (W : X.Opens) : AddSubgroup (∀ α, κ α → Γ(X, W ⊓ U α)) where
  carrier := {s | ∀ α β k, rs (inf_le_left : W ⊓ U α ⊓ U β ≤ W ⊓ U α) (s α k) =
    ∑ k', rs (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W ⊓ U α ⊓ U β ≤ U α ⊓ U β) (g α β k k') *
      rs (inf_le_inf_right _ inf_le_left : W ⊓ U α ⊓ U β ≤ W ⊓ U β) (s β k')}
  add_mem' := fun {s t} hs ht α β k => by
    simp only [Pi.add_apply, map_add, hs α β k, ht α β k, mul_add, Finset.sum_add_distrib]
  zero_mem' := fun α β k => by simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero]
  neg_mem' := fun {s} hs α β k => by
    simp only [Pi.neg_apply, map_neg, hs α β k, mul_neg, Finset.sum_neg_distrib]

variable {g} in

theorem sec_rel {W : X.Opens} {s : ∀ α, κ α → Γ(X, W ⊓ U α)} (hs : s ∈ secGroup g W) (α β : ι) (k : κ α)
    {V : X.Opens} (h₁ : V ≤ W ⊓ U α) (h₂ : V ≤ W ⊓ U β) (h₃ : V ≤ U α ⊓ U β) :
    rs h₁ (s α k) = ∑ k', rs h₃ (g α β k k') * rs h₂ (s β k') := by
  have hV : V ≤ W ⊓ U α ⊓ U β := le_inf h₁ (h₂.trans inf_le_right)
  have := congrArg (rs hV) (hs α β k)
  simp only [map_sum, map_mul, rs_rs _ _ h₁, rs_rs _ _ h₂, rs_rs _ _ h₃] at this
  exact this

instance secModule (W : X.Opens) : Module Γ(X, W) (secGroup g W) where
  smul a s := ⟨fun α k => rs inf_le_left a * s.1 α k, fun α β k => by
    simp only [map_mul, s.2 α β k, rs_rs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [rs_rs _ _ (inf_le_left.trans inf_le_left), mul_left_comm,
      rs_rs _ _ (inf_le_left.trans inf_le_left)]⟩
  one_smul s := Subtype.ext <| funext fun α => funext fun k => by
    change rs _ 1 * s.1 α k = _
    rw [map_one, one_mul]
  mul_smul a b s := Subtype.ext <| funext fun α => funext fun k => by
    change rs _ (a * b) * s.1 α k = rs _ a * (rs _ b * s.1 α k)
    rw [map_mul, mul_assoc]
  smul_zero a := Subtype.ext <| funext fun α => funext fun k => mul_zero _
  smul_add a s t := Subtype.ext <| funext fun α => funext fun k => mul_add _ _ _
  add_smul a b s := Subtype.ext <| funext fun α => funext fun k => by
    change rs _ (a + b) * s.1 α k = rs _ a * s.1 α k + rs _ b * s.1 α k
    rw [map_add, add_mul]
  zero_smul s := Subtype.ext <| funext fun α => funext fun k => by
    change rs _ 0 * s.1 α k = 0
    rw [map_zero, zero_mul]

def secRes {V W : X.Opens} (h : W ≤ V) : secGroup g V →+ secGroup g W where
  toFun s := ⟨fun α k => rs (inf_le_inf_right _ h) (s.1 α k), fun α β k => by
    rw [rs_rs _ _ (le_inf (inf_le_left.trans (inf_le_left.trans h) ) (inf_le_left.trans inf_le_right))]
    rw [sec_rel s.2 α β k _ (le_inf (inf_le_left.trans (inf_le_left.trans h)) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [rs_rs]⟩
  map_zero' := Subtype.ext <| funext fun α => funext fun k => map_zero _
  map_add' s t := Subtype.ext <| funext fun α => funext fun k => map_add _ _ _

theorem secRes_smul {V W : X.Opens} (h : W ≤ V) (r : Γ(X, V)) (m : secGroup g V) :
    secRes g h (r • m) = rs h r • secRes g h m :=
  Subtype.ext <| funext fun α => funext fun k => by
    change rs _ (rs _ r * m.1 α k) = rs _ (rs h r) * rs _ (m.1 α k)
    rw [map_mul, rs_rs _ _ (inf_le_left.trans h), rs_rs _ _ (inf_le_left.trans h)]

def secPresheaf : TopCat.Presheaf Ab.{0} X where
  obj V := AddCommGrpCat.of (secGroup g V.unop)
  map f := AddCommGrpCat.ofHom (secRes g (leOfHom f.unop))
  map_id V := by
    ext s α k
    exact rs_self _ _
  map_comp f f' := by
    ext s α k
    exact (rs_rs _ _ _ _).symm

theorem isSheaf_secPresheaf : (secPresheaf g).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro I W sf hsf
  have hc (α : ι) : iSup W ⊓ U α ≤ ⨆ j, W j ⊓ U α := by rw [iSup_inf_eq]
  have hW (α : ι) (j : I) : W j ⊓ U α ≤ iSup W ⊓ U α := inf_le_inf_right _ (le_iSup W j)
  have H (α : ι) (k : κ α) : ∃ b : Γ(X, iSup W ⊓ U α), ∀ j, rs (hW α j) b = (sf j).1 α k := by
    refine GlobalTheory.LB.exists_fun_of_cover (fun j => W j ⊓ U α) (hW α) (hc α) (fun j => (sf j).1 α k)
      fun j l => ?_
    have e : rs (inf_le_inf_right (U α) (inf_le_left : W j ⊓ W l ≤ W j)) ((sf j).1 α k) =
        rs (inf_le_inf_right (U α) (inf_le_right : W j ⊓ W l ≤ W l)) ((sf l).1 α k) :=
      congrFun (congrFun (congrArg Subtype.val (hsf j l)) α) k
    have := congrArg (rs (le_inf (inf_le_inf inf_le_left inf_le_left)
      (inf_le_left.trans inf_le_right) :
        (W j ⊓ U α) ⊓ (W l ⊓ U α) ≤ W j ⊓ W l ⊓ U α)) e
    rw [rs_rs _ _ (inf_le_left), rs_rs _ _ (inf_le_right)] at this
    exact this
  choose b hb using H
  refine ⟨⟨b, fun α β k => ?_⟩, fun j => Subtype.ext (funext fun α => funext fun k => hb α k j), fun t ht => ?_⟩
  · refine GlobalTheory.LB.fun_ext_of_cover (fun j => W j ⊓ U α ⊓ U β)
      (fun j => inf_le_inf_right _ (hW α j)) (by rw [iSup_inf_eq, iSup_inf_eq]) fun j => ?_
    have e1 : ∀ (γ : ι) (c : κ γ) (h : W j ⊓ U α ⊓ U β ≤ W j ⊓ U γ)
        (h' : W j ⊓ U α ⊓ U β ≤ iSup W ⊓ U γ), rs h' (b γ c) = rs h ((sf j).1 γ c) := fun γ c h h' => by
      rw [← hb γ c j, rs_rs]
    have hA : W j ⊓ U α ⊓ U β ≤ W j ⊓ U α := inf_le_left
    have hB : W j ⊓ U α ⊓ U β ≤ W j ⊓ U β := inf_le_inf_right _ inf_le_left
    have hC : W j ⊓ U α ⊓ U β ≤ U α ⊓ U β := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    change rs _ (rs _ (b α k)) = rs _ (∑ k', rs _ (g α β k k') * rs _ (b β k'))
    rw [rs_rs _ _ (hA.trans (hW α j)), e1 α k hA, sec_rel (sf j).2 α β k hA hB hC, map_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [map_mul, rs_rs _ _ hC, rs_rs _ _ (hB.trans (hW β j)), e1 β k' hB]
  · refine Subtype.ext (funext fun α => funext fun k => GlobalTheory.LB.fun_ext_of_cover _ (hW α) (hc α) fun j => ?_)
    exact (congrFun (congrFun (congrArg Subtype.val (ht j)) α) k).trans (hb α k j).symm

def toMod : X.Modules :=
  letI : ∀ V, Module (X.ringCatSheaf.obj.obj V) ((secPresheaf g).obj V) :=
    fun V => secModule g V.unop
  { val := PresheafOfModules.ofPresheaf (secPresheaf g) fun _ _ f r m =>
      secRes_smul g (leOfHom f.unop) r m
    isSheaf := isSheaf_secPresheaf g }

@[simp] theorem rs_trans {A B C : X.Opens} (h : B ≤ A) (h' : C ≤ B) (a : Γ(X, A)) :
    rs h' (rs h a) = rs (h'.trans h) a := rs_rs h h' _ a

def Coc : Prop :=
  (∀ α (V : X.Opens) (h : V ≤ U α ⊓ U α) (v : κ α → Γ(X, V)) (k : κ α),
    ∑ k', rs h (g α α k k') * v k' = v k) ∧
  (∀ α β γ (V : X.Opens) (h₁ : V ≤ U α ⊓ U β) (h₂ : V ≤ U β ⊓ U γ) (h₃ : V ≤ U α ⊓ U γ)
    (v : κ γ → Γ(X, V)) (k : κ α),
    ∑ k', rs h₁ (g α β k k') * ∑ k'', rs h₂ (g β γ k' k'') * v k'' = ∑ k'', rs h₃ (g α γ k k'') * v k'')

def coord {W : X.Opens} (α : ι) (h : W ≤ U α) (s : secGroup g W) (k : κ α) : Γ(X, W) :=
  rs (le_inf le_rfl h) (s.1 α k)

theorem coord_change {W : X.Opens} (α β : ι) (hα : W ≤ U α) (hβ : W ≤ U β) (hαβ : W ≤ U α ⊓ U β)
    (s : secGroup g W) (k : κ α) :
    coord g α hα s k = ∑ k', rs hαβ (g α β k k') * coord g β hβ s k' :=
  sec_rel s.2 α β k _ _ hαβ

theorem coord_res {V W : X.Opens} (h : W ≤ V) (α : ι) (hV : V ≤ U α) (hW : W ≤ U α)
    (s : secGroup g V) (k : κ α) :
    coord g α hW (secRes g h s) k = rs h (coord g α hV s k) := by
  change rs _ (rs _ (s.1 α k)) = rs _ (rs _ (s.1 α k))
  simp only [rs_trans]

variable {g} in

def ofCoord (hc : Coc g) {W : X.Opens} (α : ι) (h : W ≤ U α) (t : κ α → Γ(X, W)) : secGroup g W :=
  ⟨fun β k => ∑ k', rs (le_inf inf_le_right (inf_le_left.trans h) : W ⊓ U β ≤ U β ⊓ U α) (g β α k k') *
    rs inf_le_left (t k'), fun β γ k => by
      simp only [map_sum, map_mul, rs_trans, Finset.mul_sum]
      have := hc.2 β γ α (W ⊓ U β ⊓ U γ)
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (le_inf inf_le_right (inf_le_left.trans (inf_le_left.trans h)))
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans (inf_le_left.trans h)))
        (fun k' => rs (inf_le_left.trans inf_le_left) (t k')) k
      simp only [Finset.mul_sum] at this
      exact this.symm⟩

variable {g} in

def coordEquiv (hc : Coc g) {W : X.Opens} (α : ι) (h : W ≤ U α) :
    secGroup g W ≃ₗ[Γ(X, W)] (κ α → Γ(X, W)) where
  toFun := coord g α h
  map_add' s t := funext fun k => map_add _ _ _
  map_smul' r s := funext fun k => by
    change rs _ (rs _ r * s.1 α k) = r * rs _ (s.1 α k)
    rw [map_mul, rs_trans, rs_self]
  invFun := ofCoord hc α h
  left_inv s := Subtype.ext <| funext fun β => funext fun k => by
    have := sec_rel s.2 β α k (le_rfl : W ⊓ U β ≤ W ⊓ U β) (le_inf inf_le_left (inf_le_left.trans h))
      (le_inf inf_le_right (inf_le_left.trans h))
    rw [rs_self] at this
    rw [this]
    refine Finset.sum_congr rfl fun k' _ => ?_
    change _ * rs _ (rs _ (s.1 α k')) = _
    rw [rs_trans]
  right_inv t := funext fun k => by
    change rs _ (∑ k', _ * rs _ (t k')) = t k
    simp only [map_sum, map_mul, rs_trans, rs_self]
    exact hc.1 α W (le_inf h h) t k

variable {g}

theorem coord_ofCoord (hc : Coc g) {W : X.Opens} (α : ι) (h : W ≤ U α) (t : κ α → Γ(X, W)) :
    coord g α h (ofCoord hc α h t) = t := (coordEquiv hc α h).apply_symm_apply t

theorem sec_ext_coord (hc : Coc g) {W : X.Opens} (α : ι) (h : W ≤ U α) {s t : secGroup g W}
    (e : coord g α h s = coord g α h t) : s = t := (coordEquiv hc α h).injective e

end GlobalTheory.CompanionTheory.VBGlue
