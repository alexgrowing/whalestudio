import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechSeparated
import GroundTheory.ArithmeticGeometry.SchemeCohomology.AffineVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.VBAff

section Rs

variable {X : Scheme.{0}}

theorem rs_rs {A B C : X.Opens} (h₁ : B ≤ A) (h₂ : C ≤ B) (x : Γ(X, A)) :
    rs h₂ (rs h₁ x) = rs (h₂.trans h₁) x := by
  simp only [rs, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem rs_self {A : X.Opens} (h : A ≤ A) (x : Γ(X, A)) : rs h x = x := by
  have : (homOfLE h).op = 𝟙 (op A) := rfl
  simp only [rs, this, CategoryTheory.Functor.map_id]
  rfl

theorem eq_of_cover {J : Type} {T : X.Opens} (C : J → X.Opens) (hC : ∀ j, C j ≤ T)
    (hc : T ≤ iSup C) {a b : Γ(X, T)} (h : ∀ j, rs (hC j) a = rs (hC j) b) : a = b :=
  TopCat.Sheaf.eq_of_locally_eq' X.sheaf C T (fun j => homOfLE (hC j)) hc a b h

theorem exists_glue {J : Type} {T : X.Opens} (C : J → X.Opens) (hC : ∀ j, C j ≤ T)
    (hc : T ≤ iSup C) (t : ∀ j, Γ(X, C j))
    (h : ∀ j l (D : X.Opens) (hj : D ≤ C j) (hl : D ≤ C l), rs hj (t j) = rs hl (t l)) :
    ∃ a : Γ(X, T), ∀ j, rs (hC j) a = t j := by
  obtain ⟨a, ha, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf C T (fun j => homOfLE (hC j)) hc t
    (fun j l => h j l _ inf_le_left inf_le_right)
  exact ⟨a, ha⟩

end Rs

section Sections

variable {X : Scheme.{0}} {ι : Type} (U : ι → X.Opens) (κ : ι → Type) [∀ α, Fintype (κ α)]
  (g : ∀ α β, κ α → κ β → Γ(X, U α ⊓ U β))

def Compat (V : X.Opens) (s : ∀ α, κ α → Γ(X, V ⊓ U α)) : Prop :=
  ∀ α β (k : κ α), rs (show V ⊓ U α ⊓ U β ≤ V ⊓ U α from inf_le_left) (s α k) =
    ∑ k' : κ β, rs (show V ⊓ U α ⊓ U β ≤ U α ⊓ U β from inf_le_inf_right _ inf_le_right) (g α β k k') *
      rs (show V ⊓ U α ⊓ U β ≤ V ⊓ U β from inf_le_inf_right _ inf_le_left) (s β k')

variable {U κ g} in

theorem Compat.on {V : X.Opens} {s : ∀ α, κ α → Γ(X, V ⊓ U α)} (hs : Compat U κ g V s) (α β : ι)
    (k : κ α) {T : X.Opens} (h₁ : T ≤ V ⊓ U α) (h₂ : T ≤ U α ⊓ U β) (h₃ : T ≤ V ⊓ U β) :
    rs h₁ (s α k) = ∑ k' : κ β, rs h₂ (g α β k k') * rs h₃ (s β k') := by
  have hT : T ≤ V ⊓ U α ⊓ U β := le_inf h₁ (h₂.trans inf_le_right)
  have := congrArg (rs hT) (hs α β k)
  simp only [map_sum, map_mul, rs_rs] at this
  exact this

def secGroup (V : X.Opens) : AddSubgroup (∀ α, κ α → Γ(X, V ⊓ U α)) where
  carrier := {s | Compat U κ g V s}
  add_mem' := fun {s t} hs ht α β k => by
    simp only [Pi.add_apply, map_add, hs α β k, ht α β k, mul_add, Finset.sum_add_distrib]
  zero_mem' := fun α β k => by
    simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero]
  neg_mem' := fun {s} hs α β k => by
    simp only [Pi.neg_apply, map_neg, hs α β k, mul_neg, Finset.sum_neg_distrib]

instance secGroupModule (V : X.Opens) : Module Γ(X, V) (secGroup U κ g V) where
  smul a s := ⟨fun α k => rs inf_le_left a * s.1 α k, fun α β k => by
    have := s.2 α β k
    simp only [map_mul, rs_rs, this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    ring⟩
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

variable {U κ g} in

theorem smul_val {V : X.Opens} (a : Γ(X, V)) (s : secGroup U κ g V) (α : ι) (k : κ α) :
    (a • s).1 α k = rs inf_le_left a * s.1 α k := rfl

def secRes {V V' : X.Opens} (h : V' ≤ V) : secGroup U κ g V →+ secGroup U κ g V' where
  toFun s := ⟨fun α k => rs (inf_le_inf_right _ h) (s.1 α k), fun α β k => by
    have := s.2.on α β k (T := V' ⊓ U α ⊓ U β) (inf_le_left.trans (inf_le_inf_right _ h))
      (inf_le_inf_right _ inf_le_right)
      ((inf_le_inf_right _ inf_le_left).trans (inf_le_inf_right _ h))
    simp only [rs_rs, this]⟩
  map_zero' := Subtype.ext <| funext fun α => funext fun k => map_zero _
  map_add' s t := Subtype.ext <| funext fun α => funext fun k => map_add _ _ _

variable {U κ g} in
@[simp] theorem secRes_val {V V' : X.Opens} (h : V' ≤ V) (s : secGroup U κ g V) (α : ι) (k : κ α) :
    (secRes U κ g h s).1 α k = rs (inf_le_inf_right _ h) (s.1 α k) := rfl

theorem secRes_smul {V V' : X.Opens} (h : V' ≤ V) (r : Γ(X, V)) (m : secGroup U κ g V) :
    secRes U κ g h (r • m) = rs h r • secRes U κ g h m :=
  Subtype.ext <| funext fun α => funext fun k => by
    simp only [secRes_val, smul_val, map_mul, rs_rs]

def secPresheaf : TopCat.Presheaf Ab.{0} X where
  obj V := AddCommGrpCat.of (secGroup U κ g V.unop)
  map f := AddCommGrpCat.ofHom (secRes U κ g (leOfHom f.unop))
  map_id V := by
    ext s α k
    exact rs_self _ _
  map_comp f g' := by
    ext s α k
    exact (rs_rs _ _ _).symm

theorem isSheaf_secPresheaf : (secPresheaf U κ g).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro J C sf hsf
  let sf' (j : J) : secGroup U κ g (C j) := sf j
  have hsf' (j l : J) (α : ι) (k : κ α) (D : X.Opens) (hj : D ≤ C j ⊓ U α) (hl : D ≤ C l ⊓ U α) :
      rs hj ((sf' j).1 α k) = rs hl ((sf' l).1 α k) := by
    have e : secRes U κ g (inf_le_left : C j ⊓ C l ≤ C j) (sf' j) =
      secRes U κ g (inf_le_right : C j ⊓ C l ≤ C l) (sf' l) := hsf j l
    have e' := congrArg (fun s => s.1 α k) e
    simp only [secRes_val] at e'
    have hD : D ≤ (C j ⊓ C l) ⊓ U α :=
      le_inf (le_inf (hj.trans inf_le_left) (hl.trans inf_le_left)) (hj.trans inf_le_right)
    have e'' := congrArg (rs hD) e'
    simpa only [rs_rs] using e''
  have hcov (α : ι) : iSup C ⊓ U α ≤ ⨆ j, C j ⊓ U α := by
    rw [iSup_inf_eq]
  have hC (α : ι) (j : J) : C j ⊓ U α ≤ iSup C ⊓ U α := inf_le_inf_right _ (le_iSup C j)
  choose b hb using fun (α : ι) (k : κ α) => exists_glue (fun j => C j ⊓ U α) (hC α) (hcov α)
    (fun j => (sf' j).1 α k) fun j l D hj hl => hsf' j l α k D hj hl
  have hbc : Compat U κ g (iSup C) b := fun α β k => by
    have hle : iSup C ⊓ U α ⊓ U β ≤ ⨆ j, C j ⊓ U α ⊓ U β := by
      rw [iSup_inf_eq, iSup_inf_eq]
    refine eq_of_cover (fun j => C j ⊓ U α ⊓ U β) (fun j => inf_le_inf_right _ (hC α j)) hle
      fun j => ?_
    simp only [map_sum, map_mul, rs_rs]
    have h1 := (sf' j).2.on α β k (T := C j ⊓ U α ⊓ U β) inf_le_left
      (inf_le_inf_right _ inf_le_right) (inf_le_inf_right _ inf_le_left)
    rw [← hb α k j, rs_rs] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [← hb β k' j, rs_rs]
  refine ⟨(⟨b, hbc⟩ : secGroup U κ g (iSup C)), fun j => ?_, fun t ht => ?_⟩
  · refine Subtype.ext <| funext fun α => funext fun k => ?_
    exact hb α k j
  · let t' : secGroup U κ g (iSup C) := t
    refine Subtype.ext <| funext fun α => funext fun k => ?_
    refine eq_of_cover (fun j => C j ⊓ U α) (hC α) (hcov α) fun j => ?_
    have e : secRes U κ g (le_iSup C j) t' = sf' j := ht j
    rw [hb α k j]
    exact congrArg (fun s => s.1 α k) e

def toMod : X.Modules :=
  letI : ∀ V, Module (X.ringCatSheaf.obj.obj V) ((secPresheaf U κ g).obj V) :=
    fun V => secGroupModule U κ g V.unop
  { val := PresheafOfModules.ofPresheaf (secPresheaf U κ g) fun _ _ f r m =>
      secRes_smul U κ g (leOfHom f.unop) r m
    isSheaf := isSheaf_secPresheaf U κ g }

end Sections

section Coords

variable {X : Scheme.{0}} {ι : Type} (U : ι → X.Opens) (κ : ι → Type) [∀ α, Fintype (κ α)]
  (g : ∀ α β, κ α → κ β → Γ(X, U α ⊓ U β))

def IsCoc : Prop :=
  (∀ (α : ι) (T : X.Opens) (h : T ≤ U α ⊓ U α) (k : κ α) (f : κ α → Γ(X, T)),
    ∑ k', rs h (g α α k k') * f k' = f k) ∧
  (∀ (α β γ : ι) (T : X.Opens) (h₁ : T ≤ U α ⊓ U β) (h₂ : T ≤ U β ⊓ U γ) (h₃ : T ≤ U α ⊓ U γ)
    (k : κ α) (f : κ γ → Γ(X, T)),
    ∑ k', rs h₁ (g α β k k') * ∑ k'', rs h₂ (g β γ k' k'') * f k'' =
      ∑ k'', rs h₃ (g α γ k k'') * f k'')

variable {U κ g}

def coord {V : X.Opens} {β : ι} (h : V ≤ U β) : secGroup U κ g V →ₗ[Γ(X, V)] (κ β → Γ(X, V)) where
  toFun s k := rs (le_inf le_rfl h) (s.1 β k)
  map_add' s t := funext fun k => map_add _ _ _
  map_smul' a s := funext fun k => by
    change rs _ (rs _ a * s.1 β k) = a * rs _ (s.1 β k)
    rw [map_mul, rs_rs, rs_self]

theorem coord_apply {V : X.Opens} {β : ι} (h : V ≤ U β) (s : secGroup U κ g V) (k : κ β) :
    coord h s k = rs (le_inf le_rfl h) (s.1 β k) := rfl

def ofCoord (hg : IsCoc U κ g) {V : X.Opens} {β : ι} (h : V ≤ U β) (t : κ β → Γ(X, V)) :
    secGroup U κ g V :=
  ⟨fun α k => ∑ k', rs (le_inf inf_le_right (inf_le_left.trans h)) (g α β k k') * rs inf_le_left (t k'),
    fun α γ k => by
    simp only [map_sum, map_mul, rs_rs, Finset.mul_sum]
    have hT1 : V ⊓ U α ⊓ U γ ≤ U α ⊓ U γ := inf_le_inf_right _ inf_le_right
    have hT2 : V ⊓ U α ⊓ U γ ≤ U γ ⊓ U β := le_inf inf_le_right (inf_le_left.trans (inf_le_left.trans h))
    have hT3 : V ⊓ U α ⊓ U γ ≤ U α ⊓ U β :=
      le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans (inf_le_left.trans h))
    have := hg.2 α γ β _ hT1 hT2 hT3 k
      (fun k' => rs (inf_le_left.trans inf_le_left) (t k'))
    rw [← this]
    simp only [Finset.mul_sum]⟩

theorem ofCoord_val (hg : IsCoc U κ g) {V : X.Opens} {β : ι} (h : V ≤ U β) (t : κ β → Γ(X, V))
    (α : ι) (k : κ α) : (ofCoord hg h t).1 α k =
      ∑ k', rs (le_inf inf_le_right (inf_le_left.trans h)) (g α β k k') * rs inf_le_left (t k') := rfl

theorem coord_ofCoord' (hg : IsCoc U κ g) {V : X.Opens} {α β : ι} (hα : V ≤ U α) (hβ : V ≤ U β)
    (t : κ β → Γ(X, V)) (k : κ α) :
    coord hα (ofCoord hg hβ t) k = ∑ k', rs (le_inf hα hβ) (g α β k k') * t k' := by
  simp only [coord_apply, ofCoord_val, map_sum, map_mul, rs_rs, rs_self]

theorem coord_ofCoord (hg : IsCoc U κ g) {V : X.Opens} {β : ι} (h : V ≤ U β) (t : κ β → Γ(X, V)) :
    coord h (ofCoord hg h t) = t := funext fun k => by
  rw [coord_ofCoord']
  exact hg.1 β V (le_inf h h) k t

theorem ofCoord_coord (hg : IsCoc U κ g) {V : X.Opens} {β : ι} (h : V ≤ U β)
    (s : secGroup U κ g V) : ofCoord hg h (coord h s) = s :=
  Subtype.ext <| funext fun α => funext fun k => by
    rw [ofCoord_val]
    have hT : V ⊓ U α ≤ V ⊓ U α ⊓ U β := le_inf le_rfl (inf_le_left.trans h)
    have := s.2.on α β k (T := V ⊓ U α) le_rfl (le_inf inf_le_right (inf_le_left.trans h))
      (le_inf inf_le_left (inf_le_left.trans h))
    rw [rs_self] at this
    rw [this]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [coord_apply, rs_rs]

def secEquiv (hg : IsCoc U κ g) {V : X.Opens} {β : ι} (h : V ≤ U β) :
    secGroup U κ g V ≃ₗ[Γ(X, V)] (κ β → Γ(X, V)) :=
  { coord h with
    invFun := ofCoord hg h
    left_inv := ofCoord_coord hg h
    right_inv := coord_ofCoord hg h }

theorem coord_secRes {V V' : X.Opens} {β : ι} (h : V ≤ U β) (h' : V' ≤ V) (s : secGroup U κ g V)
    (k : κ β) : coord (h'.trans h) (secRes U κ g h' s) k = rs h' (coord h s k) := by
  simp only [coord_apply, secRes_val, rs_rs]

theorem sec_ext_coord {V : X.Opens} {β : ι} (hg : IsCoc U κ g) (h : V ≤ U β) {s t : secGroup U κ g V}
    (e : ∀ k, coord h s k = coord h t k) : s = t := by
  rw [← ofCoord_coord hg h s, ← ofCoord_coord hg h t, funext e]

end Coords

section Frames

variable {X : Scheme.{0}} {ι : Type} {U : ι → X.Opens} {κ : ι → Type} [∀ α, Fintype (κ α)]
  {g : ∀ α β, κ α → κ β → Γ(X, U α ⊓ U β)}

open Classical in

def frame (hg : IsCoc U κ g) (β : ι) (k : κ β) : Γ(toMod U κ g, U β) :=
  show secGroup U κ g (U β) from ofCoord hg le_rfl (Pi.single k 1)

open Classical in
theorem isFrame_frame (hg : IsCoc U κ g) (β : ι) : GlobalTheory.VB.IsFrame (frame (U := U) hg β) := by
  refine GlobalTheory.VB.isFrame_of_basis
    (fun V h => (Module.Basis.ofEquivFun (secEquiv hg h) : Module.Basis (κ β) Γ(X, V) (secGroup U κ g V)))
    fun V h k => ?_
  refine (congrFun (Module.Basis.coe_ofEquivFun (secEquiv hg h)) k).trans ?_
  change ofCoord hg h (Pi.single k 1) = secRes U κ g h (ofCoord hg le_rfl (Pi.single k 1))
  refine sec_ext_coord hg h fun k' => ?_
  rw [coord_ofCoord, coord_secRes (le_refl (U β)) h, coord_ofCoord, Pi.single_apply, Pi.single_apply]
  split_ifs <;> simp

theorem isQuasicoherent_toMod (hg : IsCoc U κ g) (hU : iSup U = ⊤) :
    (toMod U κ g).IsQuasicoherent :=
  GlobalTheory.OmegaGlobal.isQuasicoherent_of_frames fun x => by
    obtain ⟨β, hβ⟩ := Opens.mem_iSup.1 (hU ▸ trivial : x ∈ iSup U)
    exact ⟨U β, Fintype.card (κ β), _, hβ,
      (isFrame_frame hg β).comp_equiv (Fintype.equivFin _).symm⟩

end Frames

section FromVB

attribute [local instance] VB.fin

variable {O : Type} [CommRing O] {X : Scheme.{0}} {str : ∀ W : X.Opens, O →+* Γ(X, W)}
  {ι : Type} {U : ι → X.Opens} {K : Cos.{1} O} (V : VB str U K)

theorem mul_g_tuple {n : ℕ} (a b c : Fin (n + 1)) (i : Fin (n + 1) → ι) (k : V.κ (i a)) (m : V.κ (i c)) :
    ∑ k', rs (le_inf (capO_le U i a) (capO_le U i b)) (V.g (i a) (i b) k k') *
      rs (le_inf (capO_le U i b) (capO_le U i c)) (V.g (i b) (i c) k' m) =
    rs (le_inf (capO_le U i a) (capO_le U i c)) (V.g (i a) (i c) k m) := by
  classical
  obtain ⟨x, hx⟩ := (V.e n c).surjective (fun i' => if h : i' = i then h ▸ Pi.single m 1 else 0)
  have hxi : V.e n c x i = Pi.single m 1 := by
    rw [hx]
    simp
  have h1 := V.e_chg n a c x i k
  have h2 := V.e_chg n a b x i k
  rw [h2] at h1
  simp only [fun k' => V.e_chg n b c x i k', hxi, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  exact h1

open Classical in

theorem g_self_tuple {n : ℕ} (a : Fin (n + 1)) (i : Fin (n + 1) → ι) (k m : V.κ (i a)) :
    rs (le_inf (capO_le U i a) (capO_le U i a)) (V.g (i a) (i a) k m) = if k = m then 1 else 0 := by
  classical
  obtain ⟨x, hx⟩ := (V.e n a).surjective (fun i' => if h : i' = i then h ▸ Pi.single m 1 else 0)
  have hxi : V.e n a x i = Pi.single m 1 := by
    rw [hx]
    simp
  have h1 := V.e_chg n a a x i k
  simp only [hxi, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h1
  exact h1.symm

theorem isCoc : IsCoc U V.κ V.g := by
  classical
  constructor
  · intro α T h k f
    let i : Fin 1 → ι := fun _ => α
    have hT : T ≤ capO U i := le_iInf fun _ => h.trans inf_le_left
    have e (k' : V.κ α) : rs h (V.g α α k k') = if k = k' then 1 else 0 := by
      have := congrArg (rs hT) (g_self_tuple V (0 : Fin 1) i k k')
      simp only [rs_rs] at this
      rw [this]
      split_ifs <;> simp
    simp only [e, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · intro α β γ T h₁ h₂ h₃ k f
    let i : Fin 3 → ι := ![α, β, γ]
    have hT : T ≤ capO U i := le_iInf fun a => by
      fin_cases a
      · exact h₁.trans inf_le_left
      · exact h₁.trans inf_le_right
      · exact h₂.trans inf_le_right
    have e (m : V.κ γ) : ∑ k', rs h₁ (V.g α β k k') * rs h₂ (V.g β γ k' m) = rs h₃ (V.g α γ k m) := by
      have := congrArg (rs hT) (mul_g_tuple V (0 : Fin 3) 1 2 i k m)
      simp only [map_sum, map_mul, rs_rs] at this
      exact this
    simp only [← e, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun m _ => ?_
    ring

end FromVB

section Cochains

open GroundTheory.Arith.SchemeCoh

attribute [local instance] VB.fin

variable {O : Type} [CommRing O] {X : Scheme.{0}} {str : ∀ W : X.Opens, O →+* Γ(X, W)}
  {ι : Type} {U : ι → X.Opens} {K : Cos.{1} O} (V : VB str U K)

theorem inter_le_capO {n : ℕ} (i : Fin n → ι) : inter (X := X.toTopCat) U i ≤ capO U i :=
  (inter_eq_iInf U i).le

theorem capO_le_inter {n : ℕ} (i : Fin n → ι) : capO U i ≤ inter (X := X.toTopCat) U i :=
  (inter_eq_iInf U i).ge

theorem inter_le' {n : ℕ} (i : Fin n → ι) (a : Fin n) : inter (X := X.toTopCat) U i ≤ U (i a) :=
  (inter_le_capO i).trans (capO_le U i a)

def secOf (n : ℕ) (x : K.X n) (i : Fin (n + 1) → ι) :
    secGroup U V.κ V.g (inter (X := X.toTopCat) U i) :=
  ofCoord (isCoc V) (inter_le' i 0) fun k => rs (inter_le_capO i) (V.e n 0 x i k)

theorem coord_secOf (n : ℕ) (x : K.X n) (i : Fin (n + 1) → ι) (a : Fin (n + 1)) (k : V.κ (i a)) :
    coord (inter_le' i a) (secOf V n x i) k = rs (inter_le_capO i) (V.e n a x i k) := by
  rw [secOf, coord_ofCoord', V.e_chg n a 0 x i k]
  simp only [map_sum, map_mul, rs_rs]

def cochainEquiv (n : ℕ) : K.X n ≃+ Cochain (modulesAb (toMod U V.κ V.g)).obj U n where
  toFun x i := secOf V n x i
  invFun σ := (V.e n 0).symm fun i k => rs (capO_le_inter i)
    (coord (inter_le' i 0) (show secGroup U V.κ V.g _ from σ i) k)
  left_inv x := by
    apply (V.e n 0).injective
    rw [AddEquiv.apply_symm_apply]
    funext i k
    change rs _ (coord (inter_le' i 0) (secOf V n x i) k) = _
    rw [coord_secOf, rs_rs, rs_self]
  right_inv σ := by
    funext i
    refine sec_ext_coord (isCoc V) (inter_le' i 0) fun k => ?_
    rw [coord_secOf, AddEquiv.apply_symm_apply, rs_rs, rs_self]
  map_add' x y := by
    funext i
    refine sec_ext_coord (isCoc V) (inter_le' i 0) fun k => ?_
    change _ = coord (inter_le' i 0) (secOf V n x i + secOf V n y i) k
    rw [map_add, Pi.add_apply, coord_secOf, coord_secOf, coord_secOf, map_add, Pi.add_apply,
      Pi.add_apply, map_add]

theorem cochainEquiv_δ (n : ℕ) (j : Fin (n + 2)) (x : K.X n) (i : Fin (n + 2) → ι) :
    cochainEquiv V (n + 1) (K.δ n j x) i =
      res (modulesAb (toMod U V.κ V.g)).obj (inter_le_comp U i j.succAbove)
        (cochainEquiv V n x (i ∘ j.succAbove)) := by
  refine sec_ext_coord (isCoc V) (inter_le' i (j.succAbove 0)) fun k => ?_
  change coord _ (secOf V (n + 1) (K.δ n j x) i) k =
    coord _ (secRes U V.κ V.g (inter_le_comp U i j.succAbove) (secOf V n x (i ∘ j.succAbove))) k
  rw [coord_secOf, V.e_δ n 0 j x i k, rs_rs]
  have := coord_secRes (inter_le' (i ∘ j.succAbove) 0) (inter_le_comp U i j.succAbove)
    (secOf V n x (i ∘ j.succAbove)) k
  refine Eq.trans ?_ this.symm
  rw [coord_secOf, rs_rs]

theorem cochainEquiv_d (n : ℕ) (x : K.X n) :
    cochainEquiv V (n + 1) (K.d n x) = d (modulesAb (toMod U V.κ V.g)).obj U n (cochainEquiv V n x) := by
  funext i
  rw [d_apply, Cos.d_apply, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, Pi.smul_apply, cochainEquiv_δ]

end Cochains

section Top

open GroundTheory.Arith.SchemeCoh

attribute [local instance] VB.fin

variable {O : Type} [CommRing O] {X : Scheme.{0}} {str : ∀ W : X.Opens, O →+* Γ(X, W)}
  {ι : Type} {U : ι → X.Opens} {K : Cos.{1} O}

theorem subsingleton_H_of_isAffine [IsAffine X] (hU : iSup U = ⊤)
    (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i)) (V : VB str U K) (p : ℕ) :
    Subsingleton (K.cx.H (p + 1)) := by
  have hq : (toMod U V.κ V.g).IsQuasicoherent := isQuasicoherent_toMod (isCoc V) hU
  obtain ⟨e⟩ := nonempty_cechH_equiv_H.{0, 0} (toMod U V.κ V.g) U hU ha (p + 1)
  have h1 : Subsingleton (Sheaf.H.{0} (modulesAb (toMod U V.κ V.g)) (p + 1)) :=
    (GlobalTheory.coh.toH (toMod U V.κ V.g) (p + 1)).symm.toEquiv.subsingleton
  have h2 := e.toEquiv.subsingleton
  have key : ∀ c : K.cx.H (p + 1), c = 0 := fun c => by
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have hx' : K.d (p + 1) x = 0 := hx
    have hσ : d (modulesAb (toMod U V.κ V.g)).obj U (p + 1) (cochainEquiv V (p + 1) x) = 0 := by
      rw [← cochainEquiv_d, hx', map_zero]
    have h3 := Subsingleton.elim (cls _ hσ) 0
    rw [cls_eq_zero_iff] at h3
    obtain ⟨τ, hτ⟩ := h3
    obtain ⟨y, rfl⟩ := (cochainEquiv V p).surjective τ
    rw [← cochainEquiv_d] at hτ
    have h4 := (cochainEquiv V (p + 1)).injective hτ
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨y, h4⟩
  exact ⟨fun a b => (key a).trans (key b).symm⟩

end Top

section Restrict

attribute [local instance] VB.fin

variable {X : Scheme.{0}} (W : X.Opens)

def toY {A : X.Opens} {T : W.toScheme.Opens} (h : W.ι ''ᵁ T ≤ A) : Γ(X, A) →+* Γ(W.toScheme, T) :=
  rs h

def ofY {A : X.Opens} {T : W.toScheme.Opens} (h : A ≤ W.ι ''ᵁ T) : Γ(W.toScheme, T) →+* Γ(X, A) :=
  rs h

theorem toY_ofY {A : X.Opens} {T : W.toScheme.Opens} (h : W.ι ''ᵁ T ≤ A) (h' : A ≤ W.ι ''ᵁ T)
    (x : Γ(W.toScheme, T)) : toY W h (ofY W h' x) = x :=
  (rs_rs h' h x).trans (rs_self (le_refl (W.ι ''ᵁ T)) x)

theorem ofY_toY {A : X.Opens} {T : W.toScheme.Opens} (h : W.ι ''ᵁ T ≤ A) (h' : A ≤ W.ι ''ᵁ T)
    (x : Γ(X, A)) : ofY W h' (toY W h x) = x :=
  (rs_rs h h' x).trans (rs_self _ x)

theorem rs_toY {A B : X.Opens} {T T' : W.toScheme.Opens} (h : W.ι ''ᵁ T ≤ A) (hT : T' ≤ T)
    (hAB : B ≤ A) (h' : W.ι ''ᵁ T' ≤ B) (x : Γ(X, A)) :
    rs hT (toY W h x) = toY W h' (rs hAB x) :=
  (rs_rs h (W.ι.image_mono hT) x).trans (rs_rs hAB h' x).symm

theorem toY_toY {A B : X.Opens} {T : W.toScheme.Opens} (hAB : B ≤ A) (h' : W.ι ''ᵁ T ≤ B)
    (h : W.ι ''ᵁ T ≤ A) (x : Γ(X, A)) : toY W h' (rs hAB x) = toY W h x :=
  rs_rs hAB h' x

theorem image_preimage_of_le {A : X.Opens} (h : A ≤ W) : W.ι ''ᵁ (W.ι ⁻¹ᵁ A) = A := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 h]

variable {ι : Type} {U : ι → X.Opens}

theorem capO_preimage {n : ℕ} (i : Fin n → ι) :
    capO (fun α => W.ι ⁻¹ᵁ U α) i = W.ι ⁻¹ᵁ capO U i := by
  refine SetLike.ext fun x => ?_
  rw [← SetLike.mem_coe, capO, Opens.coe_iInf, Set.mem_iInter]
  change _ ↔ W.ι x ∈ capO U i
  rw [← SetLike.mem_coe, capO, Opens.coe_iInf, Set.mem_iInter]
  rfl

theorem image_capO (hUW : ∀ α, U α ≤ W) {n : ℕ} (i : Fin (n + 1) → ι) :
    W.ι ''ᵁ capO (fun α => W.ι ⁻¹ᵁ U α) i = capO U i := by
  rw [capO_preimage, image_preimage_of_le W ((capO_le U i 0).trans (hUW _))]

theorem image_inf (hUW : ∀ α, U α ≤ W) (α β : ι) :
    W.ι ''ᵁ (W.ι ⁻¹ᵁ U α ⊓ W.ι ⁻¹ᵁ U β) = U α ⊓ U β :=
  image_preimage_of_le W (inf_le_left.trans (hUW α))

variable {O : Type} [CommRing O] {str : ∀ W : X.Opens, O →+* Γ(X, W)} {K : Cos.{1} O}

def strY (str : ∀ W : X.Opens, O →+* Γ(X, W)) (T : W.toScheme.Opens) : O →+* Γ(W.toScheme, T) :=
  str (W.ι ''ᵁ T)

theorem toY_str {A : X.Opens} {T : W.toScheme.Opens} (e : W.ι ''ᵁ T = A) (c : O) :
    toY W e.le (str A c) = strY W str T c := by
  subst e
  exact rs_self _ _

def restrictVB (hUW : ∀ α, U α ≤ W) (V : VB str U K) :
    VB (strY W str) (fun α => W.ι ⁻¹ᵁ U α) K where
  κ := V.κ
  fin := V.fin
  g α β k k' := toY W (image_inf W hUW α β).le (V.g α β k k')
  e n a :=
    { toFun := fun x i k => toY W (image_capO W hUW i).le (V.e n a x i k)
      invFun := fun t => (V.e n a).symm fun i k => ofY W (image_capO W hUW i).ge (t i k)
      left_inv := fun x => by
        apply (V.e n a).injective
        rw [AddEquiv.apply_symm_apply]
        funext i k
        exact ofY_toY W _ _ _
      right_inv := fun t => by
        funext i k
        simp only [AddEquiv.apply_symm_apply]
        exact toY_ofY W _ _ _
      map_add' := fun x y => by
        funext i k
        simp only [map_add, Pi.add_apply] }
  e_smul n a c x i k := by
    change toY W _ (V.e n a (c • x) i k) = _ * toY W _ (V.e n a x i k)
    rw [V.e_smul, map_mul, toY_str W (image_capO W hUW i)]
  e_δ n a b x i k := by
    change toY W _ (V.e (n + 1) (b.succAbove a) (K.δ n b x) i k) =
      rs _ (toY W _ (V.e n a x (i ∘ b.succAbove) k))
    rw [V.e_δ, rs_toY W _ _ (capO_comp U i b.succAbove) (image_capO W hUW i).le]
  e_chg n a b x i k := by
    change toY W _ (V.e n a x i k) = ∑ k', rs _ (toY W _ (V.g (i a) (i b) k k')) * toY W _ (V.e n b x i k')
    rw [V.e_chg n a b x i k, map_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [map_mul, rs_toY W _ _ (le_inf (capO_le U i a) (capO_le U i b)) (image_capO W hUW i).le]

end Restrict

theorem subsingleton_H : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (str : ∀ W : X.Opens, O →+* Γ(X, W)) (W : X.Opens) (hW : IsAffineOpen W)
    {ι : Type} [Fintype ι] (U : ι → X.Opens) (hU : (⨆ α, U α) = W) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i))
    (K : Cos.{1} O) (V : VB str U K) (p : ℕ), Subsingleton (K.cx.H (p + 1)) := by
  intro O _ X str W hW ι _ U hU ha K V p
  haveI : IsAffine W.toScheme := hW
  have hUW (α : ι) : U α ≤ W := hU ▸ le_iSup U α
  refine subsingleton_H_of_isAffine (X := W.toScheme) (U := fun α => W.ι ⁻¹ᵁ U α) ?_ ?_
    (restrictVB W hUW V) p
  · rw [← Scheme.Hom.preimage_iSup, hU]
    exact Scheme.Opens.ι_preimage_self W
  · intro n i
    rw [← W.ι.isAffineOpen_iff_of_isOpenImmersion]
    exact (image_capO W hUW i).symm ▸ ha n i

end GlobalTheory.CompanionTheory.VBAff
