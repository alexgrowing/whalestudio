import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LowerSetTypesSpan

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G.Joints

section dec

variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V] {W : I → Submodule K V} {e : I → Module.End K V}

theorem mem_iSup_components_iff (h : DecSys W e) (pi : Set I) (x : V) : x ∈ (⨆ a ∈ pi, W a) ↔ ∀ a, a ∉ pi → e a x = 0 := by
  constructor
  · intro hx
    have hle : (⨆ a ∈ pi, W a) ≤ ⨅ a ∈ piᶜ, LinearMap.ker (e a) := by
      refine iSup₂_le fun b hb => ?_
      refine le_iInf₂ fun a ha => ?_
      intro y hy
      exact h.zero_on a b (fun hab => ha (hab ▸ hb)) y hy
    have := hle hx
    intro a ha
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this a ha
  · intro hx
    obtain ⟨T, hT⟩ := h.cover x
    rw [hT]
    refine Submodule.sum_mem _ fun mu _ => ?_
    by_cases hmu : mu ∈ pi
    · exact Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem hmu (h.mem mu x))
    · rw [hx mu hmu]; exact Submodule.zero_mem _

theorem mem_component_iff_fixed (h : DecSys W e) (a : I) (x : V) : x ∈ W a ↔ e a x = x := ⟨h.id_on a x, fun hx => hx ▸ h.mem a x⟩

end dec

section main

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {κ : Type} {Λ : κ → Type} {X : Type}
  (J : JointData K V κ Λ X)

def componentSum (i : κ) (pi : Set (Λ i)) : Submodule K V := ⨆ a ∈ pi, J.W i a

theorem mem_component_sum_iff (i : κ) (pi : Set (Λ i)) (x : V) : x ∈ componentSum J i pi ↔ ∀ a, a ∉ pi → J.e i a x = 0 := mem_iSup_components_iff (J.sys i) pi x

theorem projectors_commute (i j : κ) (a : Λ i) (c : Λ j) (x : V) : J.e i a (J.e j c x) = J.e j c (J.e i a x) := by
  exact LinearMap.congr_fun (J.comm i j a c) x

theorem component_sum_stable (i : κ) (pi : Set (Λ i)) (j : κ) (c : Λ j) (x : V) (hx : x ∈ componentSum J i pi) :
    J.e j c x ∈ componentSum J i pi := by
  rw [mem_component_sum_iff] at hx ⊢
  intro a ha
  rw [projectors_commute, hx a ha, map_zero]

theorem component_stable (i : κ) (a : Λ i) (j : κ) (c : Λ j) (x : V) (hx : x ∈ J.W i a) : J.e j c x ∈ J.W i a := by
  rw [mem_component_iff_fixed (J.sys i)] at hx ⊢
  rw [projectors_commute, hx]

theorem component_le_component_sum (i : κ) (pi : Set (Λ i)) (a : Λ i) (ha : a ∈ pi) : J.W i a ≤ componentSum J i pi := le_iSup₂_of_le (f := fun a (_ : a ∈ pi) => J.W i a) a ha le_rfl

theorem basis_mem_plane (x : X) : J.b x ∈ J.Pl := by
  rw [← J.span]
  exact Submodule.subset_span ⟨x, rfl⟩

def projectorProduct (lam : ∀ i, Λ i) : List κ → Module.End K V
  | [] => 1
  | i :: l => J.e i (lam i) * projectorProduct lam l

theorem projector_product_cons (lam : ∀ i, Λ i) (i : κ) (l : List κ) (x : V) :
    projectorProduct J lam (i :: l) x = J.e i (lam i) (projectorProduct J lam l x) := rfl

theorem projector_product_commute (lam : ∀ i, Λ i) (l : List κ) (j : κ) (c : Λ j) (x : V) :
    J.e j c (projectorProduct J lam l x) = projectorProduct J lam l (J.e j c x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [projector_product_cons, projector_product_cons, projectors_commute, ih]

theorem projector_product_fixed (lam : ∀ i, Λ i) (l : List κ) (x : V) (hx : ∀ i, x ∈ J.W i (lam i)) :
    projectorProduct J lam l x = x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [projector_product_cons, ih]
    exact (J.sys i).id_on _ x (hx i)

theorem projector_product_kill (lam : ∀ i, Λ i) (l : List κ) (j : κ) (hj : j ∈ l) (y : V) (hy : J.e j (lam j) y = 0) :
    projectorProduct J lam l y = 0 := by
  induction l with
  | nil => simp at hj
  | cons i l ih =>
    rw [projector_product_cons]
    rcases List.mem_cons.mp hj with rfl | hj'
    · rw [projector_product_commute, hy, map_zero]
    · rw [ih hj', map_zero]

theorem projector_product_mem_component (lam : ∀ i, Λ i) (l : List κ) (j : κ) (hj : j ∈ l) (x : V) :
    projectorProduct J lam l x ∈ J.W j (lam j) := by
  induction l with
  | nil => simp at hj
  | cons i l ih =>
    rw [projector_product_cons]
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact (J.sys _).mem _ _
    · exact component_stable J j (lam j) i (lam i) _ (ih hj')

theorem projector_product_stable (lam : ∀ i, Λ i) (l : List κ) (S : Submodule K V) (hS : ∀ i a, ∀ x ∈ S, J.e i a x ∈ S) (x : V)
    (hx : x ∈ S) : projectorProduct J lam l x ∈ S := by
  induction l with
  | nil => exact hx
  | cons i l ih =>
    rw [projector_product_cons]
    exact hS i (lam i) _ ih

def lowerLabels (lam : ∀ i, Λ i) (i : κ) : Set (Λ i) := {a | J.dom i a ∧ J.le i a (lam i)}

def strictLowerLabels (lam : ∀ i, Λ i) (i : κ) : Set (Λ i) := {a | J.dom i a ∧ J.le i a (lam i) ∧ a ≠ lam i}

theorem lower_part_eq_span (lam : ∀ i, Λ i) (i : κ) :
    J.Pl ⊓ componentSum J i (lowerLabels J lam i) = Submodule.span K (J.b '' {x | J.P x i ∈ lowerLabels J lam i}) := J.low i (lowerLabels J lam i) (fun a ha => ha.1) (fun a ha c hc hca => ⟨hc, J.le_trans i c a (lam i) hca ha.2⟩)

theorem strict_lower_part_eq_span (lam : ∀ i, Λ i) (i : κ) :
    J.Pl ⊓ componentSum J i (strictLowerLabels J lam i) = Submodule.span K (J.b '' {x | J.P x i ∈ strictLowerLabels J lam i}) := by
  exact J.low i (strictLowerLabels J lam i) (fun a ha => ha.1) (fun a ha c hc hca => ⟨hc, J.le_trans i c a (lam i) hca ha.2.1,
    fun hcl => ha.2.2 (J.le_antisymm i a (lam i) ha.2.1 (hcl ▸ hca))⟩)

def jointLowerPart (lam : ∀ i, Λ i) : Submodule K V := J.Pl ⊓ ⨅ i, componentSum J i (lowerLabels J lam i)

def strictLowerPart (lam : ∀ i, Λ i) (j : κ) : Submodule K V := jointLowerPart J lam ⊓ componentSum J j (strictLowerLabels J lam j)

def strictJointLower (lam : ∀ i, Λ i) : Submodule K V := ⨆ j, strictLowerPart J lam j

theorem joint_lower_part_stable (lam : ∀ i, Λ i) (i : κ) (a : Λ i) (x : V) (hx : x ∈ jointLowerPart J lam) :
    J.e i a x ∈ jointLowerPart J lam := by
  simp only [jointLowerPart, Submodule.mem_inf, Submodule.mem_iInf] at hx ⊢
  exact ⟨J.stab i a x hx.1, fun k => component_sum_stable J k _ i a x (hx.2 k)⟩

theorem strict_joint_lower_le (lam : ∀ i, Λ i) : strictJointLower J lam ≤ jointLowerPart J lam := iSup_le fun j => inf_le_left

theorem sub_projector_mem_strict (lam : ∀ i, Λ i) (k : κ) (x : V) (hx : x ∈ jointLowerPart J lam) :
    x - J.e k (lam k) x ∈ strictLowerPart J lam k := by
  have hxM := hx
  simp only [jointLowerPart, Submodule.mem_inf, Submodule.mem_iInf] at hxM
  simp only [strictLowerPart, Submodule.mem_inf]
  refine ⟨Submodule.sub_mem _ hx (joint_lower_part_stable J lam k (lam k) x hx), ?_⟩
  rw [mem_component_sum_iff]
  intro a ha
  rw [map_sub]
  by_cases hal : a = lam k
  · subst hal
    rw [(J.sys k).id_on _ _ ((J.sys k).mem _ x), sub_self]
  · have h1 : J.e k a x = 0 := by
      have := (mem_component_sum_iff J k _ x).mp (hxM.2 k)
      apply this
      intro hle
      exact ha ⟨hle.1, hle.2, hal⟩
    have h2 : J.e k a (J.e k (lam k) x) = 0 := (J.sys k).zero_on a (lam k) (Ne.symm hal) _ ((J.sys k).mem _ x)
    rw [h1, h2, sub_zero]

theorem sub_projector_product_mem_strict (lam : ∀ i, Λ i) (l : List κ) (x : V) (hx : x ∈ jointLowerPart J lam) :
    x - projectorProduct J lam l x ∈ strictJointLower J lam := by
  induction l with
  | nil => simp [projectorProduct]
  | cons i l ih =>
    rw [projector_product_cons]
    have hy : projectorProduct J lam l x ∈ jointLowerPart J lam :=
      projector_product_stable J lam l _ (fun i a z hz => joint_lower_part_stable J lam i a z hz) x hx
    have h2 := sub_projector_mem_strict J lam i _ hy
    have : x - J.e i (lam i) (projectorProduct J lam l x) =
        (x - projectorProduct J lam l x) + (projectorProduct J lam l x - J.e i (lam i) (projectorProduct J lam l x)) := by abel
    rw [this]
    exact Submodule.add_mem _ ih (Submodule.mem_iSup_of_mem i h2)

theorem basis_mem_joint_lower_part (lam : ∀ i, Λ i) (x : X) (hx : ∀ i, J.P x i ∈ lowerLabels J lam i) : J.b x ∈ jointLowerPart J lam := by
  simp only [jointLowerPart, Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨basis_mem_plane J x, fun i => ?_⟩
  have : J.b x ∈ J.Pl ⊓ componentSum J i (lowerLabels J lam i) := by
    rw [lower_part_eq_span]
    exact Submodule.subset_span ⟨x, hx i, rfl⟩
  exact this.2

private theorem mem_span_image_iInter_of_forall_mem_span {ι' : Type} [Nonempty ι'] (A : ι' → Set X) (x : V)
    (hA : ∀ k, x ∈ Submodule.span K (J.b '' A k)) : x ∈ Submodule.span K (J.b '' ⋂ k, A k) := by
  obtain ⟨k0⟩ := ‹Nonempty ι'›
  obtain ⟨l0, hl0, hl0x⟩ := (Finsupp.mem_span_image_iff_linearCombination K).mp (hA k0)
  refine (Finsupp.mem_span_image_iff_linearCombination K).mpr ⟨l0, ?_, hl0x⟩
  rw [Finsupp.mem_supported]
  intro y hy
  rw [Set.mem_iInter]
  intro k
  obtain ⟨lk, hlk, hlkx⟩ := (Finsupp.mem_span_image_iff_linearCombination K).mp (hA k)
  have hkk : lk = l0 := J.li (hlkx.trans hl0x.symm)
  rw [hkk, Finsupp.mem_supported] at hlk
  exact hlk hy

theorem joint_lower_part_eq_span [Nonempty κ] (lam : ∀ i, Λ i) :
    jointLowerPart J lam = Submodule.span K (J.b '' {x | ∀ i, J.P x i ∈ lowerLabels J lam i}) := by
  apply le_antisymm
  · intro x hx
    have hx' := hx
    simp only [jointLowerPart, Submodule.mem_inf, Submodule.mem_iInf] at hx'
    have hA : ∀ i, x ∈ Submodule.span K (J.b '' {y | J.P y i ∈ lowerLabels J lam i}) := fun i => by
      rw [← lower_part_eq_span]; exact Submodule.mem_inf.mpr ⟨hx'.1, hx'.2 i⟩
    have := mem_span_image_iInter_of_forall_mem_span J (fun i => {y | J.P y i ∈ lowerLabels J lam i}) x hA
    have hset : {y | ∀ i, J.P y i ∈ lowerLabels J lam i} = ⋂ i, {y | J.P y i ∈ lowerLabels J lam i} := by
      ext y; simp
    rw [hset]; exact this
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact basis_mem_joint_lower_part J lam y hy

theorem strict_joint_lower_eq_span [Nonempty κ] (lam : ∀ i, Λ i) :
    strictJointLower J lam = Submodule.span K (J.b '' {x | (∀ i, J.P x i ∈ lowerLabels J lam i) ∧ J.P x ≠ lam}) := by
  apply le_antisymm
  · refine iSup_le fun j => ?_
    intro x hx
    have hx' := hx
    simp only [strictLowerPart, jointLowerPart, Submodule.mem_inf, Submodule.mem_iInf] at hx'
    let A : Option κ → Set X := fun o =>
      o.elim {y | J.P y j ∈ strictLowerLabels J lam j} (fun i => {y | J.P y i ∈ lowerLabels J lam i})
    have hA : ∀ o, x ∈ Submodule.span K (J.b '' A o) := by
      intro o
      cases o with
      | none =>
        show x ∈ Submodule.span K (J.b '' {y | J.P y j ∈ strictLowerLabels J lam j})
        rw [← strict_lower_part_eq_span]; exact Submodule.mem_inf.mpr ⟨hx'.1.1, hx'.2⟩
      | some i =>
        show x ∈ Submodule.span K (J.b '' {y | J.P y i ∈ lowerLabels J lam i})
        rw [← lower_part_eq_span]; exact Submodule.mem_inf.mpr ⟨hx'.1.1, hx'.1.2 i⟩
    have := mem_span_image_iInter_of_forall_mem_span J A x hA
    refine Submodule.span_mono (Set.image_mono ?_) this
    intro y hy
    rw [Set.mem_iInter] at hy
    refine ⟨fun i => hy (some i), fun h => ?_⟩
    have h0 : J.P y j ∈ strictLowerLabels J lam j := hy none
    exact h0.2.2 (congrFun h j)
  · rw [Submodule.span_le]
    rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
    obtain ⟨j, hj⟩ : ∃ j, J.P y j ≠ lam j := by
      by_contra hcon
      push_neg at hcon
      exact hy2 (funext hcon)
    refine Submodule.mem_iSup_of_mem j ?_
    simp only [strictLowerPart, Submodule.mem_inf]
    refine ⟨basis_mem_joint_lower_part J lam y hy1, ?_⟩
    have : J.b y ∈ J.Pl ⊓ componentSum J j (strictLowerLabels J lam j) := by
      rw [strict_lower_part_eq_span]
      exact Submodule.subset_span ⟨y, ⟨J.Pdom y j, (hy1 j).2, hj⟩, rfl⟩
    exact (Submodule.mem_inf.mp this).2

end main

theorem restJointDim : RestJointDim := by
  intro K V _ _ _ κ _ _ Λ X _ J lam
  classical
  haveI : Fintype X := Fintype.ofFinite X
  haveI hPl : FiniteDimensional K J.Pl := J.span ▸ FiniteDimensional.span_of_finite K (Set.finite_range J.b)
  set U := J.Pl ⊓ ⨅ i, J.W i (lam i) with hU
  haveI : FiniteDimensional K U := Submodule.finiteDimensional_of_le (inf_le_left : U ≤ J.Pl)
  haveI : FiniteDimensional K (strictJointLower J lam) :=
    Submodule.finiteDimensional_of_le ((strict_joint_lower_le J lam).trans inf_le_left)
  have hl : ∀ i, i ∈ (Finset.univ : Finset κ).toList := fun i => Finset.mem_toList.mpr (Finset.mem_univ i)
  set l := (Finset.univ : Finset κ).toList
  have hPU : ∀ x ∈ J.Pl, projectorProduct J lam l x ∈ U := fun x hx =>
    Submodule.mem_inf.mpr ⟨projector_product_stable J lam l J.Pl J.stab x hx,
      (Submodule.mem_iInf _).mpr fun i => projector_product_mem_component J lam l i (hl i) x⟩
  have hfix : ∀ x ∈ U, projectorProduct J lam l x = x := fun x hx =>
    projector_product_fixed J lam l x fun i => (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hx).2 i
  have hkill : ∀ y ∈ strictJointLower J lam, projectorProduct J lam l y = 0 := by
    intro y hy
    refine Submodule.iSup_induction (fun j => strictLowerPart J lam j) (motive := fun z => projectorProduct J lam l z = 0) hy
      (fun j z hz => ?_) (map_zero _) (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
    have hz' := (Submodule.mem_inf.mp hz).2
    rw [mem_component_sum_iff] at hz'
    exact projector_product_kill J lam l j (hl j) z (hz' (lam j) (fun h => h.2.2 rfl))
  have hUle : U ≤ jointLowerPart J lam := by
    intro x hx
    have hx' := Submodule.mem_inf.mp hx
    simp only [jointLowerPart, Submodule.mem_inf, Submodule.mem_iInf]
    refine ⟨hx'.1, fun i => ?_⟩
    rw [mem_component_sum_iff]
    intro a ha
    have hxi := (Submodule.mem_iInf _).mp hx'.2 i
    by_cases hal : a = lam i
    · subst hal
      have hnd : ¬ J.dom i (lam i) := fun hd => ha ⟨hd, J.le_refl i _⟩
      rw [J.bot i _ hnd, Submodule.mem_bot] at hxi
      rw [hxi, map_zero]
    · exact (J.sys i).zero_on a (lam i) (Ne.symm hal) x hxi
  have hsup : U ⊔ strictJointLower J lam = jointLowerPart J lam := by
    apply le_antisymm (sup_le hUle (strict_joint_lower_le J lam))
    intro x hx
    have hxP : x ∈ J.Pl := (Submodule.mem_inf.mp hx).1
    have hsplit : x = projectorProduct J lam l x + (x - projectorProduct J lam l x) := by abel
    rw [hsplit]
    exact Submodule.add_mem_sup (hPU x hxP) (sub_projector_product_mem_strict J lam l x hx)
  have hinf : U ⊓ strictJointLower J lam = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 := hfix x (Submodule.mem_inf.mp hx).1
    have h2 := hkill x (Submodule.mem_inf.mp hx).2
    rw [Submodule.mem_bot, ← h1, h2]
  have hfin : ∀ s : Set X, Module.finrank K (Submodule.span K (J.b '' s)) = Nat.card s := by
    intro s
    rw [Set.image_eq_range]
    exact (finrank_span_eq_card (J.li.comp _ Subtype.val_injective)).trans Nat.card_eq_fintype_card.symm
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq U (strictJointLower J lam)
  rw [hsup, hinf, finrank_bot, add_zero, joint_lower_part_eq_span, strict_joint_lower_eq_span, hfin, hfin] at hdim
  have hset : {x | ∀ i, J.P x i ∈ lowerLabels J lam i} =
      {x | (∀ i, J.P x i ∈ lowerLabels J lam i) ∧ J.P x ≠ lam} ∪ {x | J.P x = lam} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro h
      by_cases hx : J.P x = lam
      · exact Or.inr hx
      · exact Or.inl ⟨h, hx⟩
    · rintro (h | h)
      · exact h.1
      · intro i
        have hd := J.Pdom x i
        rw [h] at hd ⊢
        exact ⟨hd, J.le_refl i _⟩
  have hdisj : Disjoint {x | (∀ i, J.P x i ∈ lowerLabels J lam i) ∧ J.P x ≠ lam} {x | J.P x = lam} := by
    rw [Set.disjoint_left]
    intro x h1 h2
    exact h1.2 h2
  have hcard : Nat.card {x | ∀ i, J.P x i ∈ lowerLabels J lam i} =
      Nat.card {x | (∀ i, J.P x i ∈ lowerLabels J lam i) ∧ J.P x ≠ lam} + Nat.card {x // J.P x = lam} := by
    rw [hset, Nat.card_coe_set_eq, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    rfl
  omega

section sum

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {κ : Type} {Λ : κ → Type} {X : Type}
  (J : JointData K V κ Λ X)

theorem mem_iSup_of_split [DecidableEq κ] (pi : ∀ i, Set (Λ i)) (s : Finset κ) :
    ∀ (y : V) (q : ∀ i, Λ i), (∀ i, q i ∈ pi i) → (∀ i, y ∈ componentSum J i (pi i)) → (∀ i, i ∉ s → y ∈ J.W i (q i)) →
      y ∈ ⨆ q ∈ {q : ∀ i, Λ i | ∀ i, q i ∈ pi i}, ⨅ i, J.W i (q i) := by
  induction s using Finset.induction_on with
  | empty =>
    intro y q hq _ hW
    refine Submodule.mem_iSup_of_mem q (Submodule.mem_iSup_of_mem hq ?_)
    exact (Submodule.mem_iInf _).mpr fun i => hW i (by simp)
  | @insert k s hks ih =>
    intro y q hq hT hW
    obtain ⟨T, hTy⟩ := (J.sys k).cover y
    rw [hTy]
    refine Submodule.sum_mem _ fun a _ => ?_
    by_cases ha : a ∈ pi k
    · apply ih (J.e k a y) (Function.update q k a)
      · intro i
        by_cases hik : i = k
        · subst hik; simpa using ha
        · simpa [hik] using hq i
      · intro i; exact component_sum_stable J i (pi i) k a y (hT i)
      · intro i hi
        by_cases hik : i = k
        · subst hik; simpa using (J.sys i).mem a y
        · have hW' := hW i (fun h => by
            rcases Finset.mem_insert.mp h with h' | h'
            · exact hik h'
            · exact hi h')
          simpa [hik] using component_stable J i (q i) k a y hW'
    · rw [(mem_component_sum_iff J k (pi k) y).mp (hT k) a ha]
      exact Submodule.zero_mem _

end sum

theorem restJointSum : RestJointSum := by
  intro K V _ _ _ κ _ _ Λ X _ J pi hdom hdown
  classical
  have hlowi : ∀ i, J.Pl ⊓ componentSum J i (pi i) = Submodule.span K (J.b '' {x | J.P x i ∈ pi i}) :=
    fun i => J.low i (pi i) (hdom i) (hdown i)
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP, hxS⟩ := Submodule.mem_inf.mp hx
    have hle : (⨆ q ∈ {q : ∀ i, Λ i | ∀ i, q i ∈ pi i}, ⨅ i, J.W i (q i)) ≤ ⨅ i, componentSum J i (pi i) :=
      iSup₂_le fun q hq => le_iInf fun i => (iInf_le _ i).trans (component_le_component_sum J i (pi i) (q i) (hq i))
    have hxT := (Submodule.mem_iInf _).mp (hle hxS)
    have hA : ∀ i, x ∈ Submodule.span K (J.b '' {y | J.P y i ∈ pi i}) := fun i => by
      rw [← hlowi]; exact Submodule.mem_inf.mpr ⟨hxP, hxT i⟩
    have := mem_span_image_iInter_of_forall_mem_span J (fun i => {y | J.P y i ∈ pi i}) x hA
    have hset : {y | ∀ i, J.P y i ∈ pi i} = ⋂ i, {y | J.P y i ∈ pi i} := by ext y; simp
    rw [hset]; exact this
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    refine Submodule.mem_inf.mpr ⟨basis_mem_plane J y, ?_⟩
    apply mem_iSup_of_split J pi Finset.univ (J.b y) (J.P y) hy
    · intro i
      have : J.b y ∈ J.Pl ⊓ componentSum J i (pi i) := by
        rw [hlowi]; exact Submodule.subset_span ⟨y, hy i, rfl⟩
      exact (Submodule.mem_inf.mp this).2
    · intro i hi; exact absurd (Finset.mem_univ i) hi

end Formalism.MainNotions.G.ColumnFamilies
