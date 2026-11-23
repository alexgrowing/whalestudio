import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroBasicTwistOfSpecialForm

noncomputable section

open scoped Classical

open GlobalTheory.SmGL

namespace UpperTheory.TNZ.P_spLat

variable {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {I : Representation ℂ Γ V}

theorem eqvInt {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    {α : Representation ℂ Γ A} {β : Representation ℂ Γ B} (e : α.Equiv β) (g : Γ) (v : A) :
    e (α g v) = β g (e v) :=
  Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v

def eqvTrans {A B C : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] {α : Representation ℂ Γ A} {β : Representation ℂ Γ B}
    {γ : Representation ℂ Γ C} (e : α.Equiv β) (f : β.Equiv γ) : α.Equiv γ :=
  Representation.Equiv.mk (e.toLinearEquiv.trans f.toLinearEquiv) (fun g => by
    ext v
    show f (e (α g v)) = γ g (f (e v))
    rw [eqvInt e, eqvInt f])

theorem dich {A : Type} [AddCommGroup A] [Module ℂ A] {α : Representation ℂ Γ A} (hα : α.IsIrreducible)
    (X Y S : Subrepresentation I) (e : (subQuot Y X).Equiv α) :
    Y ⊓ S ≤ X ∨ Y ≤ S ⊔ X := by
  let T : Subrepresentation α :=
    ⟨((S.toSubmodule.comap Y.toSubmodule.subtype).map
        (X.toSubmodule.comap Y.toSubmodule.subtype).mkQ).map e.toLinearMap, by
      rintro g _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨_, ⟨Y.toRepresentation g v, S.apply_mem_toSubmodule g hv, rfl⟩, ?_⟩
      exact eqvInt e g (Submodule.Quotient.mk v)⟩
  rcases hα.eq_bot_or_eq_top T with hT | hT
  · left
    intro v hv
    obtain ⟨hvY, hvS⟩ := hv
    have hm : e (Submodule.Quotient.mk (⟨v, hvY⟩ : Y.toSubmodule)) ∈ T.toSubmodule :=
      ⟨_, ⟨⟨v, hvY⟩, hvS, rfl⟩, rfl⟩
    rw [hT] at hm
    have h0 : e (Submodule.Quotient.mk (⟨v, hvY⟩ : Y.toSubmodule)) = 0 := (Submodule.mem_bot ℂ).1 hm
    rw [map_eq_zero_iff e (EquivLike.injective e), Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  · right
    intro v hvY
    have hm : e (Submodule.Quotient.mk (⟨v, hvY⟩ : Y.toSubmodule)) ∈ T.toSubmodule := by
      rw [hT]; exact Submodule.mem_top
    obtain ⟨_, ⟨w, hwS, rfl⟩, hw⟩ := hm
    have hw' := EquivLike.injective e hw
    have hx0 := (Submodule.Quotient.eq (X.toSubmodule.comap Y.toSubmodule.subtype)).1 hw'
    have hx : (w : V) - v ∈ X.toSubmodule := hx0
    show v ∈ S.toSubmodule ⊔ X.toSubmodule
    refine Submodule.mem_sup.2 ⟨w, hwS, v - w, ?_, by abel⟩
    simpa using X.toSubmodule.neg_mem hx

def eqv (Z W Y X : Subrepresentation I) (hZY : Z ≤ Y) (hY : Y ≤ Z ⊔ X)
    (hW : Z ⊓ W = Z ⊓ X) : (subQuot Z W).Equiv (subQuot Y X) := by
  let f : Z.toSubmodule →ₗ[ℂ] (Y.toSubmodule ⧸ X.toSubmodule.comap Y.toSubmodule.subtype) :=
    (X.toSubmodule.comap Y.toSubmodule.subtype).mkQ ∘ₗ Submodule.inclusion hZY
  have hf : Function.Surjective f := by
    rintro ⟨⟨v, hv⟩⟩
    obtain ⟨z, hz, x, hx, rfl⟩ := Submodule.mem_sup.1 (hY hv)
    refine ⟨⟨z, hz⟩, ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    refine (Submodule.Quotient.eq _).2 ?_
    show z - (z + x) ∈ X.toSubmodule
    simpa using X.toSubmodule.neg_mem hx
  have hker : W.toSubmodule.comap Z.toSubmodule.subtype = LinearMap.ker f := by
    ext ⟨v, hv⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker, f,
      LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show v ∈ W.toSubmodule ↔ v ∈ X.toSubmodule
    have h := congrArg Subrepresentation.toSubmodule hW
    simp only [Subrepresentation.toSubmodule_inf] at h
    constructor
    · intro hw
      have : v ∈ Z.toSubmodule ⊓ W.toSubmodule := ⟨hv, hw⟩
      rw [h] at this
      exact this.2
    · intro hx
      have : v ∈ Z.toSubmodule ⊓ X.toSubmodule := ⟨hv, hx⟩
      rw [← h] at this
      exact this.2
  refine Representation.Equiv.mk ((Submodule.quotEquivOfEq _ _ hker).trans
    (f.quotKerEquivOfSurjective hf)) (fun g => ?_)
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply]
  rfl

end UpperTheory.TNZ.P_spLat

namespace UpperTheory.TNZ

open P_spLat in
theorem step_spLat : SpecialLatticeProp := by
  intro Γ V _ _ _ I d hmono hmod htop A B _ _ _ _ α β hα hβ h₁ h₂
  obtain ⟨X₁, Y₁, hXY₁, hd₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨X₂, Y₂, hXY₂, hd₂, ⟨e₂⟩⟩ := h₂
  have hY₁ : d Y₁ ≤ 1 := (hmono le_top).trans htop
  have hY₂ : d Y₂ ≤ 1 := (hmono le_top).trans htop
  have hZ : d (Y₁ ⊓ Y₂) = 1 := by
    have := hmod Y₁ Y₂
    have := (hmono (le_top : Y₁ ⊔ Y₂ ≤ ⊤)).trans htop
    have := hmono (inf_le_left : Y₁ ⊓ Y₂ ≤ Y₁)
    omega
  have hN : d (X₁ ⊔ X₂) = 0 := by
    have := hmod X₁ X₂
    omega
  set Z := Y₁ ⊓ Y₂ with hZdef
  set N := X₁ ⊔ X₂ with hNdef
  have side : ∀ (C : Type) [AddCommGroup C] [Module ℂ C] (γ : Representation ℂ Γ C), γ.IsIrreducible →
      ∀ X Y : Subrepresentation I, X ≤ Y → X ≤ N → Z ≤ Y → d X = 0 → (subQuot Y X).Equiv γ →
      Y ≤ Z ⊔ X ∧ Z ⊓ N = Z ⊓ X := by
    intro C _ _ γ hγ X Y hXY hXN hZY hX e
    refine ⟨?_, ?_⟩
    · rcases dich hγ X Y Z e with h | h
      · exfalso
        have h' : Z ≤ X := by
          have : Y ⊓ Z = Z := inf_eq_right.2 hZY
          rw [← this]; exact h
        have := hmono h'
        omega
      · exact h
    · rcases dich hγ X Y N e with h | h
      · apply le_antisymm
        · exact le_inf inf_le_left ((inf_le_inf_right N hZY).trans h)
        · exact inf_le_inf_left Z hXN
      · exfalso
        have h' : Z ≤ N := hZY.trans (h.trans (sup_le le_rfl hXN))
        have := hmono h'
        omega
  have hd1 : d X₁ = 0 := by omega
  have hd2 : d X₂ = 0 := by omega
  obtain ⟨s₁, t₁⟩ := side A α hα X₁ Y₁ hXY₁ le_sup_left inf_le_left hd1 e₁
  obtain ⟨s₂, t₂⟩ := side B β hβ X₂ Y₂ hXY₂ le_sup_right inf_le_right hd2 e₂
  exact ⟨eqvTrans (eqvTrans e₁.symm (eqv Z N Y₁ X₁ inf_le_left s₁ t₁).symm)
    (eqvTrans (eqv Z N Y₂ X₂ inf_le_right s₂ t₂) e₂)⟩

end UpperTheory.TNZ
