import Mathlib

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.CechLevelIsoPf.Gen

universe v u
variable {C : Type u} [Category.{v} C]

def stepLimit {S X W W' : C} {f : X ⟶ S} {b : W ⟶ S} {n : ℕ} (π : Fin (n+1) → (W ⟶ X))
    (hπ : ∀ i, π i ≫ f = b) (hc : IsLimit (WidePullbackCone.mk (f := fun _ : Fin (n+1) => f) b π hπ))
    (q : W' ⟶ W) (r : W' ⟶ X) (hpb : IsPullback q r b f)
    (h' : ∀ i, (Fin.lastCases r (fun i => q ≫ π i) i : W' ⟶ X) ≫ f = q ≫ b) :
    IsLimit (WidePullbackCone.mk (f := fun _ : Fin (n+2) => f) (q ≫ b) (Fin.lastCases r (fun i => q ≫ π i)) h') := by
  have L : ∀ t : WidePullbackCone (fun _ : Fin (n+2) => f), ∃ l : t.pt ⟶ W,
      l ≫ b = t.base ∧ ∀ i : Fin (n+1), l ≫ π i = t.π (Fin.castSucc i) := fun t =>
    ⟨WidePullbackCone.IsLimit.lift hc t.base (fun i => t.π (Fin.castSucc i)) (fun i => by simp),
      WidePullbackCone.IsLimit.lift_base hc _ _ _, fun i => WidePullbackCone.IsLimit.lift_π hc _ _ _ i⟩
  choose l hl1 hl2 using L
  have hw : ∀ t : WidePullbackCone (fun _ : Fin (n+2) => f), l t ≫ b = t.π (Fin.last _) ≫ f := fun t => by
    rw [hl1]; simp
  refine WidePullbackCone.IsLimit.mk _ (fun t => hpb.lift (l t) (t.π (Fin.last _)) (hw t)) ?_ ?_ ?_
  · intro t
    have : (hpb.lift (l t) (t.π (Fin.last _)) (hw t) : t.pt ⟶ W') ≫ q ≫ b = t.base := by
      rw [IsPullback.lift_fst_assoc, hl1]
    exact this
  · intro t i
    have : (hpb.lift (l t) (t.π (Fin.last _)) (hw t) : t.pt ⟶ W') ≫ Fin.lastCases r (fun i => q ≫ π i) i = t.π i := by
      induction i using Fin.lastCases with
      | last => rw [Fin.lastCases_last, IsPullback.lift_snd]
      | cast i => rw [Fin.lastCases_castSucc, IsPullback.lift_fst_assoc, hl2]
    exact this
  · intro t m hb hπ'
    have key : ∀ m : t.pt ⟶ W', m ≫ q ≫ b = t.base → (∀ i, m ≫ Fin.lastCases r (fun i => q ≫ π i) i = t.π i) →
        m = hpb.lift (l t) (t.π (Fin.last _)) (hw t) := by
      intro m hb hπ'
      apply hpb.hom_ext
      · rw [IsPullback.lift_fst]
        apply WidePullbackCone.IsLimit.hom_ext hc
        · change (m ≫ q) ≫ b = l t ≫ b
          rw [Category.assoc, hb, hl1]
        · intro i
          change (m ≫ q) ≫ π i = l t ≫ π i
          rw [Category.assoc, hl2, ← hπ' (Fin.castSucc i), Fin.lastCases_castSucc]
      · rw [IsPullback.lift_snd, ← hπ' (Fin.last _), Fin.lastCases_last]
    exact key m hb hπ'

def baseChangeLimit {S S' X X' W W' : C} {f : X ⟶ S} {b : W ⟶ S} {ι : Type*} (π : ι → (W ⟶ X))
    (hπ : ∀ i, π i ≫ f = b) (hc : IsLimit (WidePullbackCone.mk (f := fun _ : ι => f) b π hπ))
    {g : S' ⟶ S} {f' : X' ⟶ S'} {gX : X' ⟶ X} (hX : IsPullback gX f' f g)
    {b' : W' ⟶ S'} {gW : W' ⟶ W} (hW : IsPullback gW b' b g) (π' : ι → (W' ⟶ X'))
    (hπ' : ∀ i, π' i ≫ f' = b') (hgi : ∀ i, π' i ≫ gX = gW ≫ π i) :
    IsLimit (WidePullbackCone.mk (f := fun _ : ι => f') b' π' hπ') := by
  have L : ∀ t : WidePullbackCone (fun _ : ι => f'), ∃ l : t.pt ⟶ W,
      l ≫ b = t.base ≫ g ∧ ∀ i, l ≫ π i = t.π i ≫ gX := fun t =>
    ⟨WidePullbackCone.IsLimit.lift hc (t.base ≫ g) (fun i => t.π i ≫ gX)
      (fun i => by rw [Category.assoc, hX.w, ← Category.assoc, WidePullbackCone.condition]),
      WidePullbackCone.IsLimit.lift_base hc _ _ _, fun i => WidePullbackCone.IsLimit.lift_π hc _ _ _ i⟩
  choose l hl1 hl2 using L
  refine WidePullbackCone.IsLimit.mk _ (fun t => hW.lift (l t) t.base (hl1 t)) ?_ ?_ ?_
  · intro t
    have : (hW.lift (l t) t.base (hl1 t) : t.pt ⟶ W') ≫ b' = t.base := IsPullback.lift_snd _ _ _ _
    exact this
  · intro t i
    have : (hW.lift (l t) t.base (hl1 t) : t.pt ⟶ W') ≫ π' i = t.π i := by
      apply hX.hom_ext
      · rw [Category.assoc, hgi, IsPullback.lift_fst_assoc, hl2]
      · rw [Category.assoc, hπ', IsPullback.lift_snd, WidePullbackCone.condition]
    exact this
  · intro t m hb hπ''
    have key : ∀ m : t.pt ⟶ W', m ≫ b' = t.base → (∀ i, m ≫ π' i = t.π i) → m = hW.lift (l t) t.base (hl1 t) := by
      intro m hb hπ''
      apply hW.hom_ext
      · rw [IsPullback.lift_fst]
        apply WidePullbackCone.IsLimit.hom_ext hc
        · change (m ≫ gW) ≫ b = l t ≫ b
          rw [Category.assoc, hW.w, ← Category.assoc, hb, hl1]
        · intro i
          change (m ≫ gW) ≫ π i = l t ≫ π i
          rw [Category.assoc, ← hgi, ← Category.assoc, hπ'', hl2]
      · rw [IsPullback.lift_snd, hb]
    exact key m hb hπ''

end LateralTheory.E.CechLevelIsoPf.Gen
