import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Proof.exists_semisimplification'

variable {k Γ : Type} [Field k] [Group Γ] {V : Type} [AddCommGroup V] [Module k V]

def glue (ρ s : Representation k Γ V) (U : Submodule k V) (p : V →ₗ[k] V) (hp : ∀ v, p v ∈ U)
    (hpU : ∀ u ∈ U, p u = u) (hρ : Stable ρ U) (hs : Stable s U) : Representation k Γ V where
  toFun g := s g ∘ₗ p + (LinearMap.id - p) ∘ₗ ρ g ∘ₗ (LinearMap.id - p)
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp [hpU _ (hp v)]
  map_mul' g h := by
    refine LinearMap.ext fun v => ?_
    have h1 : p (s h (p v)) = s h (p v) := hpU _ (hs h _ (hp v))
    have h2 : ∀ x, p (p x) = p x := fun x => hpU _ (hp x)
    have h3 : ∀ x, p (ρ g (p x)) = ρ g (p x) := fun x => hpU _ (hρ g _ (hp x))
    have h4 : p (ρ h (p v)) = ρ h (p v) := hpU _ (hρ h _ (hp v))
    have h5 : p (ρ g (ρ h (p v))) = ρ g (ρ h (p v)) := hpU _ (hρ g _ (hρ h _ (hp v)))
    simp [h1, h2, h3, h4, h5]

theorem glue_apply (ρ s : Representation k Γ V) (U : Submodule k V) (p : V →ₗ[k] V) (hp : ∀ v, p v ∈ U)
    (hpU : ∀ u ∈ U, p u = u) (hρ : Stable ρ U) (hs : Stable s U) (g : Γ) (v : V) :
    glue ρ s U p hp hpU hρ hs g v = s g (p v) + (ρ g (v - p v) - p (ρ g (v - p v))) := rfl

def Partial (ρ : Representation k Γ V) (U : Submodule k V) : Prop :=
  ∃ (s : Representation k Γ V) (m : ℕ) (Ws : ℕ → Submodule k V),
    Stable s U ∧
    (∀ W ≤ U, Stable s W → ∃ W', Stable s W' ∧ Disjoint W W' ∧ W ⊔ W' = U) ∧
    (∀ j < m, Stable s (Ws j)) ∧ (Finset.range m).SupIndep Ws ∧ (Finset.range m).sup Ws = U ∧
    ∀ j < m, ∀ g, ∀ v ∈ Ws j, ρ g v - s g v ∈ (Finset.range j).sup Ws

theorem partial_bot (ρ : Representation k Γ V) : Partial ρ ⊥ := by
  unfold Partial
  have hb : Stable ρ (⊥ : Submodule k V) := by
    intro g v hv
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  refine ⟨ρ, 0, fun _ => ⊥, hb, ?_, ?_, ?_, ?_, ?_⟩
  · intro W hW _
    refine ⟨⊥, hb, disjoint_bot_right, ?_⟩
    rw [le_bot_iff.mp hW, bot_sup_eq]
  · intro j hj
    exact absurd hj (Nat.not_lt_zero j)
  · simp
  · simp
  · intro j hj
    exact absurd hj (Nat.not_lt_zero j)

private theorem stable_sup' (f : Representation k Γ V) (A B : Submodule k V) (hA : Stable f A)
    (hB : Stable f B) : Stable f (A ⊔ B) := by
  intro g x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.add_mem_sup (hA g a ha) (hB g b hb)

theorem partial_step (ρ : Representation k Γ V) (U U' : Submodule k V) (hU : Stable ρ U)
    (hU' : Stable ρ U') (hle : U' ≤ U)
    (hmax : ∀ X, Stable ρ X → U' ≤ X → X ≤ U → X = U' ∨ X = U) (h : Partial ρ U') : Partial ρ U := by
  obtain ⟨s, m, Ws, hsU', hcomp, hWst, hind, hsup, htri⟩ := h
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U'
  obtain ⟨p, hp, hpU⟩ : ∃ p : V →ₗ[k] V, (∀ v, p v ∈ U') ∧ ∀ u ∈ U', p u = u :=
    ⟨U'.projection C hC, fun v => Submodule.projection_apply_mem hC v,
      fun u hu => Submodule.projection_apply_left hC ⟨u, hu⟩⟩
  have hpp : ∀ v, p (p v) = p v := fun v => hpU _ (hp v)
  set s' := glue ρ s U' p hp hpU hU' hsU' with hs'
  have hA : ∀ g, ∀ u ∈ U', s' g u = s g u := by
    intro g u hu
    rw [hs', glue_apply, hpU u hu, sub_self, map_zero, map_zero, sub_zero, add_zero]
  have hB : ∀ g w, p w = 0 → s' g w = ρ g w - p (ρ g w) := by
    intro g w hw
    rw [hs', glue_apply, hw, map_zero, sub_zero, zero_add]
  have hD : ∀ g v, s' g (v - p v) = s' g v - p (s' g v) := by
    intro g v
    have e1 : p (v - p v) = 0 := by rw [map_sub, hpp, sub_self]
    have e2 : p (s g (p v)) = s g (p v) := hpU _ (hsU' g _ (hp v))
    have e3 : s' g v = s g (p v) + (ρ g (v - p v) - p (ρ g (v - p v))) := by rw [hs', glue_apply]
    rw [hB g _ e1, e3, map_add, e2]
    generalize ρ g (v - p v) = x
    rw [map_sub, hpp, sub_self, add_zero, add_sub_cancel_left]
  set Wm : Submodule k V := U ⊓ LinearMap.ker p with hWm
  have hUle : ∀ v, p v ∈ U := fun v => hle (hp v)
  have hWmst : Stable s' Wm := by
    intro g w hw
    have hwk : p w = 0 := hw.2
    rw [hB g w hwk]
    refine ⟨sub_mem (hU g w hw.1) (hUle _), ?_⟩
    show p (ρ g w - p (ρ g w)) = 0
    rw [map_sub, hpp, sub_self]
  have hdisj : Disjoint U' Wm := by
    rw [Submodule.disjoint_def]
    intro x hx hxW
    have h0 : p x = 0 := hxW.2
    rw [← hpU x hx, h0]
  have hsupU : U' ⊔ Wm = U := by
    refine le_antisymm (sup_le hle inf_le_left) ?_
    intro u hu
    refine Submodule.mem_sup.mpr ⟨p u, hp u, u - p u, ⟨sub_mem hu (hUle u), ?_⟩, add_sub_cancel _ _⟩
    show p (u - p u) = 0
    rw [map_sub, hpp, sub_self]
  have hs'U' : Stable s' U' := by
    intro g u hu
    rw [hA g u hu]
    exact hsU' g u hu
  have hs'U : Stable s' U := hsupU ▸ stable_sup' s' U' Wm hs'U' hWmst
  have hirr : ∀ X ≤ Wm, Stable s' X → X = ⊥ ∨ X = Wm := by
    intro X hX hXs
    have hρX : Stable ρ (U' ⊔ X) := by
      intro g x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      have hbk : p b = 0 := (hX hb).2
      have hρb : ρ g b = p (ρ g b) + s' g b := by rw [hB g b hbk]; abel
      rw [map_add, hρb, ← add_assoc]
      exact Submodule.add_mem_sup (add_mem (hU' g a ha) (hp _)) (hXs g b hb)
    rcases hmax (U' ⊔ X) hρX le_sup_left (sup_le hle (hX.trans inf_le_left)) with h1 | h1
    · left
      exact le_bot_iff.mp (hdisj (h1 ▸ le_sup_right) hX)
    · right
      refine le_antisymm hX ?_
      intro w hw
      have hwU : w ∈ U' ⊔ X := h1 ▸ hw.1
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hwU
      have haW : a ∈ Wm := by
        have := sub_mem hw (hX hb)
        rwa [add_sub_cancel_right] at this
      have ha0 : a = 0 := Submodule.disjoint_def.mp hdisj a ha haW
      rw [ha0, zero_add]
      exact hb
  have hWsle : ∀ j < m, Ws j ≤ U' := fun j hj => hsup ▸ Finset.le_sup (Finset.mem_range.mpr hj)
  have hsuple : ∀ t ⊆ Finset.range m, t.sup Ws ≤ U' :=
    fun t ht => Finset.sup_le fun j hj => hWsle j (Finset.mem_range.mp (ht hj))
  unfold Partial
  refine ⟨s', m + 1, fun j => if j < m then Ws j else Wm, hs'U, ?_, ?_, ?_, ?_, ?_⟩
  · intro W hWU hW
    set X : Submodule k V := W.map (LinearMap.id - p) with hX
    have hXmem : ∀ w ∈ W, w - p w ∈ X := fun w hw => ⟨w, hw, rfl⟩
    have hXWm : X ≤ Wm := by
      rintro x ⟨w, hw, rfl⟩
      refine ⟨sub_mem (hWU hw) (hUle w), ?_⟩
      show p (w - p w) = 0
      rw [map_sub, hpp, sub_self]
    have hXs : Stable s' X := by
      rintro g x ⟨w, hw, rfl⟩
      show s' g (w - p w) ∈ X
      rw [hD]
      exact hXmem _ (hW g w hw)
    rcases hirr X hXWm hXs with h0 | h0
    · have hWU' : W ≤ U' := by
        intro w hw
        have h1 : w - p w ∈ X := hXmem w hw
        rw [h0, Submodule.mem_bot, sub_eq_zero] at h1
        rw [h1]
        exact hp w
      have hWs : Stable s W := by
        intro g w hw
        rw [← hA g w (hWU' hw)]
        exact hW g w hw
      obtain ⟨W'', hW''s, hdis, hsup'⟩ := hcomp W hWU' hWs
      have hW''le : W'' ≤ U' := hsup' ▸ le_sup_right
      have hW''s' : Stable s' W'' := by
        intro g x hx
        rw [hA g x (hW''le hx)]
        exact hW''s g x hx
      refine ⟨W'' ⊔ Wm, stable_sup' s' W'' Wm hW''s' hWmst, ?_, ?_⟩
      · exact hdis.disjoint_sup_right_of_disjoint_sup_left (hsup' ▸ hdisj)
      · rw [← sup_assoc, hsup', hsupU]
    · have hYs : Stable s (W ⊓ U') := by
        intro g y hy
        refine ⟨?_, hsU' g y hy.2⟩
        rw [← hA g y hy.2]
        exact hW g y hy.1
      obtain ⟨C', hC's, hdis', hsup''⟩ := hcomp (W ⊓ U') inf_le_right hYs
      have hC'le : C' ≤ U' := hsup'' ▸ le_sup_right
      refine ⟨C', ?_, ?_, ?_⟩
      · intro g x hx
        rw [hA g x (hC'le hx)]
        exact hC's g x hx
      · rw [Submodule.disjoint_def]
        intro x hxW hxC
        exact Submodule.disjoint_def.mp hdis' x ⟨hxW, hC'le hxC⟩ hxC
      · refine le_antisymm (sup_le hWU (hC'le.trans hle)) ?_
        rw [← hsupU]
        refine sup_le (hsup'' ▸ sup_le_sup_right inf_le_left C') ?_
        rw [← h0]
        rintro x ⟨w, hw, rfl⟩
        show w - p w ∈ W ⊔ C'
        have hpw : p w ∈ W ⊔ C' := by
          have : p w ∈ W ⊓ U' ⊔ C' := hsup''.symm ▸ hp w
          exact sup_le_sup_right inf_le_left C' this
        exact sub_mem (Submodule.mem_sup_left hw) hpw
  · intro j hj
    by_cases hjm : j < m
    · simp only [if_pos hjm]
      intro g x hx
      rw [hA g x (hWsle j hjm hx)]
      exact hWst j hjm g x hx
    · simp only [if_neg hjm]
      exact hWmst
  · intro t ht i hi hit
    have hle' : t.sup (fun j => if j < m then Ws j else Wm) ≤ (t.erase m).sup Ws ⊔ Wm := by
      refine Finset.sup_le fun j hj => ?_
      by_cases hjm : j < m
      · simp only [if_pos hjm]
        exact le_sup_of_le_left (Finset.le_sup (Finset.mem_erase.mpr ⟨hjm.ne, hj⟩))
      · simp only [if_neg hjm]
        exact le_sup_right
    have hT0 : t.erase m ⊆ Finset.range m := by
      intro j hj
      obtain ⟨hjm, hjt⟩ := Finset.mem_erase.mp hj
      have := Finset.mem_range.mp (ht hjt)
      exact Finset.mem_range.mpr (by omega)
    by_cases him : i < m
    · simp only [if_pos him]
      have h1 : Disjoint (Ws i) ((t.erase m).sup Ws) :=
        hind hT0 (Finset.mem_range.mpr him) (fun h => hit (Finset.mem_of_mem_erase h))
      have h2 : Disjoint (Ws i ⊔ (t.erase m).sup Ws) Wm :=
        hdisj.mono_left (sup_le (hWsle i him) (hsuple _ hT0))
      exact (h1.disjoint_sup_right_of_disjoint_sup_left h2).mono_right hle'
    · simp only [if_neg him]
      have him' : i = m := by
        have := Finset.mem_range.mp hi
        omega
      subst him'
      refine hdisj.symm.mono_right (Finset.sup_le fun j hj => ?_)
      have hjm : j < i := by
        have h1 := Finset.mem_range.mp (ht hj)
        have h2 : j ≠ i := fun h => hit (h ▸ hj)
        omega
      simp only [if_pos hjm]
      exact hWsle j hjm
  · rw [Finset.range_add_one, Finset.sup_insert, if_neg (lt_irrefl m),
      Finset.sup_congr rfl (fun j hj => if_pos (Finset.mem_range.mp hj)), hsup, sup_comm, hsupU]
  · intro j hj g v hv
    have hsame : (Finset.range j).sup (fun j => if j < m then Ws j else Wm) = (Finset.range j).sup Ws :=
      Finset.sup_congr rfl (fun i hi => if_pos (lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.lt_succ_iff.mp hj)))
    rw [hsame]
    by_cases hjm : j < m
    · simp only [if_pos hjm] at hv
      rw [hA g v (hWsle j hjm hv)]
      exact htri j hjm g v hv
    · simp only [if_neg hjm] at hv
      have hjm' : j = m := by omega
      subst hjm'
      rw [hB g v hv.2, sub_sub_cancel, hsup]
      exact hp _

private theorem partial_of_stable_finrank [FiniteDimensional k V] (ρ : Representation k Γ V) (n : ℕ) :
    ∀ U : Submodule k V, Module.finrank k U = n → Stable ρ U → Partial ρ U := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hn hU
    by_cases hb : U = ⊥
    · subst hb
      exact partial_bot ρ
    · have hbot : Stable ρ (⊥ : Submodule k V) := by
        intro g v hv
        rw [Submodule.mem_bot] at hv ⊢
        rw [hv, map_zero]
      have hne : {X : Submodule k V | Stable ρ X ∧ X < U}.Nonempty :=
        ⟨⊥, hbot, bot_lt_iff_ne_bot.mpr hb⟩
      obtain ⟨U', ⟨hU', hlt⟩, hmin⟩ := (wellFounded_gt (α := Submodule k V)).has_min _ hne
      have hmax : ∀ X, Stable ρ X → U' ≤ X → X ≤ U → X = U' ∨ X = U := by
        intro X hX h1 h2
        by_cases hXU : X = U
        · exact Or.inr hXU
        · left
          by_contra hne'
          exact hmin X ⟨hX, lt_of_le_of_ne h2 hXU⟩ (lt_of_le_of_ne h1 (Ne.symm hne'))
      exact partial_step ρ U U' hU hU' hlt.le hmax
        (ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) U' rfl hU')

theorem partial_of_stable [FiniteDimensional k V] (ρ : Representation k Γ V) (U : Submodule k V) :
    Stable ρ U → Partial ρ U := by
  intro hU
  exact partial_of_stable_finrank ρ _ U rfl hU

theorem exists_isSemisimplificationOf : ∀ {k Γ : Type} [Field k] [Group Γ] {V : Type} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k Γ V),
    ∃ s : Representation k Γ V, GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ := by
  intro k Γ _ _ V _ _ _ ρ
  obtain ⟨s, m, Ws, -, hcomp, hst, hind, hsup, htri⟩ :=
    partial_of_stable ρ ⊤ (fun _ _ _ => Submodule.mem_top)
  refine ⟨s, ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf IsSS
  refine ⟨?_, m, fun j => Ws j, LinearEquiv.refl k V, fun j => hst j j.isLt, ?_, ?_⟩
  · intro W hW
    obtain ⟨W', hW', hd, hs⟩ := hcomp W le_top hW
    exact ⟨W', hW', hd, codisjoint_iff.mpr hs⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨?_, ?_⟩
    · rw [iSupIndep_iff_supIndep_univ]
      intro t _ i _ hit
      have h := hind (t := t.map Fin.valEmbedding)
        (by
          intro x hx
          obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
          exact Finset.mem_range.mpr a.isLt)
        (Finset.mem_range.mpr i.isLt)
        (by
          intro hx
          obtain ⟨a, ha, hai⟩ := Finset.mem_map.mp hx
          exact hit (Fin.ext hai ▸ ha))
      rw [Finset.sup_map] at h
      exact h
    · refine eq_top_iff.mpr ?_
      rw [← hsup]
      exact Finset.sup_le fun i hi => le_iSup_of_le (⟨i, Finset.mem_range.mp hi⟩ : Fin m) le_rfl
  · intro j g v hv
    refine Submodule.mem_map.mpr ⟨ρ g v - s g v, ?_, rfl⟩
    have hle2 : (Finset.range j).sup Ws ≤ ⨆ j' ∈ Set.Iio j, Ws (j' : ℕ) := by
      refine Finset.sup_le fun i hi => ?_
      have hij : i < (j : ℕ) := Finset.mem_range.mp hi
      exact le_iSup₂_of_le (⟨i, hij.trans j.isLt⟩ : Fin m)
        (show (⟨i, hij.trans j.isLt⟩ : Fin m) < j from hij) le_rfl
    exact hle2 (htri j j.isLt g v hv)

end GlobalTheory.Proof.exists_semisimplification'
