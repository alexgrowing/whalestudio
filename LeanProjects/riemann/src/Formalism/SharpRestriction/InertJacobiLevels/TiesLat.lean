import Formalism.SharpRestriction.InertJacobiLevels.TieTTwValsOfMem

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem mono_from_one (w : ℕ → ℤ) (hw : ∀ i, 1 ≤ i → w i ≤ w (i + 1)) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    w a ≤ w b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact ih.trans (hw n (ha.trans hn))

theorem liftWt_antitone (t m : ℕ) (lam : Fin (m + 1) → ℤ) (w : ℕ → ℤ) (j : ℕ) (hl : Antitone lam)
    (h1 : -(lam (Fin.last m)) ≤ w 1) (hw : ∀ i, 1 ≤ i → w i ≤ w (i + 1)) : Antitone (G.liftWt t m lam w j) := by
  intro a b hab
  have hab' : a.val ≤ b.val := hab
  unfold G.liftWt
  by_cases ha : a.val < m + 1
  · by_cases hb : b.val < m + 1
    · rw [dif_pos ha, dif_pos hb]
      exact hl hab'
    · rw [dif_pos ha, dif_neg hb]
      have e1 : lam (Fin.last m) ≤ lam ⟨a.val, ha⟩ := hl (Fin.le_last _)
      have e2 := mono_from_one w hw 1 ((b.val - (m + 1)) / (t + 1) + 1) le_rfl (Nat.le_add_left _ _)
      linarith
  · have hb : ¬ b.val < m + 1 := by omega
    rw [dif_neg ha, dif_neg hb]
    have e2 := mono_from_one w hw ((a.val - (m + 1)) / (t + 1) + 1) ((b.val - (m + 1)) / (t + 1) + 1)
      (Nat.le_add_left _ _) (Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le_sub_right hab' _)) 1)
    linarith

def tCo (D : D7) (τ : D.what₂.Tau) : G.HH D := D.R.iotaInv ((D.eTau τ : D.R.GG)).2

theorem coordinate_of_first_embedding (D : D7) (τ : D.what₂.Tau) (t : G.HH D) (h : (D.eTau τ : D.R.GG) = D.R.tau1 t) :
    tCo D τ = t := by
  unfold tCo
  rw [h]
  rfl

theorem tau_top_places_iff (D : D7) (t : G.HH D) : D.R.tau1 t ∈ D.host.topPlaces ↔ t ∈ D.host.TT := by
  rw [← plGG_false, plGG_top_iff]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

structure LatHyp {D : D7} (hT : GatTies D) {L : SizeData₂ D} (X : G.Inst D L) where
  vOf : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    G.HH D → Fin (D.gat u w hg).P.nV
  inj : ∀ u w hg, Set.InjOn (vOf u w hg) (G.reps X (D.what₂.places.resChar w))
  n_eq : ∀ u w hg, ∀ t0 ∈ G.reps X (D.what₂.places.resChar w),
    (D.gat u w hg).P.n' (vOf u w hg t0) = addOrderOf (G.hP D (D.what₂.places.resChar w))
  pos : ∀ u w hg, ∀ t0 ∈ G.reps X (D.what₂.places.resChar w), ∀ s : Fin ((D.gat u w hg).P.n' (vOf u w hg t0)),
    ((D.eTau (hT.gat_pos u w hg ⟨vOf u w hg t0, s⟩) : D.R.Psi) : D.R.GG) =
      D.R.tau1 (t0 + s.val • G.hP D (D.what₂.places.resChar w))
  r_eq : ∀ u w hg, (D.gat u w hg).P.r =
    (if ((D.what₂.places.resChar w : ℕ) : ℝ) < L.sc.p0 D.R.k then G.rG L.sc else 1)
  c : ℕ
  c_le : (c : ℝ) ≤ G.cG L
  wZ : D.what₂.Tau → ℕ → ℤ
  wZ_eq : ∀ τ, ∀ j ∈ SizeData₂.lifts D, (wZ τ j : ℝ) = wj D j τ - G.kaJ D j
  wZ_mono : ∀ τ j, 1 ≤ j → wZ τ j ≤ wZ τ (j + 1)
  base_top : ∀ u w hg (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (t : D.host.TT),
    ((D.eTau (hT.gat_pos u w hg ⟨v, s⟩) : D.R.Psi) : D.R.GG) = D.R.tau1 t →
    (D.gat u w hg).P.lam0 v s 0 = L.aT t ∧ (D.gat u w hg).P.lam0 v s (Fin.last _) = -L.bT t ∧
      ∀ i : Fin ((D.gat u w hg).P.m + 1), 0 < i.val → i.val < (D.gat u w hg).P.m →
        |(D.gat u w hg).P.lam0 v s i| ≤ c
  base_off : ∀ u w hg (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)),
    ((D.eTau (hT.gat_pos u w hg ⟨v, s⟩) : D.R.Psi) : D.R.GG) ∉ D.host.topPlaces →
    ∀ i, |(D.gat u w hg).P.lam0 v s i| ≤ c
  wZ_ge : ∀ u w hg (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)),
    max (c : ℤ) (-((D.gat u w hg).P.lam0 v s (Fin.last _))) ≤ wZ (hT.gat_pos u w hg ⟨v, s⟩) 1

namespace LatHyp

variable {D : D7} {hT : GatTies D} {L : SizeData₂ D} {X : G.Inst D L} (H : LatHyp hT X)

open Classical in

def fills (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : G.Fills (D.gat u w hg) where
  TT := fun v => Finset.univ.filter
    (fun s => ((D.eTau (hT.gat_pos u w hg ⟨v, s⟩) : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces)
  a := fun v s => G.aL L (tCo D (hT.gat_pos u w hg ⟨v, s⟩))
  b := fun v s => G.bL L (tCo D (hT.gat_pos u w hg ⟨v, s⟩))
  c := H.c
  base := fun v s => by
    constructor
    · intro hs
      have hs' := (Finset.mem_filter.1 hs).2
      obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 hs'
      have h1 := H.base_top u w hg v s ⟨t, ht⟩ hte.symm
      have h2 := coordinate_of_first_embedding D _ t hte.symm
      refine ⟨?_, ?_, h1.2.2⟩
      · rw [h1.1]
        show L.aT ⟨t, ht⟩ = G.aL L (tCo D (hT.gat_pos u w hg ⟨v, s⟩))
        rw [h2]
        unfold G.aL
        rw [dif_pos ht]
      · rw [h1.2.1]
        show -L.bT ⟨t, ht⟩ = -G.bL L (tCo D (hT.gat_pos u w hg ⟨v, s⟩))
        rw [h2]
        unfold G.bL
        rw [dif_pos ht]
    · intro hs
      exact H.base_off u w hg v s (fun h => hs (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
  t := D.R.t
  mm := D.R.m
  w := fun v j s => H.wZ (hT.gat_pos u w hg ⟨v, s⟩) j
  w_ge := fun v s => H.wZ_ge u w hg v s
  w_mono := fun v s j hj => H.wZ_mono _ j hj
  domJ := fun j v s => liftWt_antitone _ _ _ _ j ((D.gat u w hg).P.dom v s)
    ((le_max_right _ _).trans (H.wZ_ge u w hg v s)) (fun i hi => H.wZ_mono _ i hi)

def latInst : G.LatInst D where
  vOf := H.vOf
  Fl := H.fills
  Lv := fun _ _ _ => { compS := fun _ => Empty, levS := fun _ c => c.elim }
  Ch := fun _ _ _ => { Kz := fun _ => 0 }
  Vram := fun _ _ _ => ⊥

theorem latTied
    (hf : ∀ j ∈ SizeData₂.lifts D, ∀ (τ : D.what₂.Tau) (z : Bool × G.HH D),
      (D.eTau τ : D.R.GG) = G.plGG D z → G.fill X (G.bL L) j z = wj D j τ) :
    G.LatTied hT X H.latInst := by
  intro u w hg
  refine ⟨rfl, rfl, H.c_le, H.r_eq u w hg, H.inj u w hg, fun v s t ht => ⟨fun hs => ?_, fun j hj => ?_⟩,
    fun t0 ht0 => ⟨H.n_eq u w hg t0 ht0, fun s => ?_⟩⟩
  · have h1 : D.R.tau2 t ∈ D.host.topPlaces := ht ▸ (Finset.mem_filter.1 hs).2
    rw [← plGG_true, plGG_top_iff] at h1
    exact Bool.noConfusion h1.1
  · show ((H.wZ (hT.gat_pos u w hg ⟨v, s⟩) j : ℤ) : ℝ) = _
    rw [H.wZ_eq _ j hj]
    unfold G.fillG
    rw [hf j hj (hT.gat_pos u w hg ⟨v, s⟩) (true, t) (by rw [ht, plGG_true])]
  have hp := H.pos u w hg t0 ht0 s
  have hmem : s ∈ (H.latInst.Fl u w hg).TT (H.latInst.vOf u w hg t0) ↔
      t0 + s.val • G.hP D (D.what₂.places.resChar w) ∈ D.host.TT := by
    rw [← tau_top_places_iff, ← hp]
    exact ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩
  refine ⟨hp, hmem, fun _ => ⟨?_, ?_⟩, fun j hj => ?_⟩
  · exact congrArg (G.aL L) (coordinate_of_first_embedding D _ _ hp)
  · exact congrArg (G.bL L) (coordinate_of_first_embedding D _ _ hp)
  · show ((H.wZ (hT.gat_pos u w hg ⟨H.vOf u w hg t0, s⟩) j : ℤ) : ℝ) = _
    rw [H.wZ_eq _ j hj]
    unfold G.fillG
    rw [hf j hj (hT.gat_pos u w hg ⟨H.vOf u w hg t0, s⟩) (false, _) (by rw [hp, plGG_false])]

end LatHyp

theorem sizeDataLat_of_subsingleton {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (Y : G.LatInst D) (K : G.Consts)
    (hs : ∀ u w hg, Subsingleton (D.gat u w hg).Fn) (hl : ∀ u w, L.lenMN u w = 0) (w : D.what₂.places.Pl) :
    G.LatticeLengthsAtPlace X Y K w := by
  refine ⟨fun _ u hg => ⟨0, ?_, by rw [hl]; simp⟩, fun u _ _ => hl u w⟩
  have := hs u w hg
  rw [Nat.cast_zero, Module.length_eq_zero_iff]
  infer_instance

theorem sizeDataLat_of_M_bot {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (Y : G.LatInst D) (K : G.Consts)
    (hM : ∀ u w hg, (D.gat u w hg).M = ⊥) (hl : ∀ u w, L.lenMN u w = 0) (w : D.what₂.places.Pl) :
    G.LatticeLengthsAtPlace X Y K w := by
  refine ⟨fun _ u hg => ⟨0, ?_, by rw [hl]; simp⟩, fun u _ _ => hl u w⟩
  have h1 : (D.gat u w hg).M ⊓ Y.Vram u w hg = ⊥ := by rw [hM, bot_inf_eq]
  have h2 : Subsingleton ↥((D.gat u w hg).M ⊓ Y.Vram u w hg) := by
    rw [h1]
    infer_instance
  rw [Nat.cast_zero, Module.length_eq_zero_iff]
  infer_instance

theorem sizeDataLat_of_Vram_bot {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (Y : G.LatInst D) (K : G.Consts)
    (hV : ∀ u w hg, Y.Vram u w hg = ⊥) (hl : ∀ u w, L.lenMN u w = 0) (w : D.what₂.places.Pl) :
    G.LatticeLengthsAtPlace X Y K w := by
  refine ⟨fun _ u hg => ⟨0, ?_, by rw [hl]; simp⟩, fun u _ _ => hl u w⟩
  have h1 : (D.gat u w hg).M ⊓ Y.Vram u w hg = ⊥ := by rw [hV, inf_bot_eq]
  have h2 : Subsingleton ↥((D.gat u w hg).M ⊓ Y.Vram u w hg) := by
    rw [h1]
    infer_instance
  rw [Nat.cast_zero, Module.length_eq_zero_iff]
  infer_instance

end Formalism.MainNotions.Inhab

end
