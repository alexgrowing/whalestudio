import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical

noncomputable section

namespace GlobalTheory.ChamberFlip

open Finset GlobalTheory.Chamber

variable {k : ℕ}

theorem below_refl (u : SV k) : Below u u := fun _ _ => rfl

theorem below_trans {a b c : SV k} (h : Below a b) (h' : Below b c) : Below a c :=
  fun i hi => (h' i (h i hi ▸ hi)).trans (h i hi)

theorem below_antisymm {a b : SV k} (h : Below a b) (h' : Below b a) : a = b := funext fun i => by
  by_cases e : a i = 0
  · by_cases e' : b i = 0
    · rw [e, e']
    · exact h' i e'
  · exact (h i e).symm

theorem zero_below (a : SV k) : Below 0 a := fun _ hi => (hi rfl).elim

theorem exists_gap {a b : SV k} (h : Below a b) (hne : a ≠ b) : ∃ i, a i = 0 ∧ b i ≠ 0 := by
  by_contra! hn
  exact hne (funext fun i => by
    by_cases e : a i = 0
    · rw [e, hn i e]
    · exact (h i e).symm)

def lowTop (S : Finset (SV k)) : SV k :=
  if h : ∃ a ∈ insert 0 S, ∀ b ∈ insert 0 S, Below b a then h.choose else 0

def upBot (S : Finset (SV k)) : SV k :=
  if h : ∃ a ∈ S, ∀ b ∈ S, Below a b then h.choose else 0

theorem lowTop_spec {S : Finset (SV k)} (hS : ∀ x ∈ S, ∀ y ∈ S, Below x y ∨ Below y x) :
    lowTop S ∈ insert 0 S ∧ ∀ b ∈ S, Below b (lowTop S) := by
  have h : ∃ a ∈ insert 0 S, ∀ b ∈ insert 0 S, Below b a :=
    exists_top (r := Below) (fun a b c h h' => below_trans h h') _ (insert_nonempty _ _) fun x hx y hy => by
      rcases mem_insert.1 hx with rfl | hx
      · exact .inl (zero_below _)
      rcases mem_insert.1 hy with rfl | hy
      · exact .inr (zero_below _)
      exact hS x hx y hy
  rw [lowTop, dif_pos h]
  exact ⟨h.choose_spec.1, fun b hb => h.choose_spec.2 b (mem_insert_of_mem hb)⟩

theorem upBot_spec {S : Finset (SV k)} (hn : S.Nonempty) (hS : ∀ x ∈ S, ∀ y ∈ S, Below x y ∨ Below y x) :
    upBot S ∈ S ∧ ∀ b ∈ S, Below (upBot S) b := by
  have h : ∃ a ∈ S, ∀ b ∈ S, Below a b :=
    exists_top (r := fun a b => Below b a) (fun a b c h h' => below_trans h' h) S hn fun x hx y hy => hS y hy x hx
  rw [upBot, dif_pos h]
  exact h.choose_spec

def lowSet (W : Finset (SV k)) (v : SV k) : Finset (SV k) := W.filter (Below · v)

def highSet (W : Finset (SV k)) (v : SV k) : Finset (SV k) := W.filter (Below v ·)

def wallFlip (W : Finset (SV k)) (v : SV k) : SV k :=
  if (highSet W v).Nonempty then fun i => if v i = 0 then upBot (highSet W v) i else lowTop (lowSet W v) i
  else fun i => if lowTop (lowSet W v) i = 0 then -v i else lowTop (lowSet W v) i

theorem isPar_insert {W : Finset (SV k)} (hW : IsPar W) {v : SV k} (h0 : v ≠ 0)
    (hc : ∀ w ∈ W, Below w v ∨ Below v w) : IsPar (insert v W) := by
  refine ⟨fun h => ?_, fun x hx y hy => ?_⟩
  · rcases mem_insert.1 h with e | e
    · exact h0 e.symm
    · exact hW.1 e
  rcases mem_insert.1 hx with e | hx'
  · rcases mem_insert.1 hy with e' | hy'
    · exact .inl (e ▸ e' ▸ below_refl _)
    · exact e ▸ (hc y hy').symm
  · rcases mem_insert.1 hy with e' | hy'
    · exact e' ▸ hc x hx'
    · exact hW.2 x hx' y hy'

theorem neg_self_sign : ∀ s : SignType, -s = s → s = 0 := by decide

theorem neg_zero_sign : ∀ s : SignType, -s = 0 → s = 0 := by decide

theorem chain_flip : ∀ {k : ℕ} (W : Finset (SV k)), IsPar W → ∃ f : SV k → SV k, ∀ u, u ∉ W → IsPar (insert u W) →
    f u ∉ W ∧ f u ≠ u ∧ IsPar (insert (f u) W) ∧ vec u + vec (f u) ∈ aP W ∧ f (f u) = u := by
  intro k W hW
  have hS : ∀ S ⊆ W, ∀ x ∈ S, ∀ y ∈ S, Below x y ∨ Below y x := fun S hS x hx y hy => hW.2 x (hS hx) y (hS hy)
  refine ⟨wallFlip W, fun u huW hu => ?_⟩
  have hc : ∀ w ∈ W, Below w u ∨ Below u w := fun w hw => hu.2 w (mem_insert_of_mem hw) u (mem_insert_self _ _)
  have hu0 : u ≠ 0 := fun e => hu.1 (e ▸ mem_insert_self _ _)
  obtain ⟨ha, haA⟩ := lowTop_spec (hS (lowSet W u) (filter_subset _ _))
  set a := lowTop (lowSet W u) with ha_def
  have hau : Below a u := by
    rcases mem_insert.1 ha with e | e
    · rw [e]; exact zero_below _
    · exact (mem_filter.1 e).2
  have haW : ∀ w ∈ W, Below w u → Below w a := fun w hw h => haA w (mem_filter.2 ⟨hw, h⟩)
  have hvA : vec a ∈ aP W := by
    rcases mem_insert.1 ha with e | e
    · rw [e, show vec (0 : SV k) = 0 by ext i; simp [vec]]; exact zero_mem _
    · exact Submodule.subset_span ⟨_, (mem_filter.1 e).1, rfl⟩
  have hane : a ≠ u := fun e => by
    rcases mem_insert.1 ha with e' | e'
    · exact hu0 (e.symm.trans e')
    · exact huW (e ▸ (mem_filter.1 e').1)
  obtain ⟨j, haj, huj⟩ := exists_gap hau hane
  by_cases hB : (highSet W u).Nonempty
  · obtain ⟨hb, hbB⟩ := upBot_spec hB (hS _ (filter_subset _ _))
    set b := upBot (highSet W u) with hb_def
    have hbW : b ∈ W := (mem_filter.1 hb).1
    have hub : Below u b := (mem_filter.1 hb).2
    have hbW' : ∀ w ∈ W, Below u w → Below b w := fun w hw h => hbB w (mem_filter.2 ⟨hw, h⟩)
    have hvi : ∀ i, wallFlip W u i = if u i = 0 then b i else a i := fun i => by rw [wallFlip, if_pos hB]
    generalize wallFlip W u = v at hvi ⊢
    have hua : ∀ i, u i = 0 → a i = 0 := fun i e => by
      by_contra h; exact h ((hau i h).symm.trans e)
    obtain ⟨i, hui, hbi⟩ := exists_gap hub (fun e => huW (e ▸ hbW))
    have hvi1 : v i = b i := by rw [hvi, if_pos hui]
    have hvj : v j = a j := by rw [hvi, if_neg huj]
    have hv0 : v ≠ 0 := fun e => hbi (by rw [← hvi1, e]; rfl)
    have hvu : v ≠ u := fun e => hbi (by rw [← hvi1, e, hui])
    have hva : v ≠ a := fun e => hbi (by rw [← hvi1, e, hua i hui])
    have hvb' : v ≠ b := fun e => huj (by rw [← hub j huj, ← e, hvj, haj])
    have hav : Below a v := fun i hi => by rw [hvi, if_neg (by rw [hau i hi]; exact hi)]
    have hvb : Below v b := fun i hi => by
      by_cases e : u i = 0
      · rw [hvi, if_pos e] at hi ⊢
      · have e2 : v i = a i := by rw [hvi, if_neg e]
        rw [e2] at hi ⊢; rw [hub i e, hau i hi]
    have hcv : ∀ w ∈ W, Below w v ∨ Below v w := fun w hw => (hc w hw).imp
      (fun h => below_trans (haW w hw h) hav) (fun h => below_trans hvb (hbW' w hw h))
    have hvW : v ∉ W := fun hv => (hc v hv).elim (fun h => hva (below_antisymm (haW v hv h) hav))
      (fun h => hvb' (below_antisymm hvb (hbW' v hv h)))
    have key : ∀ i, (u i : ℝ) + v i = a i + b i := fun i => by
      by_cases e : u i = 0
      · rw [hvi, if_pos e, e, hua i e]
      · rw [hvi, if_neg e, hub i e, add_comm]
    have hsum : vec u + vec v = vec a + vec b := by ext i; simpa [vec] using key i
    have hL : lowSet W v = lowSet W u := filter_congr fun w hw => ⟨fun h => (hc w hw).resolve_right
      (fun h' => hvW (by rw [← below_antisymm h (below_trans hvb (hbW' w hw h'))]; exact hw)),
      fun h => below_trans (haW w hw h) hav⟩
    have hH : highSet W v = highSet W u := filter_congr fun w hw => ⟨fun h => (hc w hw).resolve_left
      (fun h' => hvW (by rw [below_antisymm h (below_trans (haW w hw h') hav)]; exact hw)),
      fun h => below_trans hvb (hbW' w hw h)⟩
    refine ⟨hvW, hvu, isPar_insert hW hv0 hcv, hsum ▸ add_mem hvA (Submodule.subset_span ⟨b, hbW, rfl⟩), ?_⟩
    funext i
    rw [wallFlip, hH, hL, if_pos hB]
    show (if v i = 0 then b i else a i) = u i
    by_cases e : u i = 0
    · have ev : v i = b i := by rw [hvi, if_pos e]
      rw [ev, e]
      by_cases eb : b i = 0
      · rw [if_pos eb, eb]
      · rw [if_neg eb, hua i e]
    · have ev : v i = a i := by rw [hvi, if_neg e]
      rw [ev]
      by_cases ea : a i = 0
      · rw [if_pos ea, hub i e]
      · rw [if_neg ea]; exact (hau i ea).symm
  · have hall : ∀ w ∈ W, Below w u := fun w hw =>
      (hc w hw).resolve_right (fun h => hB ⟨w, mem_filter.2 ⟨hw, h⟩⟩)
    have hvi : ∀ i, wallFlip W u i = if a i = 0 then -u i else a i := fun i => by rw [wallFlip, if_neg hB]
    generalize wallFlip W u = v at hvi ⊢
    have hav : Below a v := fun i hi => by rw [hvi, if_neg hi]
    have hvj : v j = -u j := by rw [hvi, if_pos haj]
    have hv0 : v ≠ 0 := fun e => huj (neg_zero_sign _ (hvj.symm.trans (congrFun e j)))
    have hvu : v ≠ u := fun e => huj (neg_self_sign _ (hvj.symm.trans (congrFun e j)))
    have hva : v ≠ a := fun e => huj (neg_zero_sign _ (hvj.symm.trans ((congrFun e j).trans haj)))
    have hwv : ∀ w ∈ W, Below w v := fun w hw => below_trans (haW w hw (hall w hw)) hav
    have hvW : v ∉ W := fun hv => hva (below_antisymm (haW v hv (hall v hv)) hav)
    have key : ∀ i, (u i : ℝ) + v i = 2 * a i := fun i => by
      by_cases ea : a i = 0
      · rw [hvi, if_pos ea, ea]; simp
      · rw [hvi, if_neg ea, ← hau i ea]; ring
    have hsum : vec u + vec v = (2 : ℝ) • vec a := by ext i; simpa [vec] using key i
    have hL : lowSet W v = lowSet W u := filter_congr fun w hw => iff_of_true (hwv w hw) (hall w hw)
    have hH : highSet W v = highSet W u := filter_congr fun w hw => iff_of_false
      (fun h => hvW (by rw [below_antisymm h (hwv w hw)]; exact hw)) (fun h => hB ⟨w, mem_filter.2 ⟨hw, h⟩⟩)
    have hB' : ¬ (highSet W v).Nonempty := hH ▸ hB
    refine ⟨hvW, hvu, isPar_insert hW hv0 fun w hw => .inl (hwv w hw), hsum ▸ Submodule.smul_mem _ _ hvA, ?_⟩
    funext i
    rw [wallFlip, if_neg hB', hL]
    show (if a i = 0 then -v i else a i) = u i
    by_cases ea : a i = 0
    · rw [if_pos ea, hvi, if_pos ea, neg_neg]
    · rw [if_neg ea]; exact (hau i ea).symm

end GlobalTheory.ChamberFlip
