import Formalism.SharpRestriction.Divisibility.OrbitPlaces

noncomputable section

open scoped BigOperators
open Classical
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

namespace PI.OrbBoundFW

variable {D : D7} {L : SizeData₂ D}

def wOrb (D : D7) (p i : ℕ) (z : Pl D) (s : ZMod (nP D p)) : ℝ := wPl D (i + 1) (orbMap D p z s)

def eOrb (E : Ent D) (p : ℕ) (u : D.what₂.Word) (i : ℕ) (z : Pl D) (s : ZMod (nP D p)) : ℝ :=
  if IsTopPl D (orbMap D p z s) then
    E.size u i (orbMap D p z s) - E.row u i (orbMap D p z s) 0 -
      (((D.R.k : ℝ) - 1) * wOrb D p i z s - 2 * wOrb D p i z s)
  else E.size u i (orbMap D p z s) - ((D.R.k : ℝ) - 1) * wOrb D p i z s

theorem three_le_k (D : D7) : 3 ≤ D.R.k := by
  have h := D.R.m_add_three_le_k
  omega

theorem setting_sq {X : Inst D L} {E : Ent D} (hS : Shape D L X E) {p : ℕ} [Fact p.Prime] (h : OrbOK D p)
    (hp : (p : ℝ) ≤ L.sc.X'' D.R.n) (u : D.what₂.Word) {i : ℕ} (hi : i < D.R.m) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p]) :
    (orbLoc E p h u i z Th).HidaSetting (L.sc.a ^ 2) := by
  have hxa := hS.xa
  have ha1 : 1 < L.sc.a := hxa.2
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.five
  refine ⟨?_, ?_, ?_⟩
  · show (p : ℝ) ≤ L.sc.a ^ 2
    nlinarith [hxa.1]
  · intro s
    exact hS.sizeA u i hi _
  · show 2 * Real.logb p (L.sc.a ^ 2) + 2 ≤ ((D.R.N i : ℕ) : ℝ) - 1
    have hk := hS.rankA
    have hx : 1 ≤ L.sc.a ^ 2 := by nlinarith
    have hlog : Real.logb p (L.sc.a ^ 2) ≤ Real.logb 5 (L.sc.a ^ 2) := by
      unfold Real.logb
      have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
      have hlp : Real.log 5 ≤ Real.log p := Real.log_le_log (by norm_num) hp5
      have hx0 : 0 ≤ Real.log (L.sc.a ^ 2) := Real.log_nonneg hx
      rw [div_le_div_iff₀ (by linarith) hl5]
      nlinarith
    have hN : (D.R.k : ℝ) ≤ (D.R.N i : ℝ) := by
      have : D.R.k ≤ D.R.N i := by
        unfold Formalism.BasicNotions.Ranks.N
        exact Nat.le_add_right _ _
      exact_mod_cast this
    linarith

theorem wOrb_pos {X : Inst D L} {E : Ent D} (hS : Shape D L X E) (p : ℕ) {i : ℕ} (hi : i < D.R.m) (z : Pl D)
    (s : ZMod (nP D p)) : 0 < wOrb D p i z s := by
  unfold wOrb
  exact hS.wpos i hi _

theorem eOrb_bounds {X : Inst D L} {E : Ent D} (hS : Shape D L X E) (p : ℕ) (u : D.what₂.Word) {i : ℕ}
    (hi : i < D.R.m) (z : Pl D) (s : ZMod (nP D p)) :
    0 ≤ eOrb E p u i z s ∧ eOrb E p u i z s ≤ 4 * wOrb D p i z s := by
  unfold eOrb wOrb
  split_ifs with ht
  · exact hS.top u i hi _ ht
  · exact hS.low u i hi _ ht

theorem dl_off {E : Ent D} {p : ℕ} [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p])
    (s : ZMod (nP D p)) (hs : s ∉ (orbLoc E p h u i z Th).TT) :
    ((orbLoc E p h u i z Th).Dl s : ℝ) = ((D.R.k : ℝ) - 1) * wOrb D p i z s + eOrb E p u i z s := by
  have ht : ¬ IsTopPl D (orbMap D p z s) := fun ht => hs (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩)
  have hsz : ((orbLoc E p h u i z Th).Dl s : ℝ) = E.size u i (orbMap D p z s) := by
    have h1 : (orbLoc E p h u i z Th).Dl s = (E.nu u i (orbMap D p z s)).cells.card := by
      unfold Formalism.MainNotions.product_zeroth_first_parts.Loc.Dl
      split_ifs with hh
      · exact absurd hh hs
      · rfl
    rw [h1]
    rfl
  rw [hsz]
  unfold eOrb
  rw [if_neg ht]
  ring

theorem dl_on {E : Ent D} {p : ℕ} [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p])
    (s : ZMod (nP D p)) (hs : s ∈ (orbLoc E p h u i z Th).TT) :
    ((orbLoc E p h u i z Th).Dl s : ℝ) =
      ((D.R.k : ℝ) - 1) * wOrb D p i z s - 2 * wOrb D p i z s + eOrb E p u i z s := by
  have ht : IsTopPl D (orbMap D p z s) := (Finset.mem_filter.1 hs).2
  have hA : (E.nu u i (orbMap D p z s)).rowLen 0 ≤ (E.nu u i (orbMap D p z s)).cells.card := by
    calc (E.nu u i (orbMap D p z s)).rowLen 0
        = ((Finset.range ((E.nu u i (orbMap D p z s)).rowLen 0)).map
            ⟨fun j => ((0 : ℕ), j), fun a b hab => by simpa using hab⟩).card := by simp
      _ ≤ (E.nu u i (orbMap D p z s)).cells.card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          exact YoungDiagram.mem_iff_lt_rowLen.2 hj
  have hsz : ((orbLoc E p h u i z Th).Dl s : ℝ) =
      E.size u i (orbMap D p z s) - E.row u i (orbMap D p z s) 0 := by
    have h1 : (orbLoc E p h u i z Th).Dl s =
        (E.nu u i (orbMap D p z s)).cells.card - (E.nu u i (orbMap D p z s)).rowLen 0 := by
      unfold Formalism.MainNotions.product_zeroth_first_parts.Loc.Dl
      split_ifs with hh
      · rfl
      · exact absurd hs hh
    rw [h1, Nat.cast_sub hA]
    rfl
  rw [hsz]
  unfold eOrb
  rw [if_pos ht]
  ring

end PI.OrbBoundFW
