import Formalism.LocalToGlobal.CharacterGerms.RowTieValL

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def IsIU (V : VF C) {σ : Type} (U : MvPowerSeries σ C) : Prop :=
  IntS V U ∧ V.v (MvPowerSeries.constantCoeff U) = 0

theorem IsIU.one {σ : Type} : IsIU V (1 : MvPowerSeries σ C) := by
  refine ⟨fun μ => ?_, ?_⟩
  · unfold VF.Ge
    rw [MvPowerSeries.coeff_one]
    split_ifs
    · rw [AddValuation.map_one]; exact le_rfl
    · rw [AddValuation.map_zero]; exact le_top
  · rw [map_one, AddValuation.map_one]

theorem IsIU.mul {σ : Type} {U U' : MvPowerSeries σ C} (h : IsIU V U) (h' : IsIU V U') : IsIU V (U * U') :=
  ⟨IntS.mul h.1 h'.1, by rw [map_mul, AddValuation.map_mul, h.2, h'.2, add_zero]⟩

theorem IsIU.prod {σ ι : Type} (s : Finset ι) {U : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IsIU V (U i)) :
    IsIU V (∏ i ∈ s, U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact IsIU.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

structure IsProj (π : Orb → Fin 2 → Fin dd → PS C 1 dd) : Prop where
  int : ∀ o g i, IntS V (π o g i)
  cc : ∀ o g i, MvPowerSeries.constantCoeff (π o g i) = 0
  pull : ∀ o g i, pull1 Y p (π o g i) = toAllS o ((Y.raw (p o)).expPt g i)

def Aterm (π : Orb → Fin 2 → Fin dd → PS C 1 dd) (s s' : Orb × Fin 2) : PS C 1 dd :=
  FB.expS C ((Y.k : C) • ev (n := 1) ![π s.1 s.2, comp1 (Y.B.actK C Y.w0) (π s'.1 s'.2)] Y.h)

def barS (s : Orb × Fin 2) : Orb × Fin 2 := (s.1, 1 - s.2)

def BiaddSt : Prop :=
  PairsSep Y p → ∀ π, IsProj Y p π → ∃ U : PS C 1 dd, IsIU V U ∧
    pull1 Y p (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) =
      pull1 Y p U * ∏ s : Orb × Fin 2, ∏ s' : Orb × Fin 2, pull1 Y p (Aterm Y π s s')

def CrossSt : Prop :=
  PairsSep Y p → ∀ π, IsProj Y p π → ∀ s s' : Orb × Fin 2, s' ≠ barS s →
    ∃ U : PS C 1 dd, IsIU V U ∧ pull1 Y p (Aterm Y π s s') = pull1 Y p U

def PairSt : Prop :=
  PairsSep Y p → ∀ π, IsProj Y p π → ∀ o : Orb, ∃ U : PS C 1 dd, IsIU V U ∧
    pull1 Y p (Aterm Y π (o, 0) (o, 1)) * pull1 Y p (Aterm Y π (o, 1) (o, 0)) =
      pull1 Y p U * toAllS o (mvExp (Y.raw (p o)).hRow)

end Defs

theorem unit_of (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (hP : ProjPullSt Y p) (h1 : BiaddSt Y p)
    (h2 : CrossSt Y p) (h3 : PairSt Y p) : UnitSt Y p := by
  intro hs
  choose π hπi hπc hπp using hP hs
  have hproj : IsProj Y p π := ⟨hπi, hπc, hπp⟩
  obtain ⟨U0, hU0, hE⟩ := h1 hs π hproj
  choose Uc hUc hUceq using h2 hs π hproj
  choose Up hUp hUpeq using h3 hs π hproj

  let W : Orb × Fin 2 → Orb × Fin 2 → PS C 1 dd := fun s s' =>
    if h : s' ≠ barS s then Uc s s' h else 1
  have hW : ∀ s s', IsIU V (W s s') := by
    intro s s'
    by_cases h : s' ≠ barS s
    · simp only [W, dif_pos h]; exact hUc s s' h
    · simp only [W, dif_neg h]; exact IsIU.one
  have hone : pull1 Y p (1 : PS C 1 dd) = 1 := by
    have := VP.pullback_one_var_prod (Y := Y) (p := p) (∅ : Finset Unit) (fun _ => 1)
    simpa using this
  have hA : ∀ s s', pull1 Y p (Aterm Y π s s') =
      pull1 Y p (W s s') * (if s' = barS s then pull1 Y p (Aterm Y π s (barS s)) else 1) := by
    intro s s'
    by_cases h : s' = barS s
    · have h' : ¬ s' ≠ barS s := not_not.2 h
      simp only [W, dif_neg h', if_pos h, hone, one_mul]
      rw [h]
    · simp only [W, dif_pos h, if_neg h, mul_one]
      exact hUceq s s' h
  have hpair : ∏ s : Orb × Fin 2, pull1 Y p (Aterm Y π s (barS s)) =
      ∏ o, (pull1 Y p (Up o) * toAllS o (mvExp (Y.raw (p o)).hRow)) := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun o _ => ?_
    rw [Fin.prod_univ_two]
    have hb0 : barS (o, (0 : Fin 2)) = (o, 1) := by simp [barS]
    have hb1 : barS (o, (1 : Fin 2)) = (o, 0) := by simp [barS]
    rw [hb0, hb1]
    exact hUpeq o
  refine ⟨U0 * (∏ s, ∏ s', W s s') * ∏ o, Up o,
    ((hU0.mul (IsIU.prod _ fun s _ => IsIU.prod _ fun s' _ => hW s s')).mul
      (IsIU.prod _ fun o _ => hUp o)).1,
    ((hU0.mul (IsIU.prod _ fun s _ => IsIU.prod _ fun s' _ => hW s s')).mul
      (IsIU.prod _ fun o _ => hUp o)).2, ?_⟩
  rw [hE]
  rw [Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun s' _ => hA s s']
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  rw [hpair, Finset.prod_mul_distrib, VP.pullback_one_var_mul, VP.pullback_one_var_mul, VP.pullback_one_var_prod, VP.pullback_one_var_prod]
  simp_rw [VP.pullback_one_var_prod]
  ring

theorem valuation_eq_pair_of_pairing (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V)
    (Ls : LetSys C dd) (n : ℕ) (hP : ProjPullSt Y p) (hT : ∀ o, RawChart.TCoordSt (H o).cartH)
    (h1 : BiaddSt Y p) (h2 : CrossSt Y p) (h3 : PairSt Y p) : ValEqPSt Y p H Ls n :=
  valuation_eq_pair_of_unit_germ Y p H Ls n (unit_of Y p hP h1 h2 h3) (germLift_of Y p H hP hT)

end Formalism.L2.FormalSeriesBounds
