import Formalism.LocalToGlobal.CharacterGerms.ValuationEqSelfOfUnitGerm

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

def RawChart.TCoordSt {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
    {X : RawChart C d I κ} (Hc : ∀ g, X.CartHyp V g) : Prop :=
  ∀ (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
    ∀ (g : Fin 2) (c : I g), ∃ T : MvPowerSeries κ C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst (fun x => X.expPt g x) T = upG g (t g c)

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type}
  [∀ o g, Fintype (I o g)]

theorem cc_toAllS (o : Orb) (F : MvPowerSeries (WV (I o)) C) :
    MvPowerSeries.constantCoeff (toAllS o F) = MvPowerSeries.constantCoeff F := by
  unfold toAllS
  exact VP.cc_subst_eq (fun _ => MvPowerSeries.constantCoeff_X _) F

theorem toAllS_subst {κ : Type} [Finite κ] (o : Orb) {E : κ → MvPowerSeries (WV (I o)) C}
    (hE : ∀ x, MvPowerSeries.constantCoeff (E x) = 0) (T : MvPowerSeries κ C) :
    toAllS o (MvPowerSeries.subst E T) = MvPowerSeries.subst (fun x => toAllS o (E x)) T := by
  unfold toAllS
  exact VP.subst_subst hE (fun _ => MvPowerSeries.constantCoeff_X _) T

theorem germLift_gen {σ : Type} [Finite σ] {A : σ → MvPowerSeries (WVO I) C}
    (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0) (o : Orb) (t : ∀ g, I o g → MvPowerSeries (I o g) C)
    (ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0)
    (hT : ∀ w : WV (I o), ∃ T : MvPowerSeries σ C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst A T = toAllS o (upG w.1 (t w.1 w.2))) :
    ∀ F ∈ IntGerm V t, ∃ G : MvPowerSeries σ C, IntS V G ∧ MvPowerSeries.subst A G = toAllS o F := by
  intro F hF
  obtain ⟨γ, hγ, rfl⟩ := hF
  choose T hTi hT0 hTA using hT
  have hE : ∀ w : WV (I o), MvPowerSeries.constantCoeff (upG w.1 (t w.1 w.2)) = 0 := fun w => by
    unfold upG
    exact VP.cc_subst (fun _ => MvPowerSeries.constantCoeff_X _) (ht0 _ _)
  refine ⟨MvPowerSeries.subst T γ, IntS.subst hT0 hTi hγ, ?_⟩
  rw [VP.subst_subst hT0 hA, toAllS_subst o hE]
  congr 1
  funext w
  exact hTA w

theorem tLift_gen {σ κ : Type} [Finite σ] [Finite κ] {A : σ → MvPowerSeries (WVO I) C}
    (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0) (o : Orb) {E : κ → MvPowerSeries (WV (I o)) C}
    {π : κ → MvPowerSeries σ C} (hπi : ∀ x, IntS V (π x)) (hπ0 : ∀ x, MvPowerSeries.constantCoeff (π x) = 0)
    (hπ : ∀ x, MvPowerSeries.subst A (π x) = toAllS o (E x))
    {T : MvPowerSeries κ C} (hTi : IntS V T) (hT0 : MvPowerSeries.constantCoeff T = 0) :
    ∃ T' : MvPowerSeries σ C, IntS V T' ∧ MvPowerSeries.constantCoeff T' = 0 ∧
      MvPowerSeries.subst A T' = toAllS o (MvPowerSeries.subst E T) := by
  have hπA : ∀ x, MvPowerSeries.constantCoeff (MvPowerSeries.subst A (π x)) = 0 := fun x => VP.cc_subst hA (hπ0 x)
  have hE : ∀ x, MvPowerSeries.constantCoeff (E x) = 0 := fun x => by
    rw [← cc_toAllS o (E x), ← hπ x]
    exact hπA x
  refine ⟨MvPowerSeries.subst π T, IntS.subst hπ0 hπi hTi, VP.cc_subst hπ0 hT0, ?_⟩
  rw [VP.subst_subst hπ0 hA, toAllS_subst o hE]
  congr 1
  funext x
  exact hπ x

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb]

section Pairs

variable {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def ProjPullSt (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) : Prop :=
  PairsSep Y p → ∀ (o : Orb) (g : Fin 2), ∃ π : Fin dd → PS C 1 dd, (∀ i, IntS V (π i)) ∧
    (∀ i, MvPowerSeries.constantCoeff (π i) = 0) ∧ ∀ i, pull1 Y p (π i) = toAllS o ((Y.raw (p o)).expPt g i)

theorem germLift_of (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V)
    (hP : ProjPullSt Y p) (hT : ∀ o, RawChart.TCoordSt (H o).cartH) : GermLiftSt Y p H := by
  intro hsep o S t hS F hF
  have hA : ∀ q : Fin 1 × Fin dd, MvPowerSeries.constantCoeff (expAll Y p q.2) = 0 := fun q => VP.cc_expAll Y p q.2
  have ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0 := fun g c => (hS g).1 c
  have hTw : ∀ w : WV (I o), ∃ T : MvPowerSeries (Fin 1 × Fin dd) C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) T = toAllS o (upG w.1 (t w.1 w.2)) := by
    intro w
    obtain ⟨π, hπi, hπ0, hπ⟩ := hP hsep o w.1
    obtain ⟨T, hTi, hT0, hTe⟩ := hT o S t hS w.1 w.2
    obtain ⟨T', h1, h2, h3⟩ := VP.tLift_gen hA o hπi hπ0 hπ hTi hT0
    exact ⟨T', h1, h2, by rw [h3, hTe]⟩
  exact VP.germLift_gen hA o t ht0 hTw F hF

end Pairs

section Self

variable {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

def ProjSelfSt (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) : Prop :=
  SelfSep Y p → ∀ (o : Orb) (g : Fin 2), ∃ π : Fin 2 × Fin dd → PS C 2 dd, (∀ x, IntS V (π x)) ∧
    (∀ x, MvPowerSeries.constantCoeff (π x) = 0) ∧
    ∀ x, pull2 Y p (π x) = toAllS (I := IS I0) o ((Y.rawSelf (p o)).expPt g x)

theorem germLiftSelf_of (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
    (hP : ProjSelfSt Y p) (hT : ∀ o, RawChart.TCoordSt (H o).cartH) : GermLiftSelfSt Y p H := by
  intro hsep o S t hS F hF
  unfold pull2
  have hA : ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (VP.linPt Y (uS Y p) q) = 0 := VP.cc_linPt Y (uS Y p)
  refine VP.germLift_gen (I := IS I0) hA o t (fun g c => (hS g).1 c) (fun w => ?_) F hF
  obtain ⟨π, hπi, hπ0, hπ⟩ := hP hsep o w.1
  obtain ⟨T, hTi, hT0, hTe⟩ := hT o S t hS w.1 w.2
  obtain ⟨T', h1, h2, h3⟩ := VP.tLift_gen (I := IS I0) hA o hπi hπ0 hπ hTi hT0
  exact ⟨T', h1, h2, by rw [h3, hTe]⟩

end Self

end Formalism.L2.FormalSeriesBounds
