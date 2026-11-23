import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsHomOfBasis

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.BasicNotions.Examples₂

def zeroEnt (D : D7) (Dx : DivX D) (Tw : TwForms D)
    (lam : ∀ w : D.what₂.places.Pl, (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
    (iL : ∀ w : D.what₂.places.Pl, D.what₂.LL →+* ℂ_[D.what₂.places.resChar w])
    (h1 : ∀ w x, iL w x = lamV (lam w) (D.what₂.embLL x))
    (h2 : ∀ w x, x ∈ intW D.what₂.places w ↔ ‖iL w x‖ ≤ 1)
    (h0 : ∀ u μ i, Subsingleton ((Tw.fm u μ).lat i).V) : KerEnt D Dx Tw where
  lam := lam
  iL := iL
  iL_lam := h1
  iL_int := h2
  Th := fun _ _ _ _ _ _ => 0
  VQ := fun _ _ _ _ => PUnit
  ev := fun _ _ _ _ => 0
  ev_inj := fun _ _ _ _ a b _ => Subsingleton.elim a b
  prS := fun _ _ _ _ _ => 0
  prT := fun _ _ _ _ _ => 0
  prT_val := fun _ _ _ _ _ _ _ _ _ => ⟨0, by simp⟩
  lat_S := by
    intro u μ w _ i _ φ
    have := h0 u μ i
    constructor
    · rintro ⟨x, _, rfl⟩
      have hx : x = 0 := Subsingleton.elim _ _
      subst hx
      refine ⟨by rw [map_zero]; exact Submodule.zero_mem _, fun c => ⟨PUnit.unit, by simp, by simp⟩⟩
    · rintro ⟨_, h⟩
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [map_zero]
      funext c
      obtain ⟨v, hv, _⟩ := h c
      simpa using hv
  levelFree_lattice_condition := by
    intro u μ w _ i _ φ
    have := h0 u μ (i + 1)
    constructor
    · rintro ⟨x, _, rfl⟩
      have hx : x = 0 := Subsingleton.elim _ _
      subst hx
      refine ⟨by rw [map_zero]; exact Submodule.zero_mem _, fun c => ⟨PUnit.unit, by simp, by simp⟩⟩
    · rintro ⟨_, h⟩
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [map_zero]
      funext c
      obtain ⟨v, hv, _⟩ := h c
      simpa using hv
  un := fun _ _ _ _ _ _ => 1
  un_ne := by intros; exact one_ne_zero
  kform := by intros; simp

structure EntPl (D : D7) where
  lam : ∀ w : D.what₂.places.Pl, (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]
  iL : ∀ w : D.what₂.places.Pl, D.what₂.LL →+* ℂ_[D.what₂.places.resChar w]
  iL_lam : ∀ w x, iL w x = lamV (lam w) (D.what₂.embLL x)
  iL_lam' : ∀ w x (hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ), iL w x = lam w ⟨D.what₂.embLL x, hx⟩
  iL_int : ∀ w x, x ∈ intW D.what₂.places w ↔ ‖iL w x‖ ≤ 1

theorem entPl_nonempty (D : D7) : Nonempty (EntPl D) := by
  choose lam iL h1 h2 using fun w => exists_placeEmb D w
  exact ⟨⟨lam, iL, fun w x => by
    obtain ⟨hx, e⟩ := h1 w x
    rw [lamV, dif_pos hx, e], fun w x _ => (h1 w x).choose_spec, h2⟩⟩

def entZero (D : D7) (Dx : DivX D) (Tw : TwForms D) (P : EntPl D)
    (h0 : ∀ u μ i, Subsingleton ((Tw.fm u μ).lat i).V) : KerEnt D Dx Tw :=
  zeroEnt D Dx Tw P.lam P.iL P.iL_lam P.iL_int h0

theorem entZero_lam (D : D7) (Dx Tw P h0) : (entZero D Dx Tw P h0).lam = P.lam := rfl

end Formalism.BasicNotions.Examples₂
