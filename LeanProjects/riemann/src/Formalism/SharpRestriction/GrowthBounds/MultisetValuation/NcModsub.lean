import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GrowthExclusionSumEq

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem nc_modsub (a b e' n : ℕ) (ha : a < n) (hb : b < n) (he : e' < n) (h : (a + e') % n = b) :
    (b + n - a) % n = e' := by
  rcases Nat.lt_or_ge (a + e') n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    subst h
    have : a + e' + n - a = e' + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt he]
  · have h2 : (a + e') % n = a + e' - n := by
      rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
    rw [h2] at h
    subst h
    have : a + e' - n + n - a = e' := by omega
    rw [this, Nat.mod_eq_of_lt he]

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

include hL ht0 in
theorem nc_shift (s s' : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) (e : ℕ) :
    nc_iota Y u w hg t0 s + e • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) = nc_iota Y u w hg t0 s' ↔
      (s.val + e) % (D.gat u w hg).P.n' (Y.vOf u w hg t0) = s'.val := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  have key : ∀ (a b : ℕ), b < addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) →
      (t0 + a • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) + e • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) =
        t0 + b • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ↔
      (a + e) % addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) = b) := by
    intro a b hb
    have hpos : 0 < addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := by omega
    rw [add_assoc, ← add_nsmul, show (a + e) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) =
      ((a + e) % addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) by
        rw [mod_addOrderOf_nsmul]]
    constructor
    · intro h
      exact nsmul_injOn_Iio_addOrderOf (show (a + e) % _ ∈ Set.Iio _ from Nat.mod_lt _ hpos)
        (show b ∈ Set.Iio _ from hb) (add_left_cancel h)
    · intro h; rw [h]
  have := key s.val s'.val (by rw [← hn]; exact s'.isLt)
  rw [← hn] at this
  exact this

include hL ht0 in
theorem nc_excl (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) (e : ℕ)
    (he : 2 * e + 1 ∈ dSet ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) s) :
    Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) (2 * e + 1) := by
  have hloc := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  unfold dSet at he
  obtain ⟨s', hs', hd⟩ := Finset.mem_image.1 he
  rw [Finset.mem_filter] at hs'
  have hpos : 0 < (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by have := s.isLt; omega
  have hlt : 2 * e + 1 < (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by rw [← hd]; exact Nat.mod_lt _ hpos
  have hne : s' ≠ s := fun h => hs'.2 (by rw [h])
  refine ⟨⟨e, rfl⟩, nc_iota Y u w hg t0 s', ((hloc s').2.1).1 hs'.1, fun h => hne (hinj h), ?_⟩
  refine ⟨by omega, ?_, ?_⟩
  · rw [nc_partner hg]
    congr 1
    show nc_iota Y u w hg t0 s + (2 * e + 1) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) = nc_iota Y u w hg t0 s'
    refine (nc_shift X Y hT hL u w hg t0 ht0 s s' (2 * e + 1)).2 ?_
    rw [← hd]
    have := s.isLt
    have := s'.isLt
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have : s.val + (s'.val + (D.gat u w hg).P.n' (Y.vOf u w hg t0) - s.val) =
        s'.val + (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt s'.isLt]
  · intro e' he0 he1 hp
    rw [nc_partner hg] at hp
    have hp' : nc_iota Y u w hg t0 s + e' • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) = nc_iota Y u w hg t0 s' :=
      (Prod.mk.inj hp).2
    have h1 := (nc_shift X Y hT hL u w hg t0 ht0 s s' e').1 hp'
    have h2 := nc_modsub s.val s'.val e' _ s.isLt s'.isLt (by omega) h1
    rw [hd] at h2
    omega

end Orbit

end Formalism.MainNotions.FormalGroupSystem.Pf
