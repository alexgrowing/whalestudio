import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.CupCastRight

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace CrystallineSemistableComparison.AdicCoh

section Heq
variable {q : ℕ} {E : Spc}

theorem eq_cast_of_heq {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') {x : Ht q E n' i'} {y : Ht q E n i} (h : HEq x y) :
    x = y.cast h1 h2 := by
  exact eq_of_heq (h.trans (cast_heq h1 h2 y).symm)

theorem heq_zero {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') {x : Ht q E n i} (h : HEq x (0 : Ht q E n' i')) : x = 0 := by
  subst h1 h2
  exact eq_of_heq h

theorem cup_heq {n m i j n' m' i' j' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : m = m') (h4 : j = j')
    {a : Ht q E n i} {a' : Ht q E n' i'} {b : Ht q E m j} {b' : Ht q E m' j'} (ha : HEq a a') (hb : HEq b b') :
    HEq (cup q a b) (cup q a' b') := by
  subst h1 h2 h3 h4
  cases ha
  cases hb
  exact HEq.rfl

end Heq

section Root
variable (q : ℕ) [NeZero q] {E : Spc} (hR : GlobalTheory.EtC.DivisorRingCompatibility) (hinv : Inv q E) {e : ℤ} (u : Ht q E 0 e) (v : Ht q E 0 (-e))
include hR hinv

theorem cup_one_right {n i : ℤ} (b : Ht q E n i) : HEq (cup q b (one q E)) b := by
  obtain ⟨h1, -, h3⟩ := hR q E
  rw [h3 b (one q E), h1 hinv b]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact (cast_heq _ _ _).trans (cast_heq _ _ _)

theorem root_left (hvu : cup q v u = (one q E).cast (by ring) (by ring)) {n i : ℤ} (b : Ht q E n i) :
    HEq (cup q (cup q b v) u) b := by
  obtain ⟨-, h2, -⟩ := hR q E
  rw [h2 b v u, hvu, cup_cast_right]
  exact (cast_heq _ _ _).trans ((cast_heq _ _ _).trans (cup_one_right q hR hinv b))

theorem root_right (hvu : cup q v u = (one q E).cast (by ring) (by ring)) {n i : ℤ} (b : Ht q E n i) :
    HEq (cup q (cup q b u) v) b := by
  obtain ⟨-, h2, h3⟩ := hR q E
  rw [h2 b u v, h3 u v, hvu]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, cast_cast, cup_cast_right]
  exact (cast_heq _ _ _).trans (cup_one_right q hR hinv b)

end Root

section PD
variable {k : Type} [Field k] [IsAlgClosed k] {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Spec (CommRingCat.of k)) [IsProper p]
  (d : ℕ) [SmoothOfRelativeDimension d p] (q : ℕ) [NeZero q] (hq : IsUnit (q : k))
include p hq

theorem vanish (hI : ZIn) (n : ℤ) (hn : 2 * (d : ℤ) < n) : Subsingleton (Ht q (sch.obj Y) n 0) := by
  obtain ⟨tr, htr⟩ := hI.e8 q k hq p d
  haveI : Subsingleton (Ht q (sch.obj Y) (2 * d - n) (d - 0)) :=
    (hI.a9 (ZMod q) (tw q ((d : ℤ) - 0))).1 _ _ (by omega)
  obtain ⟨c, -, hc⟩ := htr n 0 0
  refine ⟨fun a b => (hc a fun y => ?_).trans (hc b fun y => ?_).symm⟩ <;>
    simp [Subsingleton.elim y 0, cast_zero]

theorem nondeg (hI : ZIn) (hprim : Nonempty (Prim q Γ(Y, ⊤))) (hinv : Inv q (sch.obj Y)) (i j : ℤ) (hij : i + j = 2 * d)
    (a : Ht q (sch.obj Y) i 0) (h : ∀ b : Ht q (sch.obj Y) j 0, cup q a b = 0) : a = 0 := by
  obtain ⟨tr, htr⟩ := hI.e8 q k hq p d
  obtain ⟨u, v, hvu⟩ := hI.root q Y hprim (d : ℤ)
  have key : ∀ b' : Ht q (sch.obj Y) (2 * d - i) (d - 0), cup q a b' = 0 := by
    intro b'
    have hc := h ((cup q b' v).cast (by omega) (by omega))
    have s1 : cup q a (cup q b' v) = 0 :=
      heq_zero (by omega) (by omega)
        ((cup_heq rfl rfl (by omega) (by omega) HEq.rfl (cast_heq _ _ _).symm).trans (heq_of_eq hc))
    have s3 : cup q (cup q a (cup q b' v)) u = 0 := by rw [s1, map_zero, AddMonoidHom.zero_apply]
    have s4 : HEq (cup q a (cup q (cup q b' v) u)) (cup q (cup q a (cup q b' v)) u) := by
      rw [(hI.ring q _).2.1 a (cup q b' v) u]
      exact (cast_heq _ _ _).symm
    exact heq_zero (by omega) (by omega)
      ((cup_heq rfl rfl (by omega) (by omega) HEq.rfl (root_left q hI.ring hinv u v hvu b').symm).trans
        (s4.trans (heq_of_eq s3)))
  obtain ⟨c, -, hc⟩ := htr i 0 0
  have ha : a = c := hc a (fun b => by simp [key b, cast_zero])
  have h0 : (0 : Ht q (sch.obj Y) i 0) = c := hc 0 (fun b => by simp [cast_zero])
  exact ha.trans h0.symm

theorem top_cyclic (hI : ZIn) (hprim : Nonempty (Prim q Γ(Y, ⊤))) (hinv : Inv q (sch.obj Y)) :
    ∃ g : Ht q (sch.obj Y) (2 * d) 0, ∀ x, ∃ n : ℤ, x = n • g := by
  obtain ⟨tr, -⟩ := hI.e8 q k hq p d
  obtain ⟨u, v, hvu⟩ := hI.root q Y hprim (d : ℤ)
  refine ⟨(cup q (tr.symm 1) v).cast (by ring) (by ring), fun x => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      ((cup q x u).cast (by ring) (by ring) : Ht q (sch.obj Y) (2 * d) d) = m • tr.symm 1 := by
    refine ⟨((tr ((cup q x u).cast (by ring) (by ring))).val : ℤ), tr.injective ?_⟩
    rw [map_zsmul, AddEquiv.apply_symm_apply, zsmul_one, Int.cast_natCast, ZMod.natCast_zmod_val]
  refine ⟨m, ?_⟩
  have hc : cup q (m • tr.symm 1) v = m • cup q (tr.symm 1) v := by
    rw [map_zsmul]
    rfl
  rw [← cast_smul]
  refine eq_cast_of_heq _ _ ?_
  refine (root_right q hI.ring hinv u v hvu x).symm.trans ?_
  rw [← hc, ← hm]
  exact cup_heq (by ring) (by ring) rfl rfl (cast_heq _ _ _).symm HEq.rfl

end PD

end CrystallineSemistableComparison.AdicCoh
