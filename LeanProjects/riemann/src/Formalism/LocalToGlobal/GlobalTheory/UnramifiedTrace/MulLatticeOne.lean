import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUAllOfSameTe

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix
  Formalism.UG
open scoped TensorProduct Classical

theorem mul_lattice_one {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) :
    mulLat (1 : Matrix (Fin n) (Fin n) E) L = L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [Matrix.one_mulVec] using hy
  · intro hx
    exact ⟨x, hx, by simp [Matrix.one_mulVec]⟩

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 4000000 in

theorem pt_agree1 (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (w1 : Fin (D.R.N 0) → D.host.E) (s1 : 𝓞 D.host.E)
    (hz1 : s1 • w1 ∈ Lk T.atT 0 (Nat.zero_le _) v c) (hs1 : s1 ∉ T.atT.Pv v) (y : (D.fm u).lk 0 v c)
    (hy1 : T.lv0.prk v c ⟨_, hz1⟩ = T.atT.res v s1 • y)
    (g1 g3 : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (h1 : g1 y = 1) (h3 : g3 y = 1) :
    ∀ l ∈ clsCrd D u 0 (Nat.zero_le _) c, ∀ (e : 𝓞 D.host.E)
      (hY : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • l + e • w1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      g1 (T.lv0.prk v c ⟨_, hY⟩) = g3 (T.lv0.prk v c ⟨_, hY⟩) := by
  intro l hl e hY
  have hl' : s1 • l ∈ Lk T.atT 0 (Nat.zero_le _) v c := Submodule.mem_sup_left (Submodule.smul_mem _ _ hl)
  have hTl : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (s1 • l) ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.smul_mem _ _ hl'
  have hTl0 : T.lv0.prk v c ⟨_, hTl⟩ = 0 :=
    (T.lv0.prk_ker v c _).2 (Submodule.smul_mem_smul (bwA_T_mem_Pv (D := D) (u := u) (A := T.atT) (v := v)) hl')
  have e0 : s1 • (⟨_, hY⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) =
      (⟨_, hTl⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) + e • (⟨_, hz1⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) := by
    apply Subtype.ext
    show s1 • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • l + e • w1) =
      (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (s1 • l) + e • (s1 • w1)
    rw [smul_add, smul_comm s1 (((D.mem u).A.T : ℕ) : 𝓞 D.host.E), smul_comm s1 e]
  have hp : T.lv0.prk v c ⟨_, hY⟩ = T.atT.res v e • y := by
    have h := congrArg (T.lv0.prk v c) e0
    rw [T.lv0.prk_smul, map_add, T.lv0.prk_smul, hTl0, zero_add, hy1, smul_comm] at h
    exact smul_right_injective _ (res_ne T hs1) h
  rw [hp, map_smul, map_smul, h1, h3]

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem valSame_pt (T : Forms0 D u) : ValSame T := by
  intro v c G hG g η κ μ g' η' κ' μ' y hP hP'
  obtain ⟨_, γ, hD, z, γ1, κ1, hz1, hU, hpt⟩ := hP
  obtain ⟨_, γ', hD', z', γ1', κ1', hz1', hU', hpt'⟩ := hP'
  obtain ⟨u1, u2, u3, u4, u5, -⟩ := hU
  obtain ⟨u1', u2', u3', u4', u5', -⟩ := hU'
  have H1 := comp_of_moves T v c g γ η κ hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 z γ1 μ κ1 u1 u2 u3 u4 u5
  have H3 := comp_of_moves T v c g' γ' η' κ' hD'.1 hD'.2.1 hD'.2.2.1 hD'.2.2.2.1 z' γ1' μ' κ1' u1' u2' u3' u4' u5'
  have hg1 := (ptz_val T hD z _ hpt).trans hz1
  have hg3 := (ptz_val T hD' z' _ hpt').trans hz1'
  obtain ⟨s1, hs1, hw1, hy1⟩ := hpt
  obtain ⟨s3, hs3, hw3, hy3⟩ := hpt'
  have hlat := le_antisymm (ptLat_holds T v c _ _ s1 s3 hw1 hw3 hs1 hs3 y hy1 hy3)
    (ptLat_holds T v c _ _ s3 s1 hw3 hw1 hs3 hs1 y hy3 hy1)
  have hm := comp_cmp T v c _ _ _ _ g g' _ _ (hcomp T η κ μ) (hcomp T η' κ' μ') _ _ H1 H3 hlat
    (dn_fwd T hD z.1 z.2) (pt_agree1 T v c _ s1 hw1 hs1 y hy1 g g' hg1 hg3)
  exact val_of_mem T v (T.cls0.y c) (hcomp T η' κ' μ') (hcomp T η κ μ) H3.1 H1.1 hm G hG

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem valTe_pt (T : Forms0 D u) : ValTe T := by
  intro v c G hG g η κ μ hP
  obtain ⟨_, γ, hD, z, γ1, κ1, hz1, hU, hpt⟩ := hP
  obtain ⟨u1, u2, u3, u4, u5, -⟩ := hU
  have H1 := comp_of_moves T v c g γ η κ hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 z γ1 μ κ1 u1 u2 u3 u4 u5
  have hg1 := (ptz_val T hD z _ hpt).trans hz1
  obtain ⟨z0, hz0⟩ := CrossDiaZero.dni_exists_one T v c
  have hTne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have hT0 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z0.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.mem_sup_left (CrossDiaZero.dnk_tld T c z0.1 z0.2)
  have e1 : ((1 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).1.1 :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = 1 := by simp
  have hw3v : ((((D.mem u).A.T : ℕ) : D.host.E))⁻¹ • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z0.1) = z0.1 := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E, inv_smul_smul₀ hTne]
  have H3 : IsCompMv T v c c ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z0.1) g 1 1 1 := by
    refine ⟨fun v' _ => by simp, by simp, ?_, ?_, ?_⟩
    · rw [e1, mul_lattice_one]
    · rw [e1, mul_lattice_one, hw3v]
      exact ld_locP T v c z0 (by rw [hz0]; exact one_ne_zero)
    · intro x hx
      have hx' : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
        Submodule.mem_sup_left (CrossDiaZero.dnk_tld T c x.1 x.2)
      have e2 : (⟨_, hx⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = ⟨_, hx'⟩ := by
        apply Subtype.ext
        show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) •
            ((1 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).1.1 *ᵥ x.1) =
          (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • x.1
        rw [e1, Matrix.one_mulVec]
      rw [e2, projection_kernel_eq_functional T v c x hx', map_smul, hg1, smul_eq_mul, mul_one]
  have hw3 : (1 : 𝓞 D.host.E) • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z0.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
    rw [one_smul]; exact hT0
  have hy3 : T.lv0.prk v c ⟨_, hw3⟩ = T.atT.res v 1 • (D.fm u).te 0 v c := by
    have e3 : (⟨_, hw3⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = ⟨_, hT0⟩ := Subtype.ext (one_smul _ _)
    rw [e3, T.lv0.te v c z0 hz0 hT0, map_one, one_smul]
  obtain ⟨s1, hs1, hw1, hy1⟩ := hpt
  have hlat := le_antisymm
    (ptLat_holds T v c _ _ s1 1 hw1 hw3 hs1 (one_nmem T) _ hy1 hy3)
    (ptLat_holds T v c _ _ 1 s1 hw3 hw1 (one_nmem T) hs1 _ hy3 hy1)
  have hm := comp_cmp T v c _ _ (γ.1.1 *ᵥ z.1) _ g g (γ * γ1) 1 (hcomp T η κ μ) 1 (κ * κ1) 1 H1 H3 hlat
    (dn_fwd T hD z.1 z.2) (fun _ _ _ _ => rfl)
  have h := val_of_mem T v (T.cls0.y c) 1 (hcomp T η κ μ) H3.1 H1.1 hm G hG
  rw [mul_one] at h
  exact h

theorem dUAll_holds : Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.DUAll :=
  dUAll_of_same_te fun _ _ T => ⟨valSame_pt T, valTe_pt T⟩

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
