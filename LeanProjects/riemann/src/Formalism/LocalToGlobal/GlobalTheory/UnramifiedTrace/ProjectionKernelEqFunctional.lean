import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUPt0FOfVals
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.NatSmulInv
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.DiaFun
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.DualSigmaApply

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix
  Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}

theorem projection_kernel_eq_functional (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (y : ↥(Ld D u 0 (Nat.zero_le _) c))
    (hy : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c) :
    T.lv0.prk v c ⟨_, hy⟩ = (D.fm u).fv 0 v c (T.lv0.pr v c y) • (D.fm u).te 0 v c := by
  obtain ⟨z0, hz0⟩ := CrossDiaZero.dni_exists_one T v c
  obtain ⟨e, he⟩ := T.atT.res_surj v ((D.fm u).fv 0 v c (T.lv0.pr v c y))
  have hT0 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z0.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.mem_sup_left (CrossDiaZero.dnk_tld T c z0.1 z0.2)
  have hte := T.lv0.te v c z0 hz0 hT0
  have hk : (y - e • z0).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
    refine (T.lv0.fv_ker v c (y - e • z0)).1 ?_
    rw [map_sub, map_sub, T.lv0.pr_smul, map_smul, hz0, he, smul_eq_mul, mul_one, sub_self]
  have hTk : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (y - e • z0).1 ∈
      T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.smul_mem_smul (bwA_T_mem_Pv (D := D) (u := u) (A := T.atT) (v := v)) hk
  have h0 : T.lv0.prk v c ((⟨_, hy⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) - e • ⟨_, hT0⟩) = 0 := by
    refine (T.lv0.prk_ker v c _).2 ?_
    show (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y.1 - e • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z0.1) ∈ _
    rw [smul_comm e, ← smul_sub]
    exact hTk
  rw [map_sub, T.lv0.prk_smul, hte, he, sub_eq_zero] at h0
  exact h0

theorem ld_locP (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (z3 : ↥(Ld D u 0 (Nat.zero_le _) c)) (hz3 : (D.fm u).fv 0 v c (T.lv0.pr v c z3) ≠ 0) :
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔ Submodule.span (𝓞 D.host.E) {z3.1}) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, ht, htx⟩ := (rlv_mem_locP _ _ _).1 hx
    obtain ⟨e, he⟩ := T.atT.res_surj v ((D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, htx⟩) *
      ((D.fm u).fv 0 v c (T.lv0.pr v c z3))⁻¹)
    have hk : ((⟨_, htx⟩ : ↥(Ld D u 0 (Nat.zero_le _) c)) - e • z3).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      refine (T.lv0.fv_ker v c _).1 ?_
      rw [map_sub, map_sub, T.lv0.pr_smul, map_smul, he, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hz3, mul_one,
        sub_self]
    have hl := CrossDiaZero.dnk_lk_locP T v c (mem_localization_of_mem₂ _ hk)
    obtain ⟨r, hr, hrl⟩ := (rlv_mem_locP _ _ _).1 hl
    refine (rlv_mem_locP _ _ _).2 ⟨r * t, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hr ht, ?_⟩
    have e1 : (r * t) • x = r • (t • x - e • z3.1) + (r * e) • z3.1 := by
      rw [smul_sub, mul_smul, mul_smul, sub_add_cancel]
    rw [e1]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hrl)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  · exact localization_mono₂ _ (sup_le (CrossDiaZero.cls_le_ld T c)
      ((Submodule.span_singleton_le_iff_mem _ _).2 z3.2))

set_option maxHeartbeats 4000000 in

theorem ptz_val (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
    {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)}
    {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
    {η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)} {κ : T.cls0.lev.U}
    (hD : DnMvL T v c g γ η κ) (z : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) (y : (D.fm u).lk 0 v c)
    (hy : IsPtZ T v c g γ z y) : g y = (D.fm u).fv 0 v _ (T.lv0.pr v _ z) := by
  obtain ⟨s, hs, hz, hy⟩ := hy
  have hz' : γ.1.1 *ᵥ (s • z).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
    rw [Submodule.coe_smul, Matrix.mulVec_smul]; exact hz
  have h4 := hD.2.2.2.1 (s • z) hz'
  have e1 : T.lv0.prk v c ⟨_, hz'⟩ = T.lv0.prk v c ⟨_, hz⟩ := by
    congr 1
    apply Subtype.ext
    show γ.1.1 *ᵥ (s • z).1 = s • (γ.1.1 *ᵥ z.1)
    rw [Submodule.coe_smul, Matrix.mulVec_smul]
  rw [e1, hy, T.lv0.pr_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h4
  exact (mul_left_cancel₀ (res_ne T hs) h4).symm

def PtLatF (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (w1 w3 : Fin (D.R.N 0) → D.host.E) (s1 s3 : 𝓞 D.host.E)
    (hz1 : s1 • w1 ∈ Lk T.atT 0 (Nat.zero_le _) v c) (hz3 : s3 • w3 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
    s1 ∉ T.atT.Pv v → s3 ∉ T.atT.Pv v → ∀ y : (D.fm u).lk 0 v c,
    T.lv0.prk v c ⟨_, hz1⟩ = T.atT.res v s1 • y → T.lv0.prk v c ⟨_, hz3⟩ = T.atT.res v s3 • y →
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
              Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w1}) ≤
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c ⊔
        Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • w3})

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem valDia_of_lat (T : Forms0 D u) (hL : PtLatF T) : ValDia T := by
  intro v c
  refine ⟨Equiv.inv _, ?_⟩
  intro G hG a g η κ μ hP k hk δ hδ
  obtain ⟨_, γ, hD, z, γ', κ', hz1, hU, hpt⟩ := hP
  obtain ⟨u1, u2, u3, u4, u5, -⟩ := hU
  have H1 := comp_of_moves T v c g γ η κ hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 z γ' μ κ' u1 u2 u3 u4 u5
  have hga := (ptz_val T hD z _ hpt).trans hz1
  have hkb : ((k : ℤ) : (D.mem u).A.Fv v) = ((a⁻¹ : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) := hk
  have hgte : g ((D.fm u).te 0 v c) = ((k : ℤ) : (D.mem u).A.Fv v) := by
    rw [hkb, Units.val_inv_eq_inv_val]
    rw [map_smul, smul_eq_mul] at hga
    exact eq_inv_of_mul_eq_one_right hga

  have hcl := T.val0.dil v a⁻¹ k hkb c δ hδ
  obtain ⟨hh, hhH, κ0, hκK, e⟩ := (DoubleCoset.eq _ _ _ _).1 hcl
  have hκ : κ0.1 ∈ T.cls0.lev.U := hκK
  obtain ⟨γd, hγd, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have hrel : (T.cls0.y c * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v a⁻¹ c)).1 * κ0.1 := by
    rw [e]
    simp only [Subgroup.coe_mul]
    rw [← hge]
  obtain ⟨hLc, hLd⟩ := diamond_lattice_transport T v k δ hδ c ((D.fm u).dil 0 v a⁻¹ c) γd hγd ⟨κ0.1, hκ⟩ hrel
  obtain ⟨z0, hz0⟩ := CrossDiaZero.dni_exists_one T v c
  obtain ⟨ea, hea⟩ := T.atT.res_surj v (a : (D.mem u).A.Fv v)
  have hfz3 : (D.fm u).fv 0 v c (T.lv0.pr v c (ea • z0)) = (a : (D.mem u).A.Fv v) := by
    rw [T.lv0.pr_smul, map_smul, hz0, hea, smul_eq_mul, mul_one]
  have hTne : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have hw3v : ((((D.mem u).A.T : ℕ) : D.host.E))⁻¹ • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (ea • z0).1) =
      (ea • z0).1 := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E, inv_smul_smul₀ hTne]
  have H3 : IsCompMv T v c ((D.fm u).dil 0 v a⁻¹ c) ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (ea • z0).1) g
      ⟨γd, hγd⟩ δ (⟨κ0.1, hκ⟩⁻¹) := by
    refine ⟨hδ.1, ?_, congrArg _ hLc, ?_, ?_⟩
    · show bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
          (T.cls0.y ((D.fm u).dil 0 v a⁻¹ c)).1 = (T.cls0.y c).1 * δ.1 * κ0.1⁻¹
      simp only [Subgroup.coe_mul] at hrel
      rw [hrel, mul_inv_cancel_right]
    · show Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
          (Ld D u 0 (Nat.zero_le _) ((D.fm u).dil 0 v a⁻¹ c))) = _
      rw [hLd, hw3v]
      exact ld_locP T v c (ea • z0) (by rw [hfz3]; exact Units.ne_zero a)
    · intro x hx
      have hw : (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Ld D u 0 (Nat.zero_le _) c :=
        CrossDiaZero.dni_mem_of _ hLd x.2
      have hz2 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
          ((γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1) ∈
          Ld D u 0 (Nat.zero_le _) ((D.fm u).dil 0 v a⁻¹ c) := by
        rw [inv_mv]; exact x.2
      have hdf := UnramifiedDiagonal.diaFun_same T v k δ hδ c _ γd ⟨κ0.1, hκ⟩ hrel _ hw hz2
      rw [CrossDiaZero.pr_congr T v _ ⟨_, hz2⟩ x (inv_mv γd x.1)] at hdf
      rw [hdf]
      have hp := projection_kernel_eq_functional T v c ⟨_, hw⟩ hx
      show _ = g (T.lv0.prk v c ⟨_, hx⟩)
      rw [hp, map_smul, hgte, smul_eq_mul, zsmul_eq_mul, mul_comm]

  have hw3 : (1 : 𝓞 D.host.E) • ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (ea • z0).1) ∈
      Lk T.atT 0 (Nat.zero_le _) v c := by
    rw [one_smul]; exact Submodule.mem_sup_left (CrossDiaZero.dnk_tld T c _ (ea • z0).2)
  have hy3 : T.lv0.prk v c ⟨_, hw3⟩ = T.atT.res v 1 • ((a : (D.mem u).A.Fv v) • (D.fm u).te 0 v c) := by
    have hT3 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (ea • z0).1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [← one_smul (𝓞 D.host.E) ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (ea • z0).1)]; exact hw3
    have e3 : (⟨_, hw3⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = ⟨_, hT3⟩ := Subtype.ext (one_smul _ _)
    rw [e3, projection_kernel_eq_functional T v c (ea • z0) hT3, hfz3, map_one, one_smul]
  obtain ⟨s1, hs1, hw1, hy1⟩ := hpt
  have hlat := le_antisymm
    (hL v c _ _ s1 1 hw1 hw3 hs1 (one_nmem T) _ hy1 hy3)
    (hL v c _ _ 1 s1 hw3 hw1 (one_nmem T) hs1 _ hy3 hy1)
  have hm := comp_cmp T v c _ _ (γ.1.1 *ᵥ z.1) _ g g (γ * γ') ⟨γd, hγd⟩ (hcomp T η κ μ) δ (κ * κ')
    (⟨κ0.1, hκ⟩⁻¹) H1 H3 hlat (dn_fwd T hD z.1 z.2) (fun _ _ _ _ => rfl)
  exact val_of_mem T v (T.cls0.y c) δ (hcomp T η κ μ) hδ.1 H1.1 hm G hG

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
