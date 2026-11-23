import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DUAllOfParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.DnkLkLocP

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

section Gen

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem lp_smul_map (P : Ideal (𝓞 E)) [P.IsPrime] (A : Matrix (Fin n) (Fin n) E)
    (M N : Submodule (𝓞 E) (Fin n → E)) (h : ∀ m ∈ M, A *ᵥ m ∈ Formalism.HermitianLatticesTheory.localization₂ P N)
    (x : Fin n → E) (hx : x ∈ P • M) : A *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ P (P • N) := by
  refine Submodule.smul_induction_on (p := fun x => A *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ P (P • N)) hx
    (fun p hp m hm => ?_) (fun x y hx hy => ?_)
  · obtain ⟨s, hs, hsm⟩ := h m hm
    refine ⟨s, hs, ?_⟩
    show s • (A *ᵥ (p • m)) ∈ P • N
    rw [Matrix.mulVec_smul, smul_comm]
    exact Submodule.smul_mem_smul hp hsm
  · show A *ᵥ (x + y) ∈ Formalism.HermitianLatticesTheory.localization₂ P (P • N)
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hx hy

theorem inv_mv (g : GL (Fin n) E) (z : Fin n → E) :
    ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((g : Matrix (Fin n) (Fin n) E) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

end Gen

variable {D : D7} {u : D.what₂.Word}

theorem res_ne (T : Forms0 D u) {v : (D.mem u).A.vT} {s : 𝓞 D.host.E} (hs : s ∉ T.atT.Pv v) :
    T.atT.res v s ≠ 0 := fun h => hs ((RingHom.mem_ker).2 h)

section Mv

variable (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
  {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)}
  {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
  {η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)} {κ : T.cls0.lev.U}

theorem dn_fwd (hD : DnMvL T v c g γ η κ) (m : Fin (D.R.N 0) → D.host.E)
    (hm : m ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)) :
    γ.1.1 *ᵥ m ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
  have h1 : γ.1.1 *ᵥ m ∈ mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)) := by
    rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.mem_mul_lattice_iff γ.1, inv_mv]
    exact hm
  have h2 : γ.1.1 *ᵥ m ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) :=
    ⟨1, (T.atT.Pv v).primeCompl.one_mem, by simpa using h1⟩
  rw [hD.2.2.1] at h2
  exact h2

theorem dn_bwd (hD : DnMvL T v c g γ η κ) (m : Fin (D.R.N 0) → D.host.E)
    (hm : m ∈ Lk T.atT 0 (Nat.zero_le _) v c) :
    ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ m ∈
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g)) := by
  have h1 : m ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) :=
    CrossDiaZero.dnk_lk_locP T v c (mem_localization_of_mem₂ _ hm)
  rw [← hD.2.2.1] at h1
  obtain ⟨t, ht, htm⟩ := (rlv_mem_locP _ _ _).1 h1
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 htm
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hxe
  refine (rlv_mem_locP _ _ _).2 ⟨t, ht, ?_⟩
  rw [← Matrix.mulVec_smul, ← hxe, inv_mv]
  exact hx

end Mv

theorem ptz_sub (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
    {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)}
    {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
    (z z' : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) {y y' : (D.fm u).lk 0 v c}
    (s s' : 𝓞 D.host.E) (hz : s • (γ.1.1 *ᵥ z.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c)
    (hz' : s' • (γ.1.1 *ᵥ z'.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c)
    (hy : T.lv0.prk v c ⟨_, hz⟩ = T.atT.res v s • y) (hy' : T.lv0.prk v c ⟨_, hz'⟩ = T.atT.res v s' • y') :
    ∃ w : ↥(Lk T.atT 0 (Nat.zero_le _) v c), w.1 = (s * s') • (γ.1.1 *ᵥ (z.1 - z'.1)) ∧
      T.lv0.prk v c w = (T.atT.res v s * T.atT.res v s') • (y - y') := by
  refine ⟨s' • ⟨_, hz⟩ - s • ⟨_, hz'⟩, ?_, ?_⟩
  · show s' • (s • (γ.1.1 *ᵥ z.1)) - s • (s' • (γ.1.1 *ᵥ z'.1)) = _
    rw [Matrix.mulVec_sub, smul_sub, smul_smul, smul_smul, mul_comm s' s]
  · rw [map_sub, T.lv0.prk_smul, T.lv0.prk_smul, hy, hy', smul_smul, smul_smul, smul_sub,
      mul_comm (T.atT.res v s') _]

theorem ptEx_holds (T : Forms0 D u) : PtEx T := by
  intro v c g _ γ η κ hD z
  obtain ⟨s, hs, hsz⟩ := (rlv_mem_locP _ _ _).1 (dn_fwd T hD z.1 z.2)
  have hz : s • (γ.1.1 *ᵥ z.1) ∈ Lk T.atT 0 (Nat.zero_le _) v c := Submodule.mem_sup_left hsz
  refine ⟨(T.atT.res v s)⁻¹ • T.lv0.prk v c ⟨_, hz⟩, s, hs, hz, ?_⟩
  rw [smul_smul, mul_inv_cancel₀ (res_ne T hs), one_smul]

theorem ptWd_holds (T : Forms0 D u) : PtWd T := by
  rintro v c g _ γ η κ hD x y y' ⟨z, hzx, s, hs, hz, hy⟩ ⟨z', hzx', s', hs', hz', hy'⟩
  obtain ⟨w, hw, hpw⟩ := ptz_sub T z z' s s' hz hz' hy hy'
  have hd : (z - z').1 ∈ T.atT.Pv v • Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) :=
    (T.lv0.pr_ker v _ (z - z')).1 (by rw [map_sub, hzx, hzx', sub_self])
  obtain ⟨t, ht, htd⟩ := (rlv_mem_locP _ _ _).1 (lp_smul_map _ γ.1.1 _ _ (dn_fwd T hD) _ hd)
  have h0 : T.lv0.prk v c (t • w) = 0 := by
    refine (T.lv0.prk_ker v c _).2 ?_
    show t • w.1 ∈ _
    rw [hw, smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.smul_mono le_rfl le_sup_left htd)
  rw [T.lv0.prk_smul, hpw, smul_smul] at h0
  have hne : T.atT.res v t * (T.atT.res v s * T.atT.res v s') ≠ 0 :=
    mul_ne_zero (res_ne T ht) (mul_ne_zero (res_ne T hs) (res_ne T hs'))
  exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_left hne)

theorem ptInj_holds (T : Forms0 D u) : PtInj T := by
  rintro v c g _ γ η κ hD x x' y ⟨z, hzx, s, hs, hz, hy⟩ ⟨z', hzx', s', hs', hz', hy'⟩
  obtain ⟨w, hw, hpw⟩ := ptz_sub T z z' s s' hz hz' hy hy'
  rw [sub_self, smul_zero] at hpw
  have hwP : w.1 ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c := (T.lv0.prk_ker v c w).1 hpw
  have hb := lp_smul_map _ ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    _ _ (dn_bwd T hD) _ hwP
  rw [hw, ← Matrix.mulVec_smul, inv_mv] at hb
  obtain ⟨t, ht, htd⟩ := (rlv_mem_locP _ _ _).1 hb
  have h0 : T.lv0.pr v _ ((t * (s * s')) • (z - z')) = 0 := by
    refine (T.lv0.pr_ker v _ _).2 ?_
    show (t * (s * s')) • (z.1 - z'.1) ∈ _
    rw [mul_smul]
    exact htd
  rw [T.lv0.pr_smul, map_sub, hzx, hzx'] at h0
  have hne : T.atT.res v (t * (s * s')) ≠ 0 := by
    rw [map_mul, map_mul]
    exact mul_ne_zero (res_ne T ht) (mul_ne_zero (res_ne T hs) (res_ne T hs'))
  exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_left hne)

theorem dn_img (T : Forms0 D u) {v : (D.mem u).A.vT} {c : (D.mem u).C.cls 0}
    {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)}
    {γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))}
    {η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)} {κ : T.cls0.lev.U}
    (hD : DnMvL T v c g γ η κ) (m : Fin (D.R.N 0) → D.host.E) (hm : m ∈ Lk T.atT 0 (Nat.zero_le _) v c) :
    ∃ t : 𝓞 D.host.E, t ∉ T.atT.Pv v ∧
      ∃ x ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g), γ.1.1 *ᵥ x = t • m := by
  have h1 : m ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) :=
    CrossDiaZero.dnk_lk_locP T v c (mem_localization_of_mem₂ _ hm)
  rw [← hD.2.2.1] at h1
  obtain ⟨t, ht, htm⟩ := (rlv_mem_locP _ _ _).1 h1
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 htm
  exact ⟨t, ht, x, hx, hxe⟩

theorem one_nmem (T : Forms0 D u) {v : (D.mem u).A.vT} : (1 : 𝓞 D.host.E) ∉ T.atT.Pv v := fun h => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h)

set_option maxHeartbeats 1000000 in
theorem ptSurj_holds (T : Forms0 D u) : PtSurj T := by
  intro v c g _ γ η κ hD y
  obtain ⟨w0, hw0⟩ := T.lv0.prk_surj v c y
  obtain ⟨t, ht, x, hx, hxe⟩ := dn_img T hD w0.1 w0.2
  obtain ⟨r, hr⟩ := T.atT.res_surj v (T.atT.res v t)⁻¹
  have htne := res_ne T ht
  have hrx : r • x ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) := Submodule.smul_mem _ r hx
  have hz1 : (1 : 𝓞 D.host.E) • (γ.1.1 *ᵥ (r • x)) ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
    rw [one_smul, Matrix.mulVec_smul, hxe, smul_smul]
    exact Submodule.smul_mem _ _ w0.2
  refine ⟨T.lv0.pr v _ ⟨r • x, hrx⟩, ⟨r • x, hrx⟩, rfl, 1, one_nmem T, hz1, ?_⟩
  have e : (⟨_, hz1⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = (r * t) • w0 := by
    apply Subtype.ext
    show (1 : 𝓞 D.host.E) • (γ.1.1 *ᵥ (r • x)) = (r * t) • w0.1
    rw [one_smul, Matrix.mulVec_smul, hxe, smul_smul]
  rw [e, T.lv0.prk_smul, map_mul, hr, inv_mul_cancel₀ htne, one_smul, map_one, one_smul, hw0]

theorem dUPt0F_of_vals (T : Forms0 D u) (vS : ValSame T) (vT : ValTe T) (vD : ValDia T) : DUPt0F T :=
  dUPt0F_of T (ptEx_holds T) (ptWd_holds T) (ptInj_holds T) (ptSurj_holds T) vS vT vD

theorem dUAll_of_vals (h : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), ValSame T ∧ ValTe T ∧ ValDia T) :
    Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.DUAll := dUAll_of fun D u T =>
  duFib_of_pt T (dUPt0F_of_vals T (h D u T).1 (h D u T).2.1 (h D u T).2.2)

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
