import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensorStatement

open PowerSeries GlobalTheory.BK

noncomputable section

namespace GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K]

theorem PhiMod.eq_xi_red_of_conn_eq_zero (P : PhiMod O K l e a ι) {v : Vec K a ι}
    (h : P.conn v = 0) : v = P.xi (red v) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  obtain ⟨w, rfl⟩ := P.xiExt.surjective v
  rw [PhiMod.conn_xiExt] at h
  have hN : ∀ τ i, N K (w τ i) = 0 := fun τ i => by
    have := congrFun (congrFun (P.xiExt.injective (h.trans (map_zero _).symm)) τ) i
    simpa using this
  have hw : w = cst (red w) := by
    funext τ i
    ext n
    rcases n with _ | n
    · simp
    · have := congrArg (coeff (n + 1)) (hN τ i)
      rw [coeff_N, map_zero] at this
      have hn : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)
      rw [cst_apply, coeff_C, if_neg (Nat.succ_ne_zero n)]
      exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hn)
  rw [PhiMod.xi_apply, PhiMod.red_xiExt, ← hw]

theorem PhiMod.mem_ext_of_plusInl (P : PhiMod O K l e a ι) {y : Vec K a ι}
    (hy : y ∈ P.Mext (invE l e (A O K))) {B : Subalgebra O K⟦X⟧} {v : Vec K a ι}
    (h : (P.plusInl hy).app v ∈ (P.plus hy).ext B) : v ∈ P.ext B := by
  rw [PhiMod.plusInl_app] at h
  refine mem_tot.2 fun τ => ?_
  obtain ⟨m, hm, hmv⟩ := (P.plus hy).mem_extc.1 (mem_tot.1 h τ)
  refine P.mem_extc.2 ⟨fun i => m (Sum.inl i), fun i => hm (Sum.inl i), ?_⟩
  have h0 : m (Sum.inr ()) = 0 := by
    have := congrFun hmv (Sum.inr ())
    simpa [join, PhiMod.plus, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using this.symm
  funext i
  have := congrFun hmv (Sum.inl i)
  simpa [join, PhiMod.plus, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h0] using this

end GlobalTheory.BK

namespace GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

namespace BKDat

theorem exists_conn_eq_zeta_of_mem_Y (D : BKDat O K l e a ι η H) {y : Vec K a ι} (hy : y ∈ D.Y) :
    ∃ s ∈ D.MMl, s ∈ D.desc.inv ∧ D.conn s = D.zeta y := by
  have hy' := mem_invE_of_mem_Y hy
  set P := D.toPhiMod.plus hy'
  set F := D.toPhiMod.plusInl hy'
  set G := D.toPhiMod.plusProj hy'
  set t := P.phi xVec - P.xi (red (P.phi xVec)) with ht
  have inj : ∀ v w, F.app v = F.app w → v = w := fun v w h => by
    rw [PhiMod.plusInl_app, PhiMod.plusInl_app] at h
    funext τ i
    exact congrFun (congrFun h τ) (Sum.inl i)
  have hct : P.conn t = F.app (D.zeta y) := by
    rw [ht, map_sub, PhiMod.conn_xi, sub_zero]
    exact D.conn_phi_extension_generator_eq_zeta hy'
  have hrt : red t = 0 := by
    rw [ht, map_sub, PhiMod.red_xi, sub_self]
  have hx : G.app t = 0 := by
    have h1 : (rankOne O K l e fun _ : ZMod a => 0).conn (G.app t) = 0 := by
      rw [← Hom.app_conn, hct, PhiMod.plusInl_app, PhiMod.plusProj_app]
      rfl
    rw [PhiMod.eq_xi_red_of_conn_eq_zero _ h1, Hom.red_app, hrt, map_zero, map_zero]
  have key : ∀ τ, t τ (Sum.inr ()) = 0 := fun τ => by
    have := congrFun (congrFun hx τ) ()
    rw [← join_eta t, PhiMod.plusProj_app] at this
    simpa using this
  set s : Vec K a ι := fun τ i => t τ (Sum.inl i)
  have hts : t = F.app s := by
    rw [PhiMod.plusInl_app]
    conv_lhs => rw [← join_eta t]
    congr 1
    funext τ
    exact key τ
  have hxM : (xVec : Vec K a (ι ⊕ Unit)) ∈ P.M := by
    rw [← PhiMod.bas_inr]
    exact P.bas_mem_M _
  have htM : t ∈ P.MMl := by
    refine sub_mem (P.ext_mono ((A_le_S l e).trans (le_away _ _)) (P.phi_mem_L hxM)) ?_
    rw [PhiMod.xi_apply]
    refine ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a (ι ⊕ Unit) P).2 _).2 (mem_tot.2 fun τ i => ?_)
    rw [cst_apply]
    exact HasK.C_mem _
  refine ⟨s, D.toPhiMod.mem_ext_of_plusInl hy' (hts ▸ htM), fun g => ?_, inj _ _ ?_⟩
  · have hΔ : (D.desc.plus hy' hy.2).act g t = t := by
      rw [ht, map_sub, Descent.act_phi, Descent.tameDescent_extended_action_extraVector D.desc hy' hy.2 g, Descent.act_xi,
        ← Descent.red_act, Descent.act_phi, Descent.tameDescent_extended_action_extraVector D.desc hy' hy.2 g]
    apply inj
    have h2 : (D.desc.plus hy' hy.2).act g (F.app s) = F.app s := by rw [← hts]; exact hΔ
    exact ((Descent.plusInl D.desc hy' hy.2).app_act g s).trans h2
  · rw [Hom.app_conn, ← hts, hct]

end BKDat

end GlobalTheory.BK

namespace GlobalTheory.BK

namespace BKDat

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

theorem exists_conn_eq_zeta (D : BKDat O K l e a ι η H) {y : Vec K a ι} (hy : y ∈ D.Yl) :
    ∃ s ∈ D.MMl, s ∈ D.desc.inv ∧ D.conn s = D.zeta y := by
  obtain ⟨n, hn⟩ := D.desc.mem_Yl_iff.1 hy
  obtain ⟨s, hsM, hsi, hsc⟩ := D.exists_conn_eq_zeta_of_mem_Y hn
  have hl : ((l : K) ^ n) ≠ 0 := pow_ne_zero _ (l_ne_zero l)
  refine ⟨((l : K) ^ n)⁻¹ • s, ?_, D.desc.inv.smul_mem _ hsi, ?_⟩
  · have : ((l : K) ^ n)⁻¹ • s = (fun _ : ZMod a => C ((l : K) ^ n)⁻¹) • s := by
      funext τ i
      simp [smul_eq_C_mul]
    rw [this]
    exact D.smul_tot_mem_ext (fun _ => HasK.C_mem _) hsM
  · rw [map_smul, hsc, map_smul, smul_smul, inv_mul_cancel₀ hl, one_smul]

theorem Mon_mem_range_Lc : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Yl,
    (∃ s ∈ D.MMl, s ∈ D.desc.inv ∧ D.conn s = D.zeta y ∧ ∃ d : D.D, (∀ g, D.desc.actD g d = d) ∧
      D.phi s - s - D.phi y = D.xi d) ∧ ∃ w ∈ D.Zl, D.Lc w = D.Mon y := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y hy
  obtain ⟨s, hsM, hsi, hsc⟩ := D.exists_conn_eq_zeta hy
  have hyi : ∀ g, D.desc.act g y = y := hy.2
  have hsi' : ∀ g, D.desc.act g s = s := hsi
  refine ⟨⟨s, hsM, hsi, hsc, ?_⟩, D.cls (y - s), ⟨⟨y - s, ?_, rfl⟩, fun g => ?_⟩, ?_⟩
  · set v := D.phi s - s - D.phi y with hv
    have hcv : D.conn v = 0 := by
      have hz := D.zeta_eq y
      rw [PhiMod.lphi_apply, map_sub, smul_sub] at hz
      rw [hv, map_sub, map_sub, PhiMod.conn_phi, PhiMod.conn_phi, hsc, sub_right_comm]
      exact sub_eq_zero.2 hz.symm
    refine ⟨red v, fun g => ?_, D.eq_xi_red_of_conn_eq_zero hcv⟩
    rw [← Descent.red_act, hv]
    congr 1
    rw [(D.desc.act g).map_sub, (D.desc.act g).map_sub, Descent.act_phi, Descent.act_phi, hsi' g,
      hyi g]
  · rw [SetLike.mem_coe, mem_divE, smul_sub]
    refine sub_mem ((PhiMod.mem_Man _).2 (D.Mext_mono (invL_A_le_Rpi l e) (mem_divE.1 hy.1)))
      ((PhiMod.mem_Man _).2 (D.Mext_mono (invL_S_le_Rpi l e)
        (D.smul_mem_Mext ((A_le_S l e).trans (le_away _ _)) hsM)))
  · rw [Descent.actPol_cls, map_sub, hyi g, hsi' g]
  · rw [Lc_cls, PhiMod.Mon_apply, map_sub, PhiMod.EN_apply D.toPhiMod s, hsc]

end BKDat

end GlobalTheory.BK
