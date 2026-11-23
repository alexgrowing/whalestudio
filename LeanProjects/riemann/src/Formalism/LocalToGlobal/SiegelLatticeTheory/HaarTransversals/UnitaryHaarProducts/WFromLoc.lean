import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLUnit
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.TensInt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BesselLevi
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ConcreteSettingExists

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature
open Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.ConcreteSettingExists
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.WFL

variable {k r : ℕ}

section Main
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem split_S {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf z0)
    (s : Formalism.REAL.UJ ε) {hB mB : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hsm : Qi ε e f wf z0 * uMat s * Qm e f wf z0 = hB * mB)
    (h1 : (Qm e f wf z0 * hB * Qi ε e f wf z0)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * hB * Qi ε e f wf z0) = Formalism.REAL.Jm ε)
    (h2 : (Qm e f wf z0 * mB * Qi ε e f wf z0)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * mB * Qi ε e f wf z0) = Formalism.REAL.Jm ε) :
    s = toUJ _ h1 * toUJ _ h2 := by
  apply UJ_ext
  rw [uMat_mul, uMat_toUJ, uMat_toUJ]
  have : Qm e f wf z0 * hB * Qi ε e f wf z0 * (Qm e f wf z0 * mB * Qi ε e f wf z0) =
      Qm e f wf z0 * (hB * mB) * Qi ε e f wf z0 := by
    simp only [← Matrix.mul_assoc]; rw [Matrix.mul_assoc _ (Qi ε e f wf z0) (Qm e f wf z0), Qi_mul_Qm hF,
      Matrix.mul_one]
  rw [this, ← hsm]
  simp only [← Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.one_mul]
  rw [Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.mul_one]

theorem wblk_core (hQK : QuotProdK) (hHN : LocHNProps) (hNU : NUnimodLoc) (hTens : TensInt) {D : D7}
    (hB : BesselNVGap) (hCW : CoefWeightedLoc) (hWl : WlocExists) (hGB : GapBigOfGapHyp D) (hG : GapHyp D)
    (I : AutInst) (ιE : I.E ≃+* D.host.E) (ιE_conj : ∀ x : I.E, ιE (star x) = D.host.conj (ιE x))
    (ιE_F : ∀ y : D.host.E, y ∈ D.host.F ↔ ∃ a : I.F, ιE (algebraMap I.F I.E a) = y)
    (bas : Module.Basis (Fin I.n) D.host.E (VS D).V) (J_eq : ∀ i j, ιE (I.J i j) = (VS D).hT (bas i) (bas j))
    (L_eq : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ (∑ i, ιE (x i) • bas i) ∈ (VS D).L0)
    (pl : InfinitePlace I.F ≃ D.what₂.Tau) (φ_eq : ∀ v (x : I.E), I.φ v x = embS D (pl v) (ιE x))
    (n_eq : I.n = D.R.r) (eps_eq : ∀ v (i : Fin I.n), I.ε v i = epsS D.R (Fin.cast n_eq i))
    (L : UnitaryLatticeData D) (Ps : AdditiveCharacterData (⟨I, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ : UnitaryGroupInstance D))
    (Rf : ReferenceFrame (⟨I, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ : UnitaryGroupInstance D) L)
    (Bu : AutomorphicBundle (⟨I, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ : UnitaryGroupInstance D) Ps Rf)
    (Pi : RepresentationData (⟨I, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ : UnitaryGroupInstance D) L)
    (Mu : MuBlocks (⟨I, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ : UnitaryGroupInstance D) L) :
    Nonempty (WBlk (⟨I, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ : UnitaryGroupInstance D) L Bu Pi Mu) := by

  have hJc : ∀ v (p q : (VS D).V), hJ (I.ε v) (rv I v (crdOf I ιE bas p)) (rv I v (crdOf I ιE bas q)) =
      I.φ v (ιE.symm ((VS D).hT p q)) :=
    fun v p q => hJ_crdA (⟨I, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ : UnitaryGroupInstance D) v p q
  cases I with
  | mk F E cm n J J_herm J_det L0 L_span L_fg L_dual ε φ φ_over P P_unit P_spec topf_open topf_basis =>
  have hn : n = 2 * D.R.rS + D.R.k + 1 := n_eq.trans (dimS_eq D.R).symm
  subst hn

  set eV : InfinitePlace F → Fin D.R.rS → Fin (2 * D.R.rS + D.R.k + 1) → ℂ :=
    fun v a => rv _ v (crdOf _ ιE bas (L.eX a)) with heV
  set fV : InfinitePlace F → Fin D.R.rS → Fin (2 * D.R.rS + D.R.k + 1) → ℂ :=
    fun v a => rv _ v (crdOf _ ιE bas (L.fY a)) with hfV
  set zV : D.what₂.Word → InfinitePlace F → Fin (2 * D.R.rS + D.R.k + 1) → ℂ :=
    fun u v => rv _ v (crdOf _ ιE bas (L.zu u)) with hzV
  set TV : D.what₂.Word → ℝ := fun u => (((D.mem u).A.T : ℕ) : ℝ) with hTV
  have hT : ∀ u, 0 < TV u := fun u => Nat.cast_pos.mpr (D.mem u).A.T_prime.pos
  have hFr : ∀ u v, IsFrameJ (ε v) (eV v) (fV v) (Pi.wfr u v) (z0v (TV u) (zV u v)) := by
    intro u v
    refine isFrameJ_of (eV v) (fV v) (zV u v) (Pi.wfr u v) (hT u) (fun a b => ?_) (fun a b => ?_) (fun a b => ?_)
      (fun a => ?_) (fun a => ?_) ?_ (Pi.wfr_on u v) (fun c a => ((Pi.wfr_perp u v a).1 c).1)
      (fun c a => ((Pi.wfr_perp u v a).1 c).2) (fun a => (Pi.wfr_perp u v a).2)
    · rw [heV]; simp only; rw [hJc, L.ee]; simp
    · rw [hfV]; simp only; rw [hJc, L.ff]; simp
    · rw [heV, hfV]; simp only; rw [hJc, L.ef]; split_ifs <;> simp
    · rw [heV, hzV]; simp only; rw [hJc, (L.zu_orth u a).1]; simp
    · rw [hfV, hzV]; simp only; rw [hJc, (L.zu_orth u a).2]; simp
    · rw [hzV]; simp only; rw [hJc, L.zu_norm]; simp [hTV]

  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hke : Even D.R.k := D.R.k_even
  have hg : 0 < gD D := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hε : ∀ v, ε v = eps48 D.R.k D.R.rS := fun v => funext fun i =>
    (eps_eq v i).trans (by simp [epsS, eps48])
  have hlamE : ∀ v, (fun i => lamS D.R (D.hc (pl v)) (Fin.cast n_eq i)) =
      lam48 D.R.k D.R.rS (fun i => ((D.hc (pl v)).v i : ℝ)) (fun j => ((D.hc (pl v)).b (Fin.cast (mEqR D.R) j) : ℝ)) :=
    fun v => funext fun i => lam_matchR D.R (D.hc (pl v)) i n_eq
  have hDS : ∀ v, IsDS (ε v) (lam48 D.R.k D.R.rS (fun i => ((D.hc (pl v)).v i : ℝ))
      (fun j => ((D.hc (pl v)).b (Fin.cast (mEqR D.R) j) : ℝ))) (Bu.σ v) := fun v => by
    rw [← hlamE v]; exact Bu.ds v
  have hwL : ∀ v, IsLowUnit (ε v) (lam48 D.R.k D.R.rS (fun i => ((D.hc (pl v)).v i : ℝ))
      (fun j => ((D.hc (pl v)).b (Fin.cast (mEqR D.R) j) : ℝ))) (Bu.σ v) (Bu.w v) := fun v => by
    rw [← hlamE v]; exact Bu.low v
  have hl : ∀ v, Formalism.QuantumDeterminants.IsHCParam (lam48 D.R.k D.R.rS (fun i => ((D.hc (pl v)).v i : ℝ))
      (fun j => ((D.hc (pl v)).b (Fin.cast (mEqR D.R) j) : ℝ))) := fun v => by
    have h := Formalism.MainNotions.S.Inh.obj_isHCParam_lamSH D.R (D.hc (pl v))
    have e : lamSH D.R (D.hc (pl v)) = lam48 D.R.k D.R.rS (fun i => ((D.hc (pl v)).v i : ℝ))
        (fun j => ((D.hc (pl v)).b (Fin.cast (mEqR D.R) j) : ℝ)) :=
      funext fun i => lam_matchR D.R (D.hc (pl v)) i (dimS_eq D.R)
    rwa [e] at h
  have hGap : ∀ v, GapBig D.R.k D.R.rS (fun j => ((D.hc (pl v)).b (Fin.cast (mEqR D.R) j) : ℝ)) :=
    fun v => hGB (mEqR D.R).symm hG (pl v)

  have hHset : ∀ u, Hset _ (Set.range (eC ⟨_, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ L) ∪
      Set.range (fC ⟨_, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ L) ∪
      {zC ⟨_, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ L u}) =
      {s : ∀ v, Formalism.REAL.UJ (ε v) | ∀ v, (∀ a, uMat (s v) *ᵥ eV v a = eV v a) ∧
        (∀ a, uMat (s v) *ᵥ fV v a = fV v a) ∧ uMat (s v) *ᵥ zV u v = zV u v} := by
    intro u; ext s
    simp only [Hset, Set.mem_setOf_eq, Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · intro h v
      exact ⟨fun a => h v _ (Or.inl (Or.inl ⟨a, rfl⟩)), fun a => h v _ (Or.inl (Or.inr ⟨a, rfl⟩)),
        h v _ (Or.inr rfl)⟩
    · rintro h v x ((⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl)
      · exact (h v).1 a
      · exact (h v).2.1 a
      · exact (h v).2.2
  have hQ := fun u => quotRaw hQK hHN hNU eV fV (zV u) (Pi.wfr u) (hT u) (hFr u) (Mu.muN u) (Mu.muH u) (Mu.nuQ u)
    (Mu.muN_haar u) (by have h := Mu.muH_haar u; rw [hHset u] at h; exact h) (Mu.nuQ_weil u)
  choose μS νl C hC0 hCt hloc hK using hQ

  have hP := fun u v => locPack hB hCW hWl (hε v) hk hke (hT u) hg
    (Formalism.MainNotions.S.Inh.obj_isHCParam_u D.R (D.hcW u (pl v))) (hl v)
    (interlace_of D.R (D.hc (pl v)) (D.hcW u (pl v)) (D.hcW_v u (pl v)) (D.hcW_b u (pl v)))
    (halfInt_of D.R (D.hc (pl v)) (D.hcW u (pl v))) (hGap v) (z := zV u v) rfl (hFr u v) (hDS v) (hwL v)
    (Pi.piLoc_type u v) (hloc u v).1 (hloc u v).2
  choose Wl hWc hWe hWr hW1 hW2 hWw hWα using hP

  classical
  have hne : Nonempty (InfinitePlace F) := ⟨pl.symm (D.eTau.symm (Classical.arbitrary _))⟩
  let v0 : InfinitePlace F := Classical.arbitrary _
  let cU : D.what₂.Word → ℂ := fun u => (((C u).toReal ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  let cv : D.what₂.Word → InfinitePlace F → ℂ := fun u v => if v = v0 then cU u else 1
  have hcv : ∀ u, ∏ v, cv u v = cU u := fun u => by simp [cv, Finset.prod_ite_eq']
  let Wloc : ∀ u v, Formalism.REAL.UJ (ε v) → Pi.Vloc u v := fun u v y => cv u v • Wl u v y
  have hWlc : ∀ u v, Continuous (Wloc u v) := fun u v => (hWc u v).const_smul (cv u v)

  have hinv : ∀ u v, ∀ s ∈ HNset (ε v) (eV v) (fV v) (Pi.wfr u v) (z0v (TV u) (zV u v)) (zBv D.R.k D.R.rS (TV u)),
      ∀ y, ‖Wloc u v (s * y)‖ₑ = ‖Wloc u v y‖ₑ := by
    intro u v s hs y
    simp only [Wloc, enorm_smul]
    rw [show ‖Wl u v (s * y)‖ₑ = ‖Wl u v y‖ₑ by
      simp only [enorm_eq_nnnorm]
      congr 1
      exact NNReal.eq (loc_norm_inv (hT u) (hFr u v) (Pi.piLoc_type u v) (hWe u v) hs y)]
  have hnorm : ∀ u (x : ∀ v, Formalism.REAL.UJ (ε v)),
      ‖Pi.tensU u (fun v => Wloc u v (x v))‖ₑ = ∏ v, ‖Wloc u v (x v)‖ₑ := by
    intro u x
    simp only [enorm_eq_nnnorm]
    rw [← ENNReal.coe_finset_prod]
    congr 1
    exact NNReal.eq (by push_cast; exact Formalism.L2.SG.Pf.WuDec.norm_tens (Pi.tensU_inner u) _)
  refine ⟨⟨fun u x => Pi.tensU u (fun v => Wloc u v (x v)), fun u => ?_, Wloc, hWlc, fun u x => rfl⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs x
    have hsv : ∀ v, ∃ h ∈ UWset D.R.k D.R.rS (zBv D.R.k D.R.rS (TV u)), ∃ m ∈ Nset D.R.k D.R.rS,
        Qi (ε v) (eV v) (fV v) (Pi.wfr u v) (z0v (TV u) (zV u v)) * uMat (s v) *
          Qm (eV v) (fV v) (Pi.wfr u v) (z0v (TV u) (zV u v)) = h * m :=
      fun v => HNset_of_inS (fun k r T hT s hs h1 h2 => bessel_levi_formula k r T hT s hs h1 h2) (hFr u v) (hT u)
        (Qm_zB (hT u) _) (hs v)
    choose hB hhB mB hmB hsm using hsv
    let gH : ∀ v, Formalism.REAL.UJ (ε v) := fun v => toUJ _ (conjQ_UJ (hFr u v) (hhB v).1)
    let gN : ∀ v, Formalism.REAL.UJ (ε v) := fun v => toUJ _ (conjQ_UJ (hFr u v) (hmB v).1)
    have hsplit : s = gH * gN := funext fun v => split_S (hFr u v) (s v) (hsm v) _ _
    have hfixv : ∀ v, (∀ a, uMat (gH v) *ᵥ eV v a = eV v a) ∧ (∀ a, uMat (gH v) *ᵥ fV v a = fV v a) ∧
        uMat (gH v) *ᵥ zV u v = zV u v := fun v => rev_UW (hFr u v) (Qm_zB (hT u) _) (hhB v)
    have hgH : gH ∈ Hset _ (Set.range (eC ⟨_, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ L) ∪
        Set.range (fC ⟨_, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ L) ∪
        {zC ⟨_, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ L u}) := by
      intro v y hy
      rcases hy with ((⟨a, rfl⟩ | ⟨a, rfl⟩) | hy)
      · exact (hfixv v).1 a
      · exact (hfixv v).2.1 a
      · rw [Set.mem_singleton_iff] at hy; subst hy; exact (hfixv v).2.2
    have hgN : ∀ v, InN (ε v) (eV v) (zV u v) (uMat (gN v)) := fun v =>
      rev_N (hFr u v) (Qm_zB (hT u) _) (inWb_zB _) (hmB v)
    have hgHS : gH ∈ Sinf _ (eC ⟨_, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ L)
        (zC ⟨_, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ L u) := by
      intro v
      refine ⟨fun a => ?_, ?_⟩
      · have : (uMat (gH v) - 1) *ᵥ eV v a = 0 := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, (hfixv v).1 a, sub_self]
        exact this ▸ Submodule.zero_mem _
      · have : (uMat (gH v) - 1) *ᵥ zV u v = 0 := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, (hfixv v).2.2, sub_self]
        exact this ▸ Submodule.zero_mem _
    have hgNS : gN ∈ Sinf _ (eC ⟨_, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ L)
        (zC ⟨_, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ L u) := fun v => (hgN v).1
    obtain ⟨-, hmul, -, hNtriv, -⟩ := Pi.piU_rep u
    have hpiU : Pi.piU u s = Pi.piU u gH := by
      rw [hsplit, hmul gH hgHS gN hgNS, hNtriv gN hgN, mul_one]
    have hL : (fun v => Wloc u v ((s * x) v)) = fun v =>
        (cv u v * psiR (ε v) (gD D) (eV v) (fV v) (zV u v) (uMat (s v))) •
          piB (ε v) (eV v) (fV v) (Pi.wfr u v) (z0v (TV u) (zV u v)) (Pi.piLoc u v) (hB v) (Wl u v (x v)) := by
      funext v
      show cv u v • Wl u v (s v * x v) = _
      rw [hWe u v (s v) (x v) (hB v) (hhB v) (mB v) (hmB v) (hsm v), smul_smul]
    have hR : Pi.piU u s (Pi.tensU u (fun v => Wloc u v (x v))) = Pi.tensU u (fun v => cv u v •
        piB (ε v) (eV v) (fV v) (Pi.wfr u v) (z0v (TV u) (zV u v)) (Pi.piLoc u v) (hB v) (Wl u v (x v))) := by
      rw [hpiU, Pi.tensU_equiv u gH hgH]
      congr 1; funext v
      show Pi.piLoc u v _ (cv u v • Wl u v (x v)) = _
      rw [map_smul]; rfl
    show Pi.tensU u (fun v => Wloc u v ((s * x) v)) = _ • Pi.piU u s (Pi.tensU u (fun v => Wloc u v (x v)))
    rw [hL, hR, Formalism.L2.SG.Pf.WuDec.tens_smul (Pi.tensU_inner u), Formalism.L2.SG.Pf.WuDec.tens_smul (Pi.tensU_inner u),
      smul_smul, Finset.prod_mul_distrib, mul_comm (∏ v, cv u v)]
    rfl
  · intro x
    let G : ∀ v, Formalism.REAL.UJ (ε v) → Pi.Vloc u v := fun v t => cv u v •
      ((((fdegOf (Formalism.REAL.muG (ε v)) (Bu.σ v) (Bu.w v) : ℝ) : ℂ) * star ⟪Bu.w v, Bu.σ v (uMat t) (Bu.w v)⟫_ℂ) •
        Wl u v (x v * t))
    have hGi : ∀ v, Integrable (G v) (Formalism.REAL.muG (ε v)) := fun v => ((hWr u v (x v)).1).smul (cv u v)
    obtain ⟨hint, hval⟩ := hTens (InfinitePlace F) (fun v => Formalism.REAL.UJ (ε v)) (fun v => Formalism.REAL.muG (ε v))
      (Pi.Vloc u) (Pi.Vpi u) (Pi.tensU u) (Pi.tensU_inner u) (Pi.tensU_span u) G hGi
    have hpt : ∀ y : ∀ v, Formalism.REAL.UJ (ε v),
        Formalism.L2.SG.ProjRows.phInf _ Bu.σ Bu.w (fun v => fdegOf (Formalism.REAL.muG (ε v)) (Bu.σ v) (Bu.w v)) y •
          Pi.tensU u (fun v => Wloc u v ((x * y) v)) = Pi.tensU u (fun v => G v (y v)) := by
      intro y
      have hG : (fun v => G v (y v)) = fun v => (cv u v * ((((fdegOf (Formalism.REAL.muG (ε v)) (Bu.σ v) (Bu.w v) : ℝ) : ℂ) *
          star ⟪Bu.w v, Bu.σ v (uMat (y v)) (Bu.w v)⟫_ℂ))) • Wl u v (x v * y v) := by
        funext v; simp only [G]; rw [smul_smul]
      have hW' : (fun v => Wloc u v ((x * y) v)) = fun v => cv u v • Wl u v (x v * y v) := rfl
      rw [hG, hW', Formalism.L2.SG.Pf.WuDec.tens_smul (Pi.tensU_inner u), Formalism.L2.SG.Pf.WuDec.tens_smul (Pi.tensU_inner u),
        smul_smul, Finset.prod_mul_distrib]
      congr 1
      simp only [Formalism.L2.SG.ProjRows.phInf, Formalism.L2.SG.ProjRows.mInf, Complex.ofReal_prod, star_prod,
        ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v _ => by rw [mul_comm _ (cv u v)]
    refine ⟨hint.congr (ae_of_all _ fun y => (hpt y).symm), ?_⟩
    rw [integral_congr_ae (ae_of_all _ hpt), hval]
    congr 1; funext v
    simp only [G]
    rw [integral_smul, (hWr u v (x v)).2]
  · exact (Formalism.L2.SG.Pf.WuDec.continuous_tens (Pi.tensU_inner u)).comp
      (continuous_pi fun v => (hWlc u v).comp (continuous_apply v))
  ·
    rw [lintegral_congr (fun x => hnorm u x),
      hK u (fun v y => ‖Wloc u v y‖ₑ) (fun v => (hWlc u v).enorm.measurable) (fun v s hs y => hinv u v s hs y)]
    refine ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (hCt u)) (ENNReal.prod_lt_top fun v _ => ?_)
    simp only [Wloc, enorm_smul]
    rw [lintegral_const_mul' _ _ enorm_ne_top]
    exact ENNReal.mul_lt_top enorm_lt_top (hW1 u v)
  ·
    have h2 : ∀ x : ∀ v, Formalism.REAL.UJ (ε v), ‖Pi.tensU u (fun v => Wloc u v (x v))‖ₑ ^ 2 =
        ∏ v, ‖Wloc u v (x v)‖ₑ ^ 2 := fun x => by rw [hnorm u x, Finset.prod_pow]
    rw [lintegral_congr h2,
      hK u (fun v y => ‖Wloc u v y‖ₑ ^ 2) (fun v => ((hWlc u v).enorm.measurable.pow_const 2))
        (fun v s hs y => by show ‖Wloc u v (s * y)‖ₑ ^ 2 = ‖Wloc u v y‖ₑ ^ 2; rw [hinv u v s hs y])]
    have hloc2 : ∀ v, ∫⁻ y, ‖Wloc u v y‖ₑ ^ 2 ∂(νl u v) = ‖cv u v‖ₑ ^ 2 := fun v => by
      simp only [Wloc, enorm_smul, mul_pow]
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top), hW2 u v, mul_one]
    simp only [hloc2]
    rw [Finset.prod_pow]
    have hcU : ∏ v, ‖cv u v‖ₑ = ‖cU u‖ₑ := by
      rw [← hcv u]; simp only [enorm_eq_nnnorm]; rw [← ENNReal.coe_finset_prod]; congr 1; rw [nnnorm_prod]
    rw [hcU]
    have ht : 0 < (C u).toReal := ENNReal.toReal_pos (hC0 u) (hCt u)
    have he : ‖cU u‖ₑ ^ 2 = (C u)⁻¹ := by
      have hnn : 0 ≤ (C u).toReal ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
      rw [show ‖cU u‖ₑ = ENNReal.ofReal ((C u).toReal ^ (-(1 / 2 : ℝ))) by
        rw [← ofReal_norm_eq_enorm]; simp only [cU]; rw [Complex.norm_real, Real.norm_of_nonneg hnn]]
      rw [← ENNReal.ofReal_pow hnn, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      norm_num
      rw [Real.rpow_neg_one, ENNReal.ofReal_inv_of_pos ht, ENNReal.ofReal_toReal (hCt u)]
    rw [he, ENNReal.mul_inv_cancel (hC0 u) (hCt u)]

end Main

section Final

theorem weighted_block_exists_of_local_data (hQK : QuotProdK) (hHN : LocHNProps) (hNU : NUnimodLoc) (D : D7)
    (hB : BesselNVGap) (hCW : CoefWeightedLoc) (hWl : WlocExists) (hGB : GapBigOfGapHyp D) :
    Formalism.L2.SG.Pf.Set3.WBlkExists D := by
  intro hG A L Ps Rf Bu Pi Mu
  obtain ⟨I, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ := A
  exact wblk_core hQK hHN hNU Formalism.L2.SG.Pf.WuDec.integrable_and_integral_pi_apply hB hCW hWl hGB hG I ιE ιE_conj ιE_F bas J_eq L_eq pl
    φ_eq n_eq eps_eq L Ps Rf Bu Pi Mu

end Final

end Formalism.L2.SG.Pf.WFL
