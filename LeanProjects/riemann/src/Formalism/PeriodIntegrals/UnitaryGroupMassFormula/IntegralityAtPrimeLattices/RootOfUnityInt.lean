import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.IntegralityAtFormsOfIncrements
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.NaturalTranslateAdelicFunction

noncomputable section

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB NumberField Classical
  IsDedekindDomain Formalism.UG

variable {D : D7} {u : D.what₂.Word}

def IntInv (w : D.what₂.places.Pl) {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ N' : Matrix (Fin n) (Fin n) ℂ, N * N' = 1 ∧ (∀ a b, N a b ∈ bwA_Ow D w) ∧ ∀ a b, N' a b ∈ bwA_Ow D w

def UpLatLoc0 (T : Forms0 D u) : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v c (z : ↥(Ld D u 0 (Nat.zero_le _) c)),
    (D.fm u).fv 0 v c (T.lv0.pr v c z) = 1 →
    ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
      (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U),
      (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        (T.cls0.y ((D.fm u).up 0 v c (T.lv0.pr v c z))).1 = (T.cls0.y c).1 * η.1 * κ.1 →
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (clsCrd D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c z)))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c) →
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c z)))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) →
      ∀ B B₂ B' : GL (Fin (D.R.N 0)) D.host.E,
        IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) B →
        IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) ((D.fm u).up 0 v c (T.lv0.pr v c z)) : Set _) B₂ →
        IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v ((D.fm u).up 0 v c (T.lv0.pr v c z)) : Set _) B' →
        ∀ τ, IntInv w
          ((if τ = (D.fm u).tauOf w v then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ
              else atInf (embT D) (B₂⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ) *
            atInf (embT D) ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ *
            atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ)

theorem bases0 (T : Forms0 D u) (c : (D.mem u).C.cls 0) :
    (∃ B : GL (Fin (D.R.N 0)) D.host.E, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) B) ∧
    ∀ v, ∃ B' : GL (Fin (D.R.N 0)) D.host.E,
      IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) B' := by
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have hL := bwB_clsCrd_lat D u 0 (Nat.zero_le _) c
  obtain ⟨d, hd, hle⟩ := dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))
    (bwB_gramN_det D 0 (Nat.zero_le _)) _ hL
  obtain ⟨d0, hd0, hle0⟩ := exists_le_bnd _ hL
  have hLd : Ld D u 0 (Nat.zero_le _) c ≤ bnd d := hle
  have hLd_sp := dual_span (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) _ hL
  refine ⟨exists_isLocBasis _ _ _ (fg_of_le_bnd hd hLd) hLd_sp, fun v => exists_isLocBasis _ _ _ ?_ ?_⟩
  · refine fg_of_le_bnd (mul_ne_zero hd hd0) (sup_le (hle0.trans (bnd_mono d0 d)) ?_)
    refine (Submodule.smul_le_right.trans hLd).trans ?_
    rw [mul_comm]
    exact bnd_mono d d0
  · exact eq_top_iff.2 (hL.span_eq_top ▸ Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left))

theorem rootOfUnity_int (w : D.what₂.places.Pl) (r : D.what₂.LL) {n : ℕ} (hn : 0 < n) (hr : r ^ n = 1) :
    r ∈ intW D.what₂.places w := by
  show 0 ≤ (D.what₂.places.val w) r
  have h1 := congrArg (D.what₂.places.val w) hr
  rw [AddValuation.map_pow, AddValuation.map_one] at h1
  generalize hv : (D.what₂.places.val w) r = x at h1 ⊢
  cases x with
  | top => exact le_top
  | coe a =>
    have h2 : ((n • a : ℤ) : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by
      rw [WithTop.coe_nsmul, WithTop.coe_zero]
      exact h1
    have h3 : n • a = 0 := WithTop.coe_injective h2
    have ha : a = 0 := (smul_eq_zero.mp h3).resolve_left hn.ne'
    exact WithTop.coe_nonneg.mpr ha.ge

theorem chi_inv_int (T : Forms0 D u) (hC : LocalLatticeBases.ChiFin0 T) (w : D.what₂.places.Pl) (κ : T.cls0.lev.U) :
    ∃ r ∈ intW D.what₂.places w, D.what₂.embLL r = ((((T.cls0.lev.chi κ)⁻¹ : ℂˣ)) : ℂ) := by
  obtain ⟨n, hn, H⟩ := hC
  obtain ⟨hpow, r, hr⟩ := H 0 (Nat.zero_le _) rfl κ
  have hrn : r ^ n = 1 := by
    apply D.what₂.embLL.injective
    rw [map_pow, hr, map_one]
    exact hpow
  refine ⟨r⁻¹, rootOfUnity_int w r⁻¹ hn (by rw [inv_pow, hrn, inv_one]), ?_⟩
  rw [map_inv₀, hr, Units.val_inv_eq_inv_val]
  rfl

theorem valSc_smul (T : Forms0 D u) (w : D.what₂.places.Pl) (c : (D.mem u).C.cls 0) (h : (D.mem u).C.Y 0 → ℂ)
    (r : D.what₂.LL) (hr : r ∈ intW D.what₂.places w) (hh : ValSc T w c h) :
    ValSc T w c (fun s => D.what₂.embLL r * h s) := by
  unfold ValSc at hh ⊢
  unfold Formalism.L2.Forms.IntSpan at hh ⊢
  intro B hB
  obtain ⟨P, hP, hz⟩ := hh B hB
  refine ⟨D.what₂.embLL r • P, ?_, ?_⟩
  · clear hz
    induction hP using AddSubgroup.closure_induction with
    | mem p hp =>
      obtain ⟨r', f, hr', hf, rfl⟩ := hp
      apply AddSubgroup.subset_closure
      exact ⟨r * r', f, (intW D.what₂.places w).mul_mem hr hr', hf, by rw [map_mul, mul_smul]⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  · intro z
    show D.what₂.embLL r * h z = _
    rw [hz z]
    simp [map_smul, smul_eq_mul]

theorem fnOf_tr (s : D.what₂.Tau → ℤ) (M : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ) (g : GL (Fin (D.R.N 0)) D.host.E)
    (hg : g ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (y : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embT D))) :
    fnOf _ s M P (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) g hg y) =
      fnOf _ s (fun τ => M τ * atInf (embT D) (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ) P y := by
  unfold fnOf frameTranslate
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.mul_assoc]

theorem valSc_tr (T : Forms0 D u) (w : D.what₂.places.Pl) (c : (D.mem u).C.cls 0) (h : (D.mem u).C.Y 0 → ℂ)
    (g : GL (Fin (D.R.N 0)) D.host.E) (hg : g ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (H : ∀ B : GL (Fin (D.R.N 0)) D.host.E, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) B →
      ∃ M : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ,
      ∃ P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0),
        (∀ z, h z = fnOf _ (shiftOf (lamT u 0)) M P (T.val0.eY z)) ∧
        ∀ τ, IntInv w (M τ * atInf (embT D) (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ *
          atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ)) :
    ValSc T w c (fun s => h (T.val0.eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) g hg (T.val0.eY s)))) := by
  intro B hB
  obtain ⟨M, P, hP, hPe, hN⟩ := H B hB
  choose N' hNN' hNw hN'w using hN
  set N : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    M τ * atInf (embT D) (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ *
      atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ with hNdef
  refine ⟨MvPolynomial.C (∏ τ, (N τ).det ^ shiftOf (lamT u 0) τ) * subP N P,
    bwG_intSpan_allSubP D w _ N _ (fun τ q hq => local_GL_stabilises_lattice D w _ _ _ (N τ) (N' τ) (hNN' τ)
      (hNw τ) (hN'w τ) q hq) P hP, fun z => ?_⟩
  show h _ = _
  rw [hPe, Equiv.apply_symm_apply, fnOf_tr, ← LocalLatticeBases.fnOf_mul]
  have hM : (fun τ => M τ * atInf (embT D) (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ) =
      fun τ => N τ * atInf (embT D) ((B⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ := by
    funext τ
    simp only [hNdef, Matrix.mul_assoc]
    rw [LocalLatticeBases.at_infinity_mul_inv, Matrix.mul_one]
  rw [hM]

theorem upIncInt0_of (T : Forms0 D u) (hC : LocalLatticeBases.ChiFin0 T) (hL : UpLatLoc0 T) : UpIncInt0 T := by
  intro w hw hs v c x hx h hh
  obtain ⟨z, rfl⟩ := T.lv0.pr_surj v c x
  obtain ⟨γ, η, κ, h1, h2, h3, h4, -, h6⟩ := T.up_natural_level_zero v c z hx
  have e : (D.fm u).upT 0 v c (T.lv0.pr v c z) h = fun s =>
      ((((T.cls0.lev.chi κ)⁻¹ : ℂˣ)) : ℂ) * h (T.val0.eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ.1⁻¹
        ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).inv_mem γ.2) (T.val0.eY s))) :=
    funext fun s => h6 h s _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.is_translate_inverse T γ s)
  rw [e]
  obtain ⟨r, hr, her⟩ := chi_inv_int T hC w κ
  rw [← her]
  refine valSc_smul T w c _ r hr (valSc_tr T w c h _ _ fun B hB => ?_)
  obtain ⟨B₂, hB₂⟩ := (bases0 T ((D.fm u).up 0 v c (T.lv0.pr v c z))).1
  obtain ⟨B', hB'⟩ := (bases0 T ((D.fm u).up 0 v c (T.lv0.pr v c z))).2 v
  obtain ⟨P, hP, hPe⟩ := hh B₂ B' hB₂ hB'
  exact ⟨_, P, hP, hPe, fun τ => hL w hw hs v c z hx γ η κ h1 h2 h3 h4 B B₂ B' hB hB₂ hB' τ⟩

end PI.UnitaryGroupMassFormula.IAT

end
