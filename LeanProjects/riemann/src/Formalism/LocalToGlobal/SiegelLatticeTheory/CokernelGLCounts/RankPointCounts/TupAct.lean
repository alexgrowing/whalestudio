import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemDdSPow

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.TupAct

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Pf.TupOrb
  Formalism.L2.SG.Pf.TupLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem lift_move {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ) (hu : Tu D u ≠ 0) (hu' : Tu D u' ≠ 0)
    {t : TermsOf D u' F0 Λ} {Z₁ : PairVal.MatR D} {F₁ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (h₁ : F₁ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₁)
    (r₁ : TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F₁)
    {U U' : PairVal.MatR D} (hU : IsUpUni U) (hU' : IsUpUni U') (hiU : TupGlob.IntFr U) (hiU' : TupGlob.IntFr U')
    (htie : TupGlob.TieG U U') :
    ∃ ν ∈ NLam Λ (lf D F0), ∃ m ∈ NLam Λ F₁,
      (∀ b, ν (frame (lf D F0) b) = ∑ c, U c b • frame (lf D F0) c) ∧
      (∀ b, m (frame F₁ b) = ∑ c, U' c b • frame F₁ c) ∧
      ∃ F2 ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ (U.conjTranspose * Z₁ * U'),
        TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F2 ∧ ∀ b, frame F2 b = ν⁻¹ (m (frame F₁ b)) := by
  obtain ⟨p₁, e₁⟩ := r₁
  have hFun := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 Λ hΛ
  obtain ⟨ν, hν, hνF⟩ := TupOnto.nLamOnto_holds D u F0 Λ hΛ hu U hU hiU
  obtain ⟨m, hm, hmF⟩ := TupOnto.nLamOnto_holds D u' F₁.fl Λ (isRowLat_of_pd hΛ p₁) hu' U' hU' hiU'
  have hm' : m ∈ NLam Λ F₁ := hm
  have hmF' : ∀ b, m (frame F₁ b) = ∑ c, U' c b • frame F₁ c := hmF
  have hAut : IsAutLam (VS D) Λ (ν⁻¹ * m) :=
    Formalism.L2.SG.Pf.isAutLam_mul (Formalism.L2.SG.Pf.isAutLam_inv hν.1) hm.1
  let F2 := Formalism.L2.SG.Saturated.mapL (ν⁻¹ * m) hAut.1 F₁
  have hf2 : ∀ b, frame F2 b = ν⁻¹ (m (frame F₁ b)) := fun b => by
    rw [Formalism.L2.SG.Saturated.frame_mapL]; rfl
  have hdc : DCRel Λ (lf D F0) F₁ F2 := ⟨ν⁻¹, Formalism.L2.SG.Pf.nlamPf_inv hν, m, hm', hf2, rfl⟩
  have pd2 : PD D Λ (lf D F0) u' F2 := Formalism.L2.SG.Closed.TermStable_holds D u u' F0 Λ hΛ ⟨F₁, p₁⟩ F2 hdc
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hu'
  have hFΛ : ∀ c, frame (lf D F0) c ∈ Λ := by
    intro c
    refine Fin.lastCases ?_ (fun a => ?_) c
    · rw [Formalism.L2.SG.Pf.frame_last_td]; exact hΛ.2.1.2.2.1.1
    · rw [Formalism.L2.SG.Pf.frame_castSucc_td]; exact PI.NRL.e_mem_lam D F0 Λ hΛ a
  have hiso : ∀ x y, (VS D).hT (ν x) (ν y) = (VS D).hT x y := ((Formalism.L2.SG.Pf.isAutLam_iff Λ ν).1 hν.1).1
  have hent : ∀ a b, (VS D).hT (frame (lf D F0) a) (frame F2 b) =
      (U.conjTranspose * ZhatL (lf D F0) F₁ * U') a b := fun a b => by
    rw [hf2 b]; exact zhat_lift (lf D F0) F₁ hiso hνF hmF' a b
  refine ⟨ν, hν, m, hm', hνF, hmF', F2, ⟨⟨pd2.1, pd2.2.1, ?_⟩, ?_, ?_, pd2.2.2, ?_⟩,
    ⟨pd2, (Quot.sound (show TermDef.Rel Λ (lf D F0) (PD D Λ (lf D F0) u') ⟨F₁, p₁⟩ ⟨F2, pd2⟩ from hdc)).symm.trans e₁⟩, hf2⟩
  · rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hdc]; exact h₁.1.2.2
  · refine ⟨fun a b hab => Matrix.one_apply_ne (ne_of_lt hab).symm, fun a => Matrix.one_apply_eq a, fun b => ?_⟩
    rw [frameAct_one', hf2 b]
    exact modG_lift hT' p₁.1 p₁.2.2.1 hFΛ hν.1 hm' hνF hmF' htie
      (fun c => by have := h₁.2.1.2.2 c; rwa [frameAct_one'] at this) b
  · exact (hFun.2.2.2.1 ⟨F₁, p₁⟩ ⟨F2, pd2⟩ hdc).1 h₁.2.2.1
  · have hZZ : ZhatL (lf D F0) F2 = U.conjTranspose * ZhatL (lf D F0) F₁ * U' := by
      funext a b
      exact hent a b
    rw [hZZ, h₁.2.2.2.2]

theorem integral_pair_of_shape (Zd : Formalism.L2.SG.TermLoc.LocDat D) {A B : PairVal.MatR D} (hA : Formalism.L2.SG.Pf.AtPt.IsLo A)
    (hB : Formalism.L2.SG.Pf.AtPt.IsUp B) (hES : Formalism.L2.SG.Pf.StabIntSh.EntryShape D A B) :
    TupGlob.IntFr A.conjTranspose ∧
      TupGlob.IntFr (Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * B * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS) ∧
      TupGlob.TieG A.conjTranspose
        (Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * B * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS) := by
  open Formalism.L2.SG.Pf.FibD in
  refine ⟨fun c b hcb x hx => ?_, fun c b hcb x hx => ?_, fun P hP c b => ?_⟩
  · rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF]
    exact mem_aaF hcb hx (ddPow_conj Zd (by have := b.isLt; omega) (hES b c hcb).1)
  · rw [sg_entry]
    exact mem_aaF hcb hx (hES b c hcb).2.1
  · rcases lt_trichotomy c b with h | h | h
    · have hq := (hES b c h).2.2
      unfold Formalism.L2.SG.Pf.StabIntSh.qdPow Formalism.L2.SG.Pf.StabIntSh.qq at hq
      rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_singleton_mul] at hq
      obtain ⟨z, hz, hzy⟩ := hq
      obtain ⟨t, ht, htP⟩ := diff_avoid P hP
      have hk : b.val - c.val ≤ D.R.rS := by have := b.isLt; omega
      have hz' := ddPow_conj Zd hk hz
      have hprod := FractionalIdeal.mul_mem_mul (mem_ddS_pow t ht (b.val - c.val)) hz'
      unfold Formalism.L2.SG.Pf.StabIntSh.ddPow at hprod
      rw [← zpow_natCast, ← zpow_add₀ (PI.NRCW.ddS_ne_zero D), add_neg_cancel, zpow_zero] at hprod
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hprod
      refine ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t) ^ (b.val - c.val), fun hs => htP (P.isPrime.mem_of_pow_mem _ hs),
        o, ?_⟩
      rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF, sg_entry]
      have e1 : D.conjF (A b c) - Formalism.L2.SG.Pf.StabIntSh.bt D B c b =
          D.conjF (algebraMap (𝓞 D.host.E) D.host.E ((gS D : ℕ) : 𝓞 D.host.E) * z) := by
        have := congrArg D.conjF hzy
        simpa only [map_sub, Formalism.L2.SG.Pf.LocalDenominators.conjF_invol] using this
      rw [e1, map_mul, map_natCast, map_natCast, mul_left_comm, ← ho]
    · subst h
      refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.1 c, hB.1 c, ← pow_add, ← two_mul, pow_mul]
    · refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.2 b c h, hB.2 b c h]

theorem ez_of_normRep {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} {γ : TermDef.Term D u u' F0 what₂}
    (hΛ : IsRowLat D F0 γ.lam) {w w₁ : Point D.host.E (D.R.rS + 1)} (hel : Formalism.L2.SG.DataCut.EligAt γ w)
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {L U : PairVal.MatR D}
    (hn : PairVal.NormRep γ w₁ F' L U) :
    F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam (ZhatL (lf D F0) F') := by
  obtain ⟨⟨p₁, e₁⟩, hadm₁, -⟩ := hn
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam hΛ
  have hFun := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam hΛ
  obtain ⟨Fa, ⟨pa, ea⟩, hGa, -⟩ := hel.2
  have hdca := (hEq ⟨Fa, pa⟩ ⟨F', p₁⟩).1 (ea.trans e₁.symm)
  obtain ⟨Fg, ⟨pg, eg⟩, hgen⟩ := hel.1.1
  refine ⟨⟨p₁.1, p₁.2.1, ?_⟩, hadm₁, ?_, p₁.2.2, rfl⟩
  · rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hdca]; exact hGa
  · exact (hFun.2.2.2.1 ⟨Fg, pg⟩ ⟨F', p₁⟩ ((hEq ⟨Fg, pg⟩ ⟨F', p₁⟩).1 (eg.trans e₁.symm))).1 hgen

theorem moveCZ {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ) (hu : Tu D u ≠ 0) (hu' : Tu D u' ≠ 0)
    (Zd : Formalism.L2.SG.TermLoc.LocDat D) {t : TermsOf D u' F0 Λ} {Z : PairVal.MatR D}
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (h' : F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z)
    (r' : TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F')
    {a' b : PairVal.MatR D} (ha : IsLoUni a') (hb : IsUpUni b) (hst : a' * ZhatOM Z * b = ZhatOM Z)
    (hES : Formalism.L2.SG.Pf.StabIntSh.EntryShape D a' b) :
    ∃ ν ∈ NLam Λ (lf D F0), ∃ m ∈ NLam Λ F',
      (∀ c, ν (frame (lf D F0) c) = ∑ d, a'.conjTranspose d c • frame (lf D F0) d) ∧
      (∀ c, m (frame F' c) = ∑ d, (Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * b * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS) d c •
        frame F' d) ∧
      ∃ F2 ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z,
        TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F2 ∧ ∀ c, frame F2 c = ν⁻¹ (m (frame F' c)) := by
  set Sg := Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS with hSg
  have hlo : Formalism.L2.SG.Pf.AtPt.IsLo a' := ⟨fun i => (ha i i).2 rfl, fun i j h => (ha i j).1 h⟩
  have hup : Formalism.L2.SG.Pf.AtPt.IsUp b := ⟨fun i => (hb i i).2 rfl, fun i j h => (hb j i).1 h⟩
  obtain ⟨hi1, hi2, htie⟩ := integral_pair_of_shape Zd hlo hup hES
  have hU : IsUpUni a'.conjTranspose := fun i j => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [Matrix.conjTranspose_apply, (ha j i).1 h, star_zero]
    · subst h; rw [Matrix.conjTranspose_apply, (ha i i).2 rfl, star_one]
  have hU' : IsUpUni (Sg * b * Sg) := fun i j => by
    rw [Formalism.L2.SG.Pf.FibD.sg_entry]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp [Formalism.L2.SG.Pf.StabIntSh.bt, (hb i j).1 h]
    · subst h
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, (hb i i).2 rfl, ← pow_add, ← two_mul, pow_mul]
  obtain ⟨ν, hν, m, hm, hνF, hmF, F2, hF2, hr2, hf2⟩ := lift_move hΛ hu hu' h' r' hU hU' hi1 hi2 htie
  refine ⟨ν, hν, m, hm, hνF, hmF, F2, ?_, hr2, hf2⟩
  have hZ : a'.conjTranspose.conjTranspose * Z * (Sg * b * Sg) = Z := by
    rw [Matrix.conjTranspose_conjTranspose]
    have hS : ZhatOM Z = Z * Sg := Formalism.L2.SG.Pf.AtPt.zhatOM_eq Z
    rw [hS] at hst
    calc a' * Z * (Sg * b * Sg) = (a' * (Z * Sg) * b) * Sg := by simp only [Matrix.mul_assoc]
      _ = Z := by rw [hst, Matrix.mul_assoc, Formalism.L2.SG.Pf.AtPt.sg_sq, Matrix.mul_one]
  rwa [hZ] at hF2

end Formalism.L2.SG.Pf.TupAct
