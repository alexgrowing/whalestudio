import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GeneratorChange
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowLatOfMove
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLocInB

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.BBTie Formalism.L2.SG.Pf.GeneratorChange

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cmat

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

def uFi (b : Fin (D.R.rS + 1)) : (D.s.atP p).Ep := (((uF_unit Zd p b).unit⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep)

theorem uFi_mul (b : Fin (D.R.rS + 1)) : uFi Zd p b * uF Zd p b = 1 :=
  IsUnit.val_inv_mul (uF_unit Zd p b)

theorem mul_uFi (b : Fin (D.R.rS + 1)) : uF Zd p b * uFi Zd p b = 1 := by
  rw [mul_comm]; exact uFi_mul Zd p b

def Cm (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.diagonal (uFi Zd p) * ξ.map (fun x => (D.s.atP p).ιE (x : D.host.E)) * Matrix.diagonal (uF Zd p)

theorem Cm_apply (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) (c b : Fin (D.R.rS + 1)) :
    Cm Zd p ξ c b = uFi Zd p c * (D.s.atP p).ιE (ξ c b : D.host.E) * uF Zd p b := by
  simp [Cm, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem Cm_mul (ξ η : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) :
    Cm Zd p ξ * Cm Zd p η = Cm Zd p (ξ * η) := by
  ext c b
  rw [Matrix.mul_apply, Cm_apply, Matrix.mul_apply]
  simp only [Cm_apply]
  push_cast
  rw [map_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  have := uFi_mul Zd p d
  rw [map_mul]
  linear_combination (uFi Zd p c * (D.s.atP p).ιE (ξ c d : D.host.E) * (D.s.atP p).ιE (η d b : D.host.E) *
    uF Zd p b) * this

theorem Cm_one : Cm Zd p 1 = 1 := by
  ext c b
  rw [Cm_apply]
  by_cases h : c = b
  · subst h; simp [uFi_mul, mul_uFi]
  · simp [Matrix.one_apply_ne h]

theorem comb_Cm {T' : D.host.E} (F' : LFlag (VS D) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) (b : Fin (D.R.rS + 1)) :
    comb (Cm Zd p ξ) (locF' Zd p F') b = uF Zd p b • baseChange₂ D p (frameAct (frame F') ξ b) := by
  simp only [comb, Cm_apply, locF'_eq, frameAct]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, smul_smul, smul_smul]
  congr 1
  have := uFi_mul Zd p c
  linear_combination ((D.s.atP p).ιE (ξ c b : D.host.E) * uF Zd p b) * this

end Cmat

section admitted

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem ratio_mem (c b : Fin (D.R.rS + 1)) (h : c ≤ b) : uFi Zd p c * uF Zd p b ∈ (Zd.M p).L.O := by
  obtain ⟨k, hk, hkb⟩ := bt_frFac_step Zd p (Formalism.L2.SG.Pf.locDiffC_holds D Zd) c b h
  have h1 := uFi_mul Zd p c
  have h2 := sgnP'_sq p c
  have e : uFi Zd p c * uF Zd p b = sgnP' D p b * k * sgnP' D p c := by
    unfold uF at h1 ⊢
    rw [hkb]
    linear_combination (sgnP' D p b * k * sgnP' D p c) * h1 -
      (sgnP' D p b * k * uFi Zd p c * frFac Zd.δ p c) * h2
  rw [e]
  exact Subring.mul_mem _ (Subring.mul_mem _ (bt_sq_one_mem Zd p (sgnP'_sq p b)) hk)
    (bt_sq_one_mem Zd p (sgnP'_sq p c))

theorem Cm_props (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h0 : ∀ a b, b < a → ξ a b = 0) (h1 : ∀ a, ξ a a = 1) :
    (∀ a b, b < a → Cm Zd p ξ a b = 0) ∧ (∀ a, Cm Zd p ξ a a = 1) ∧ (∀ a b, Cm Zd p ξ a b ∈ (Zd.M p).L.O) := by
  refine ⟨fun a b hab => ?_, fun a => ?_, fun a b => ?_⟩
  · rw [Cm_apply, h0 a b hab]; simp
  · rw [Cm_apply, h1 a]; simp [uFi_mul]
  · rw [Cm_apply]
    by_cases hab : b < a
    · rw [h0 a b hab]; simp
    · rw [show uFi Zd p a * (D.s.atP p).ιE (ξ a b : D.host.E) * uF Zd p b =
        (uFi Zd p a * uF Zd p b) * (D.s.atP p).ιE (ξ a b : D.host.E) by ring]
      exact Subring.mul_mem _ (ratio_mem Zd p a b (not_lt.1 hab)) (bt_iota_int Zd p _)

end admitted

section Adm2

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem typed_data (g : Loc.SplitG (Zd.M p).L) (hg : (Zd.M p).split = some g) :
    ∃ sg, (D.s.atP p).split = some sg ∧ g.q = sg.q ∧ g.e = sg.e := by
  have hagree := (Zd.agree p).2.2.2.2.2
  rcases hs : (D.s.atP p).split with _ | sg
  · rw [hg, hs] at hagree; exact hagree.elim
  · rw [hg, hs] at hagree; exact ⟨sg, rfl, hagree.2, hagree.1⟩

theorem admissible_local_term {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hR : IsRowLat D F0 Λ) (hA : IsAdmissible Λ (gS D) (lf D F0) F') (g : Loc.SplitG (Zd.M p).L)
    (hg : (Zd.M p).split = some g) :
    (locH Zd p).Admissible g (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')) := by
  have hE := Formalism.L2.SG.Pf.locEqC_holds D Zd
  have hD := Formalism.L2.SG.Pf.locDiffC_holds D Zd
  have hFix := hR.2.1
  have hΛfg : Λ.FG := hFix.1.fg
  obtain ⟨sg, hs, hgq, -⟩ := typed_data Zd p g hg
  have hin : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by rw [← D.s_split p, hs]; rfl
  have hgP : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
      P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → (gS D : 𝓞 D.host.E) ∈ P.asIdeal :=
    fun P hP => (bt_g_mem_iff p P hP).2 hin
  have hφ := bt_typed_frFac Zd hE hD p F0 Λ hΛfg hR.2.2 hFix.2.2.2 hgP
  have hO := bt_typed_O Zd hD p F0 Λ F' (Tu D u) (Tu D u') hR.2.2 sg hs hφ
  have hξ : AdmWit Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F') := by
    unfold admXi; rw [dif_pos hA]; exact hA.choose_spec
  have hMΛ := bt_typed_Mle Zd hE p F0 Λ F' hΛfg hFix.2.2.1 hξ hgP
  intro b
  have hmem : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) •
      ((locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' b - (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).f b)
        ∈ lattice₂ D Zd.M p Λ := by
    apply hMΛ
    rw [← hO, hgq]
    exact Submodule.subset_span (Or.inr ⟨b, rfl⟩)
  have e : (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' b - (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).f b =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) •
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) •
        ((locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' b - (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).f b)) := by
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ (bt_q_ne Zd p g), map_one, one_smul]
  rw [e]
  exact Submodule.subset_span ⟨_, hmem, rfl⟩

set_option maxHeartbeats 1000000 in

theorem admissible_local_partner {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hR : IsRowLat D F0 Λ) (hA1 : AdmWit Λ (gS D) (lf D F0) F' 1) (g : Loc.SplitG (Zd.M p).L)
    (hg : (Zd.M p).split = some g) :
    (locH Zd p).Admissible g ⟨lattice₂ D Zd.M p Λ, (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).f, locF' Zd p F',
      (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).T, (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).T'⟩ := by
  have hE := Formalism.L2.SG.Pf.locEqC_holds D Zd
  have hD := Formalism.L2.SG.Pf.locDiffC_holds D Zd
  have hFix := hR.2.1
  have hΛfg : Λ.FG := hFix.1.fg
  obtain ⟨sg, hs, hgq, -⟩ := typed_data Zd p g hg
  have hin : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by rw [← D.s_split p, hs]; rfl
  have hgP : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
      P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → (gS D : 𝓞 D.host.E) ∈ P.asIdeal :=
    fun P hP => (bt_g_mem_iff p P hP).2 hin
  have hφ := bt_typed_frFac Zd hE hD p F0 Λ hΛfg hR.2.2 hFix.2.2.2 hgP
  have hκ := (bt_kappa Zd p sg hs).1
  have hA : IsAdmissible Λ (gS D) (lf D F0) F' := ⟨1, hA1⟩
  have hξ : AdmWit Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F') := by
    unfold admXi; rw [dif_pos hA]; exact hA.choose_spec
  have hMΛ := bt_typed_Mle Zd hE p F0 Λ F' hΛfg hFix.2.2.1 hξ hgP
  have hXfg : (XLam Λ (lf D F0)).FG := bt_fg_le hΛfg inf_le_left
  have hEq : lattice₂ D Zd.M p (Mplus Λ (gS D) (lf D F0) F' 1) =
      lattice₂ D Zd.M p (Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')) :=
    (hE p _ _ (bt_Mplus_fg 1 hXfg) (bt_Mplus_fg _ hXfg)).2 fun P hP =>
      m_plus_independent (gS D) Λ (lf D F0) F' hFix.2.2.1 hFix.2.2.2 P (hgP P hP) 1 _ hA1 hξ
  have hss : ∀ a, sgnP' D p a = sgnP D p a := fun a => by simp only [sgnP', hs]
  have hgS0 : ((gS D : ℕ) : D.host.E) ≠ 0 := by
    have : gS D ≠ 0 := by simp [gS, (D.host.g_prime 0).ne_zero, (D.host.g_prime 1).ne_zero]
    exact_mod_cast this
  intro b
  set x : (VS D).V := ((gS D : D.host.E))⁻¹ • (frame F' b - frameAct (frame (lf D F0)) 1 b) with hxdef
  have hxM : x ∈ Mplus Λ (gS D) (lf D F0) F' 1 :=
    Submodule.subset_span (Set.mem_union_right _ ⟨b, rfl⟩)
  have hx : baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ := hMΛ (hEq ▸ Submodule.subset_span ⟨x, hxM, rfl⟩)
  have hgx : frame F' b - frame (lf D F0) b = ((gS D : ℕ) : D.host.E) • x := by
    rw [hxdef, bt_frameAct_one, smul_smul, mul_inv_cancel₀ hgS0, one_smul]
  have hsc : sgnP D p b * frFac Zd.δ p b * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) *
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E)) ∈ (Zd.M p).L.O :=
    Subring.mul_mem _ (Subring.mul_mem _ (bt_sq_one_mem Zd p (localSign_sq p b)) (hφ b).1) hκ
  have e : locF' Zd p F' b - (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).f b =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) •
        ((sgnP D p b * frFac Zd.δ p b * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) *
          (D.s.atP p).ιE ((gS D : ℕ) : D.host.E))) • baseChange₂ D p x) := by
    show (sgnP' D p b * frFac Zd.δ p b) • baseChange₂ D p (frame F' b) -
      (sgnP D p b * frFac Zd.δ p b) • baseChange₂ D p (frame (lf D F0) b) = _
    rw [hss, ← smul_sub, ← map_sub, hgx, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, smul_smul, smul_smul, hgq]
    congr 1
    have hq0 : (sg.q : (D.s.atP p).Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
    have : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
    linear_combination (-(sgnP D p b * frFac Zd.δ p b * (D.s.atP p).ιE ((gS D : ℕ) : D.host.E))) * this
  rw [e]
  exact Submodule.subset_span ⟨_, smul_mem_O Zd p hsc hx, rfl⟩

end Adm2

section Main

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem locTerm_f'_eq (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) :
    (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' =
      comb (Cm Zd p (admXi D Λ (lf D F0) F')⁻¹) (locF' Zd p F') := by
  funext b
  rw [comb_Cm]
  rfl

theorem Cm_inv_props (p : PlF D) (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h0 : ∀ a b, b < a → ξ a b = 0) (h1 : ∀ a, ξ a a = 1) :
    Cm Zd p ξ⁻¹ * Cm Zd p ξ = 1 ∧ Cm Zd p ξ * Cm Zd p ξ⁻¹ = 1 ∧
      (∀ a b, b < a → ξ⁻¹ a b = 0) ∧ (∀ a, ξ⁻¹ a a = 1) := by
  have hdet : IsUnit ξ.det := bt_unitri_det ξ h0 h1
  have hup : IsUp ξ⁻¹ := isUp_inv ⟨h1, fun a b hab => h0 b a hab⟩
  refine ⟨?_, ?_, fun a b hab => hup.2 b a hab, hup.1⟩
  · rw [Cm_mul, Matrix.nonsing_inv_mul ξ hdet, Cm_one]
  · rw [Cm_mul, Matrix.mul_nonsing_inv ξ hdet, Cm_one]

theorem genXiRev_holds : GenXiRev Zd u' F0 := by
  intro Λ F' p hR hA1 _ hgen
  set ξ := admXi D Λ (lf D F0) F' with hξdef
  have hu := admissibility_witness_unitriangular Λ (lf D F0) F'
  obtain ⟨hii, hii', hi0, hi1⟩ := Cm_inv_props Zd p ξ hu.1 hu.2
  obtain ⟨hC0, hC1, hCO⟩ := Cm_props Zd p ξ⁻¹ hi0 hi1
  obtain ⟨-, -, hCiO⟩ := Cm_props Zd p ξ hu.1 hu.2
  set t₁ : Loc.Term (Vp D p) (Zd.M p) D.R.rS := ⟨lattice₂ D Zd.M p Λ, (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).f,
    locF' Zd p F', (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).T,
    (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).T'⟩ with ht₁
  have e : locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u') = chg t₁ (comb (Cm Zd p ξ⁻¹) t₁.f') := by
    show _ = (⟨_, _, comb (Cm Zd p ξ⁻¹) (locF' Zd p F'), _, _⟩ : Loc.Term (Vp D p) (Zd.M p) D.R.rS)
    rw [← locTerm_f'_eq]
    rfl
  rw [e]
  refine gen_change (locH Zd p) t₁ (Cm Zd p ξ⁻¹) (Cm Zd p ξ) hC0 hC1 hCO hCiO hii hii' (fun g hg => ?_) hgen
  rw [← e]
  exact admissible_local_term Zd p F0 Λ F' hR ⟨1, hA1⟩ g hg

theorem genXi_holds : GenXi Zd u u' F0 what₂ := by
  intro hrows γ F' p hA1 _ hgen
  have hR := hrows.1 γ.lam γ.mem
  set ξ := admXi D γ.lam (lf D F0) F' with hξdef
  have hu := admissibility_witness_unitriangular γ.lam (lf D F0) F'
  obtain ⟨hii, hii', hi0, hi1⟩ := Cm_inv_props Zd p ξ hu.1 hu.2
  obtain ⟨-, -, hCiO⟩ := Cm_props Zd p ξ⁻¹ hi0 hi1
  obtain ⟨hC0, hC1, hCO⟩ := Cm_props Zd p ξ hu.1 hu.2
  set t₂ := locTerm Zd p γ.lam (lf D F0) F' (Tu D u) (Tu D u') with ht₂
  have e : (⟨lattice₂ D Zd.M p γ.lam, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩ :
      Loc.Term (Vp D p) (Zd.M p) D.R.rS) = chg t₂ (comb (Cm Zd p ξ) t₂.f') := by
    show _ = (⟨_, _, comb (Cm Zd p ξ) t₂.f', _, _⟩ : Loc.Term (Vp D p) (Zd.M p) D.R.rS)
    rw [ht₂, locTerm_f'_eq, comb_comb, hii, comb_one]
    rfl
  rw [e]
  refine gen_change (locH Zd p) t₂ (Cm Zd p ξ) (Cm Zd p ξ⁻¹) hC0 hC1 hCO hCiO hii' hii (fun g hg => ?_) hgen
  rw [← e]
  exact admissible_local_partner Zd p F0 γ.lam F' hR hA1 g hg

end Main

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
