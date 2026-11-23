import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtFormOfMemStdAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawK1DepthTwiceM
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Formalism.LocalToGlobal.Columns.ChainTwAn
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.TopStep GlobalTheory.TopLaw

namespace GlobalTheory.TopFrameQ

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem cong_scaled {n : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) {D M : ℕ} (hMD : M ≤ D)
    (hκ : ∀ w ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ w - w) ∈ stdAt E n P)
    {v : Sp E n} (hv : ((qOf P : E) ^ M) • v ∈ stdAt E n P) :
    ((qOf P : E) ^ (D - M))⁻¹ • (κ v - v) ∈ stdAt E n P := by
  have hq : (qOf P : E) ≠ 0 := qOf_ne_zero
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMD
  have h := hκ _ hv
  rw [map_smul, ← smul_sub, smul_smul] at h
  rw [Nat.add_sub_cancel_left]
  convert h using 2
  rw [pow_add]
  field_simp

theorem cong_symm {n : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P) {D : ℕ}
    (h : ∀ w ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ w - w) ∈ stdAt E n P) :
    ∀ w ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ.symm w - w) ∈ stdAt E n P := by
  intro w hw
  have hu : κ.symm w ∈ stdAt E n P := glint_mem (⟨κ, hκ⟩⁻¹ : GLint E n P) hw
  have := neg_mem (h _ hu)
  rw [LinearEquiv.apply_symm_apply, ← smul_neg, neg_sub] at this
  exact this

def abelian₂ (P : HeightOneSpectrum (𝓞 E)) (n M : ℕ) (v : Sp E n) : Prop :=
  (∀ l, IntAt P ((qOf P : E) ^ M * v l)) ∧ ∀ l : Fin n, l.1 + 1 < n → IntAt P (v l)

theorem abelian₂.smul_mem {n M : ℕ} {v : Sp E n} (h : abelian₂ P n M v) : ((qOf P : E) ^ M) • v ∈ stdAt E n P :=
  mem_stdAt.2 fun l => by simpa only [Pi.smul_apply, smul_eq_mul] using h.1 l

theorem abelian₂.move {n M D : ℕ} {b : Sp E n ≃ₗ[E] Sp E n} (hb : b ∈ GLint E n P)
    (hbc : ∀ w ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (b w - w) ∈ stdAt E n P) (hMD : M + 1 ≤ D)
    {v : Sp E n} (hv : abelian₂ P n M v) :
    abelian₂ P n M (b v) ∧ ((qOf P : E) ^ (D - M))⁻¹ • (b v - v) ∈ stdAt E n P := by
  have hq : (qOf P : E) ≠ 0 := qOf_ne_zero
  have hd := cong_scaled b (by omega) hbc hv.smul_mem
  refine ⟨⟨fun l => ?_, fun l hl => ?_⟩, hd⟩
  · have h1 := mem_stdAt.1 (glint_mem (⟨b, hb⟩ : GLint E n P) hv.smul_mem) l
    rw [show ((⟨b, hb⟩ : GLint E n P) : Sp E n ≃ₗ[E] Sp E n) = b from rfl, map_smul] at h1
    simpa only [Pi.smul_apply, smul_eq_mul] using h1
  · have h2 := mem_stdAt.1 hd l
    have h3 : IntAt P ((qOf P : E) ^ (D - M)) := intAt_pow (GlobalTheory.TopStep.intAt_nat _) _
    have h4 := (h3.mul h2).add (hv.2 l hl)
    convert h4 using 1
    rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul, Pi.sub_apply]
    ring

theorem abelian₂.of_basis {n n' M : ℕ} (y : HomE E n' n) (hy : ∀ j, abelian₂ P n M (y (Pi.single j 1)))
    {v : Sp E n'} (hv : v ∈ stdAt E n' P) : abelian₂ P n M (y v) := by
  refine ⟨fun l => ?_, fun l hl => ?_⟩
  · exact intAt_form_of_mem_stdAt ((qOf P : E) ^ M) (LinearMap.proj l ∘ₗ y) (fun i => (hy i).1 l) hv
  · have := intAt_form_of_mem_stdAt (1 : E) (LinearMap.proj l ∘ₗ y)
      (fun i => by rw [one_mul]; exact (hy i).2 l hl) hv
    rw [one_mul] at this
    exact this

end Local

end GlobalTheory.TopFrameQ

namespace GlobalTheory.TopFrameQ

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu))

theorem k_le_N (i : ℕ) : R.k ≤ R.N i := by
  unfold Ranks.N; omega

theorem k_le_N_pred (i : ℕ) : R.k ≤ R.N (i + 1) - 1 := by
  have h : 1 ≤ (i + 1) * (R.t + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold Ranks.N
  generalize (i + 1) * (R.t + 1) = a at *
  omega

theorem lam_of_topDat_ne (i : ℕ) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (y : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i))
    (h : topDat Ch sel mu cst i P y y'' ≠ 0) :
    ∀ j, abelian₂ P.1 (R.N (i + 1)) cst.M (y (Pi.single j 1)) := by
  unfold topDat at h
  have hne := left_ne_zero_of_mul h
  have hne2 := right_ne_zero_of_mul h
  unfold PhiTopG at hne
  rw [if_neg hP] at hne
  have hint := twAn_phiQ_int _ _ (k_le_N i) (k_le_N_pred i) _ hne
  unfold ftY at hne2
  rw [if_neg hP] at hne2
  have hlast : ∀ i', IntAt P.1 ((qOf P.1 : X.E) ^ cst.M *
      (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) ∘ₗ y) (Pi.single i' 1)) := by
    by_contra hc
    exact hne2 (if_neg hc)
  intro j
  have hpre : ∀ l : Fin (R.N (i + 1)), l.1 + 1 < R.N (i + 1) → IntAt P.1 (y (Pi.single j 1) l) := by
    intro l hl
    have := hint (Fin.castAdd _ j) ⟨l.1, by omega⟩
    have e : (LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R i)) (Pi.single (Fin.castAdd (cOf R i) j) (1 : X.E)) :
        Sp X.E (R.N i)) = Pi.single j 1 := by
      ext a
      simp [LinearMap.funLeft_apply, Pi.single_apply]
    simp only [LinearMap.comp_apply, e] at this
    exact this
  refine ⟨fun l => ?_, hpre⟩
  by_cases hl : l.1 + 1 < R.N (i + 1)
  · exact (intAt_pow (GlobalTheory.TopStep.intAt_nat _) _).mul (hpre l hl)
  · have hN : R.N (i + 1) - 1 < R.N (i + 1) := by omega
    have := hlast j
    have e : l = ⟨R.N (i + 1) - 1, hN⟩ := Fin.ext (by show l.1 = R.N (i + 1) - 1; omega)
    simp only [LinearMap.comp_apply, atNL, dif_pos hN, LinearMap.proj_apply] at this
    rw [e]
    exact this

end Chain

end GlobalTheory.TopFrameQ

namespace GlobalTheory.TopFrameQ

section Move

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem lam_comp {n' n M D : ℕ} {a : Sp E n' ≃ₗ[E] Sp E n'} {b : Sp E n ≃ₗ[E] Sp E n}
    (ha : a ∈ GLint E n' P) (hb : b ∈ GLint E n P)
    (hbc : ∀ w ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (b w - w) ∈ stdAt E n P)
    (hMD : M + 1 ≤ D) (y : HomE E n' n) (hy : ∀ j, abelian₂ P n M (y (Pi.single j 1))) :
    ∀ j, abelian₂ P n M ((b.toLinearMap ∘ₗ y ∘ₗ a.toLinearMap) (Pi.single j 1)) := fun j =>
  (abelian₂.move hb hbc hMD (abelian₂.of_basis y hy (glint_mem (⟨a, ha⟩ : GLint E n' P) (single_mem_stdAt P j)))).1

theorem intAt_inv_pow_le {a b : ℕ} (h : a ≤ b) {z : E} (hz : IntAt P (((qOf P : E) ^ b)⁻¹ * z)) :
    IntAt P (z / (qOf P : E) ^ a) := by
  rw [inv_mul_eq_div] at hz
  exact GlobalTheory.TopInv.intAt_div_pow_le qOf_ne_zero h hz

end Move

end GlobalTheory.TopFrameQ

namespace GlobalTheory.TopFrameQ

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu))

theorem topDat_frames {m2 : ℕ} (hm : R.m = m2 + 2) (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hD : 2 * cst.M ≤ cst.D P)
    (κ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (κ' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1)))
    (hκ : κ ∈ GLint X.E _ P.1)
    (hκc : ∀ w ∈ stdAt X.E _ P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E _ P.1)
    (hκ' : κ' ∈ GLint X.E _ P.1)
    (hκ'c : ∀ w ∈ stdAt X.E _ P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ' w - w) ∈ stdAt X.E _ P.1)
    (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y'' : Sp X.E (R.N (m2 + 1)))
    (hy'' : ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y'' l)) :
    topDat Ch sel mu cst (m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
      topDat Ch sel mu cst (m2 + 1) P y y'' := by
  have hM1 : 1 ≤ cst.M := hc.M_pos
  have hMD : cst.M + 1 ≤ cst.D P := by omega
  have hq : (qOf P.1 : X.E) ≠ 0 := qOf_ne_zero
  have hκ's : κ'.symm ∈ GLint X.E _ P.1 := (GLint X.E _ P.1).inv_mem hκ'
  have hκs : κ.symm ∈ GLint X.E _ P.1 := (GLint X.E _ P.1).inv_mem hκ
  have hκ'sc := cong_symm hκ' hκ'c
  by_cases hg : ∀ j, abelian₂ P.1 (R.N (m2 + 1 + 1)) cst.M (y (Pi.single j 1))
  · unfold topDat
    congr 1
    · unfold PhiTopG
      rw [if_neg hP]
      have hc0 : cOf R (m2 + 1) = 0 := cOf_topB hm
      have hw : ∀ w ∈ stdAt X.E (R.N (m2 + 1)) P.1, ∀ l : Fin (R.N (m2 + 1 + 1)), l.1 + 1 < R.N (m2 + 1 + 1) →
          IntAt P.1 ((κ'.symm (y (κ w)) - y w) l / (qOf P.1 : X.E)) := by
        intro w hw l hl
        have hu := abelian₂.of_basis y hg (glint_mem (⟨κ, hκ⟩ : GLint X.E _ P.1) hw)
        have d1 := mem_stdAt.1 (abelian₂.move hκ's hκ'sc hMD hu).2 l
        have e1 := intAt_inv_pow_le (a := 1) (by omega) d1
        have hu' : ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E _ P.1 := hκc w hw
        have hyu := (abelian₂.of_basis y hg hu').2 l hl
        rw [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at hyu
        have e2 := intAt_inv_pow_le (a := 1) (by omega) hyu
        rw [pow_one] at e1 e2
        have e3 := e1.add e2
        rw [← add_div] at e3
        convert e3 using 2
        simp only [Pi.sub_apply]
        ring
      have key := fun z hz => GlobalTheory.TopInv.PhiQ_add (K := X.K) (GlobalTheory.TopInv.qOf_mem P.1) hq
        (resChar (mu : Chr X.F X.E X.K) P.1) R.k R.r (cOf R (m2 + 1)) (R.N (m2 + 1)) (R.N (m2 + 1 + 1) - 1) hc0
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) z hz
      refine (congrArg _ (add_sub_cancel _ _)).symm.trans (key _ ?_)
      intro s l
      have hws : (LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Pi.single s (1 : X.E)) : Sp X.E _) ∈
          stdAt X.E (R.N (m2 + 1)) P.1 :=
        mem_stdAt.2 fun a => GlobalTheory.TopInv.single_int s (Fin.castAdd _ a)
      have := hw _ hws ⟨l.1, by omega⟩ (by show l.1 + 1 < _; omega)
      exact this
    · have h1 := ftY_comp_glint sel mu cst hc P (fun _ => hD) ⟨κ, hκ⟩
          (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.symm.toLinearMap ∘ₗ y) y'' (κ.symm y'')
          (fun h => absurd h hP) (fun _ => hy'') (fun h => absurd h hP)
          (fun _ => by
            show ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ (κ.symm y'') - y'') ∈ _
            rw [LinearEquiv.apply_symm_apply, sub_self, smul_zero]
            exact zero_mem _)
      refine h1.trans ?_
      have hy''s : ((qOf P.1 : X.E) ^ cst.M) • y'' ∈ stdAt X.E _ P.1 :=
        mem_stdAt.2 fun l => by simpa only [Pi.smul_apply, smul_eq_mul] using hy'' l
      have hδ : ∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ *
          ((atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.symm.toLinearMap ∘ₗ y) -
            atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) (Pi.single i 1)) := by
        intro i
        have d1 := mem_stdAt.1 (abelian₂.move hκ's hκ'sc (v := y (Pi.single i 1)) hMD (hg i)).2
        have e1 : ∀ l, IntAt P.1 ((κ'.symm (y (Pi.single i 1)) - y (Pi.single i 1)) l / (qOf P.1 : X.E) ^ cst.M) :=
          fun l => intAt_inv_pow_le (by omega) (d1 l)
        have e2 := GlobalTheory.TopInv.atNL_int (R.N (m2 + 1 + 1) - 1) _ _ e1
        rw [inv_mul_eq_div]
        convert e2 using 2
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
        rfl
      have h2 := GlobalTheory.ftY_pert_qM sel mu cst hc P hP hD (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y)
        _ y'' hδ hy''s
      rw [add_sub_cancel] at h2
      exact h2
  · have h0 : topDat Ch sel mu cst (m2 + 1) P y y'' = 0 := by
      by_contra hne
      exact hg (lam_of_topDat_ne Ch sel mu cst _ P hP y y'' hne)
    rw [h0]
    by_contra hne
    apply hg
    have h1 := lam_of_topDat_ne Ch sel mu cst _ P hP _ _ hne
    have h2 := lam_comp hκs hκ' hκ'c hMD _ h1
    intro j
    have := h2 j
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using this

end Main

end GlobalTheory.TopFrameQ

namespace GlobalTheory.TopFrameQ

theorem topDat_frames_tie : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (P : SB t μ), P.1 ∉ t.Pr.vGs →
  ∀ (κ : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))
    (κ' : Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1))),
  κ ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ w - w) ∈ stdAt t.X.E _ P.1) →
  κ' ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ' w - w) ∈ stdAt t.X.E _ P.1) →
  ∀ (y : HomE t.X.E (D.R.N (t.m2 + 1)) (D.R.N (t.m2 + 1 + 1))) (y'' : Sp t.X.E (D.R.N (t.m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * y'' l)) →
  topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'') := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ P hP κ κ' hκ hκc hκ' hκ'c y y'' hy''
  exact topDat_frames t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx_ok μ).hm (t.idx_ok μ).cst_ok P hP
    ((t.idx_ok μ).depthQ P hP) κ κ' hκ hκc hκ' hκ'c y y'' hy''

end GlobalTheory.TopFrameQ
