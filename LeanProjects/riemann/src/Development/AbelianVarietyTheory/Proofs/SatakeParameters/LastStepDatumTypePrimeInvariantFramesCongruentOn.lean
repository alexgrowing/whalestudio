import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtFormOfMemStdAt
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.AwayTopG

open GlobalTheory.TopStep GlobalTheory.LastSteps GlobalTheory.TopLaw

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem hom_mem_stdAt {n m : ℕ} (f : HomE E n m) (hf : ∀ j l, IntAt P (f (Pi.single j 1) l)) {v : Sp E n}
    (hv : v ∈ stdAt E n P) : f v ∈ stdAt E m P :=
  mem_stdAt.2 fun l => by
    have h := intAt_form_of_mem_stdAt (1 : E) (LinearMap.proj l ∘ₗ f) (fun i => by simpa using hf i l) hv
    simpa using h

theorem symm_mem_stdAt {n : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P) {w : Sp E n} (hw : w ∈ stdAt E n P) :
    κ.symm w ∈ stdAt E n P :=
  (hκ (κ.symm w)).1 (by rw [LinearEquiv.apply_symm_apply]; exact hw)

theorem symm_near {n D : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P)
    (hD : ∀ w ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ w - w) ∈ stdAt E n P) {w : Sp E n} (hw : w ∈ stdAt E n P) :
    ((qOf P : E) ^ D)⁻¹ • (κ.symm w - w) ∈ stdAt E n P := by
  have h := hD _ (symm_mem_stdAt hκ hw)
  rw [LinearEquiv.apply_symm_apply] at h
  have e : ((qOf P : E) ^ D)⁻¹ • (κ.symm w - w) = -(((qOf P : E) ^ D)⁻¹ • (w - κ.symm w)) := by
    rw [← smul_neg, neg_sub]
  rw [e]
  exact Submodule.neg_mem _ h

end SlopeTestRemainingChoices

theorem topDat_frames_vGs : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs →
  ∀ (κ : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))
    (κ' : Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1))),
  κ ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ w - w) ∈ stdAt t.X.E _ P.1) →
  κ' ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ' w - w) ∈ stdAt t.X.E _ P.1) →
  ∀ (y : HomE t.X.E (D.R.N (t.m2 + 1)) (D.R.N (t.m2 + 1 + 1))) (y'' : Sp t.X.E (D.R.N (t.m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y'' l)) →
  topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'') := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie P hP κ κ' hκ hκD hκ' hκ'D y y'' hy''
  have hok := t.idx_ok μ
  have hc := hok.cst_ok
  have hn : TopNum D.R (t.m2 + 1) := topNum_of (m_eq t μ)
  have hX : t.X.Ok := hPin.fields.ok
  have hPr := t.pr_ok
  have hq0 : (qOf P.1 : t.X.E) ≠ 0 := qOf_ne_zero
  obtain ⟨d, hd⟩ : ∃ d, (t.cst μ).D P = d + 1 := ⟨(t.cst μ).D P - 1, by have := hc.D_pos P; omega⟩
  by_cases hI : ∀ j l, IntAt P.1 (y (Pi.single j 1) l)
  ·
    have hA : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
        topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y (κ.symm y'') := by
      refine topDat_congr t.Ch t.sel (t.tup μ) (t.cst μ) hX hPr hc hn P hP _ _ _ ?_ ?_
      · have h1 : κ.symm ((qOf P.1 : t.X.E) • y'') ∈ stdAt t.X.E _ P.1 := symm_mem_stdAt hκ (mem_stdAt.2 hy'')
        rw [map_smul] at h1
        intro j
        simpa using mem_stdAt.1 h1 j
      · intro j
        have hkj : κ (Pi.single j 1) ∈ stdAt t.X.E _ P.1 := (hκ _).2 (single_mem_stdAt j)
        have hv : y (κ (Pi.single j 1)) ∈ stdAt t.X.E _ P.1 := hom_mem_stdAt y hI hkj
        have hz : κ'.symm (y (κ (Pi.single j 1))) ∈ stdAt t.X.E _ P.1 := symm_mem_stdAt hκ' hv
        have hzI : ∀ l, IntAt P.1 ((κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (Pi.single j 1) l) := fun l => mem_stdAt.1 hz l
        refine ⟨iff_of_true hzI (hI j), fun _ l => ?_⟩
        set s := ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ (Pi.single j 1) - Pi.single j 1) with hs
        set s' := ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ'.symm (y (κ (Pi.single j 1))) - y (κ (Pi.single j 1))) with hs'
        have hsI : s ∈ stdAt t.X.E _ P.1 := hκD _ (single_mem_stdAt j)
        have hs'I : s' ∈ stdAt t.X.E _ P.1 := symm_near hκ' hκ'D hv
        have hys : IntAt P.1 (y s l) := mem_stdAt.1 (hom_mem_stdAt y hI hsI) l
        have e1 : y s l = ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (y (κ (Pi.single j 1)) l - y (Pi.single j 1) l) := by
          rw [hs, map_smul, map_sub]
          rfl
        have e2 : s' l = ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (κ'.symm (y (κ (Pi.single j 1))) l - y (κ (Pi.single j 1)) l) := by
          rw [hs']
          rfl
        have key : (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (Pi.single j 1) l =
            y (Pi.single j 1) l + (qOf P.1 : t.X.E) * ((qOf P.1 : t.X.E) ^ d * (y s l + s' l)) := by
          rw [e1, e2, hd]
          show κ'.symm (y (κ (Pi.single j 1))) l = _
          field_simp
          ring
        rw [key, redP_add_q ((intAt_pow (intAt_nat _) d).mul (hys.add (mem_stdAt.1 hs'I l)))]
    have hB : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y (κ.symm y'') =
        topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'' := by
      unfold topDat
      congr 1
      have hw : (qOf P.1 : t.X.E) • y'' ∈ stdAt t.X.E _ P.1 := mem_stdAt.2 hy''
      have hsw := symm_near hκ hκD hw
      have hdiff : κ.symm y'' - y'' ∈ stdAt t.X.E _ P.1 := by
        refine mem_stdAt.2 fun i => ?_
        have hi := mem_stdAt.1 hsw i
        have e : (κ.symm y'' - y'') i = (qOf P.1 : t.X.E) ^ d *
            ((((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ.symm ((qOf P.1 : t.X.E) • y'') - (qOf P.1 : t.X.E) • y'')) i) := by
          rw [map_smul, hd]
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          field_simp
          ring
        rw [e]
        exact (intAt_pow (intAt_nat _) d).mul hi
      have h := ftY_comp_glint t.sel (t.tup μ) (t.cst μ) hc P (fun h => absurd hP h) (κ := 1)
        (atNL t.X.E (D.R.N (t.m2 + 1 + 1)) (D.R.N (t.m2 + 1 + 1) - 1) ∘ₗ y) y'' (κ.symm y'')
        (fun _ => hy'') (fun h => absurd hP h) (fun _ => hdiff) (fun h => absurd hP h)
      exact h
    exact hA.trans hB
  ·
    push_neg at hI
    obtain ⟨j, l, hjl⟩ := hI
    have h0 : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'' = 0 := by
      by_contra h
      exact hjl (topDat_int t.Ch t.sel (t.tup μ) (t.cst μ) hn P hP y y'' h j l)
    have h1 : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') = 0 := by
      by_contra h
      have hzI := topDat_int t.Ch t.sel (t.tup μ) (t.cst μ) hn P hP _ _ h
      apply hjl
      have hm : (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm (Pi.single j 1)) ∈ stdAt t.X.E _ P.1 :=
        hom_mem_stdAt _ hzI (symm_mem_stdAt hκ (single_mem_stdAt j))
      have e : (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm (Pi.single j 1)) = κ'.symm (y (Pi.single j 1)) := by
        simp
      rw [e] at hm
      have hm' := (hκ' _).2 hm
      rw [LinearEquiv.apply_symm_apply] at hm'
      exact mem_stdAt.1 hm' l
    rw [h0, h1]

end GlobalTheory.TwV.AwayTopG

end
