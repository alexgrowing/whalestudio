import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.LevSrcPt

open GlobalTheory.CplPt GlobalTheory.TopStep GlobalTheory.TopLaw

theorem exists_pt_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U)
    (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) t.m2) (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2)))
    (z : SB t μ → t.X.K),
    (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) →
    ∃ (q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) t.m2) (κP : GLQ t.X.E (D.R.N t.m2) (rowSG t.Pr t.sel (t.tup μ)))
      (c : rowSG t.Pr t.sel (t.tup μ) → t.X.Kˣ),
      (∀ P, frsF t.sel (t.tup μ) q P = frsF t.sel (t.tup μ) p P * ((κP P)⁻¹).1) ∧
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG t.m2 (A.ib t.m2 hi β)) ((t.idx μ).levQ t.m2 (A.ib t.m2 hi β)) P (κP P) (c P)) ∧
      q.deco.1.N = p.deco.1.N ∧ q.deco.1.f = p.deco.1.f ∧
      (∀ P, ((c P : t.X.Kˣ) : t.X.K) * z P = 1) ∧
      (∀ P, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det ((κP P)⁻¹).1 : t.X.Eˣ) : t.X.E) =
        rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E)) ∧
      ∀ P, InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 ((κP P)⁻¹).1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin _hTie hi β κ p g z hgz
  classical
  have hok := t.idx_ok μ
  have hpr : ∀ P, g P ∈ prCat (Pr := t.Pr) (t.cst μ).sharp t.m2 P.1 ((t.idx μ).h t.m2 (A.ib t.m2 hi β) P) :=
    fun P => (exists_midLev_iff t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 P _ (g P)).1 ⟨z P, (hgz P).1⟩
  let g' : ∀ P : SB t μ, GLint t.X.E (D.R.N t.m2) P.1 := fun P => ⟨g P, hok.int t.m2 _ P (hpr P)⟩
  obtain ⟨q, κP, hN, hf, hfr, hκ⟩ := exists_pt_frames p g'
  have hc : ∀ P, ∃ c : t.X.Kˣ, LevAt ((t.idx μ).levG t.m2 (A.ib t.m2 hi β)) ((t.idx μ).levQ t.m2 (A.ib t.m2 hi β)) P (κP P) c ∧
      (c : t.X.K) * z P = 1 := by
    intro P
    obtain ⟨r, hr, hrg, hz⟩ := (hgz P).1
    by_cases hP : P.1 ∈ t.Pr.vGs
    · have hmem : redGL _ P.1 (g' P) ∈ ((t.idx μ).levG t.m2 (A.ib t.m2 hi β) ⟨P.1, hP⟩).H :=
        (hok.grpG t.m2 _ ⟨P.1, hP⟩ _).2 ⟨g P, hpr P, fun x hx => redV_redGL (g' P) hx⟩
      have hlam := hok.chrG t.m2 _ ⟨P.1, hP⟩ ⟨_, hmem⟩ (g P) r hr hrg (fun x hx => redV_redGL (g' P) hx)
      have hred : redGL _ P.1 (κP P) = (redGL _ P.1 (g' P))⁻¹ := by
        have h1 := (hκ P).1
        rw [map_mul, map_inv (redGL _ _) (g' P), inv_mul_eq_one, map_inv] at h1
        rw [h1, inv_inv]
      have hmem' : redGL _ P.1 (κP P) ∈ ((t.idx μ).levG t.m2 (A.ib t.m2 hi β) ⟨P.1, hP⟩).H := hred ▸ inv_mem hmem
      refine ⟨((t.idx μ).levG t.m2 (A.ib t.m2 hi β) ⟨P.1, hP⟩).lam ⟨_, hmem'⟩, ⟨fun _ => ⟨hmem', rfl⟩, fun _ hP' => absurd hP hP'⟩, ?_⟩
      have e : (⟨_, hmem'⟩ : ↥((t.idx μ).levG t.m2 (A.ib t.m2 hi β) ⟨P.1, hP⟩).H) = (⟨_, hmem⟩)⁻¹ := Subtype.ext hred
      have ez : z P = ((((t.idx μ).levG t.m2 (A.ib t.m2 hi β) ⟨P.1, hP⟩).lam ⟨_, hmem⟩ : t.X.Kˣ) : t.X.K) := hz.trans hlam.symm
      rw [e, map_inv, ez]
      exact Units.inv_mul _
    · have hQ : P.1 ∈ QE t.sel ((t.tup μ) : Chr t.X.F t.X.E t.X.K) := (Finset.mem_union.mp P.2).resolve_left hP
      have hmem : g' P ∈ ((t.idx μ).levQ t.m2 (A.ib t.m2 hi β) ⟨P.1, hQ⟩).H := by
        rw [hok.grpQ]
        exact Subgroup.mem_subgroupOf.2 (hpr P)
      have hlam := hok.chrQ t.m2 _ ⟨P.1, hQ⟩ ⟨g' P, hmem⟩ r hr hrg
      have hκe : κP P = (g' P)⁻¹ := by rw [← (hκ P).2 hP, inv_inv]
      have hmem' : κP P ∈ ((t.idx μ).levQ t.m2 (A.ib t.m2 hi β) ⟨P.1, hQ⟩).H := hκe ▸ inv_mem hmem
      refine ⟨((t.idx μ).levQ t.m2 (A.ib t.m2 hi β) ⟨P.1, hQ⟩).lam ⟨_, hmem'⟩, ⟨fun hP' => absurd hP' hP, fun _ _ => ⟨hmem', rfl⟩⟩, ?_⟩
      have e : (⟨_, hmem'⟩ : ↥((t.idx μ).levQ t.m2 (A.ib t.m2 hi β) ⟨P.1, hQ⟩).H) = (⟨_, hmem⟩)⁻¹ := Subtype.ext hκe
      have ez : z P = ((((t.idx μ).levQ t.m2 (A.ib t.m2 hi β) ⟨P.1, hQ⟩).lam ⟨_, hmem⟩ : t.X.Kˣ) : t.X.K) := hz.trans hlam.symm
      rw [e, map_inv, ez]
      exact Units.inv_mul _
  choose c hc using hc
  refine ⟨q, κP, c, hfr, fun P => (hc P).1, hN, hf, fun P => (hc P).2, fun P => ?_, fun P => ?_⟩
  · by_cases hP : P.1 ∈ t.Pr.vGs
    · have h1 := (hκ P).1
      rw [map_mul, map_inv (redGL _ _) (g' P), inv_mul_eq_one] at h1
      unfold rhoS
      refine unitV_congr _ ((det_glint ((κP P)⁻¹)).2.trans (Eq.trans ?_ (det_glint (g' P)).2.symm))
      rw [← redGL_val, ← redGL_val, h1]
    · rw [(hκ P).2 hP]
  · by_cases hP : P.1 ∈ t.Pr.vGs
    · have hD : (t.cst μ).D P = 1 := hok.depthG P hP
      have hq := (GlobalTheory.ColPeriod.levelPrimes t.X t.Pr t.sel t.S (t.tup μ) hPin.fields.ok t.pr_ok hPin.sel P).1.2
      have e : ((κP P)⁻¹).1 = (g' P).1 * ((g' P)⁻¹ * (κP P)⁻¹).1 := by
        rw [← Subgroup.coe_mul, mul_inv_cancel_left]
      unfold InFrame
      rw [e, map_mul]
      refine nearAt_mul _ (hgz P).2 ?_
      rw [hD]
      exact congAt_one_of_redGL t.seam hq ((g' P)⁻¹ * (κP P)⁻¹) (hκ P).1
    · rw [(hκ P).2 hP]
      exact (hgz P).2

end GlobalTheory.LevSrcPt
