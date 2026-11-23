import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Formalism.LocalToGlobal.Columns.ChainTopTilQK

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open GlobalTheory.TopStep GlobalTheory.TopLaw

noncomputable section

namespace GlobalTheory.RatEntry

theorem unitV_det_red_one {X : Fields} {n : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (χ : (𝓞 X.E ⧸ P.asIdeal)ˣ →* X.Kˣ)
    (k : GLint X.E n P) (hk : redGL n P k = 1) : LocE.unitV χ ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1 :=
  tqk_unitV_one χ (by rw [(det_glint k).2, ← redGL_val, hk, Units.val_one, Matrix.det_one])

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem red_pass_one {u : Pr.Word} {j : ℕ} {Λ : LevFam X.E X.K (R.N j) Pr.vGs} {Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))}
    (g : UF X.E (R.N j)) (p : ChPt (R := R) sel mu u j) (κ : GLQ X.E (R.N j) (rowSG Pr sel mu))
    (hκ : ∀ P, frsF sel mu (((g, 1, 1) : FrmG Λ Θ) • p) P = g.1 * (frsF sel mu p P * ((κ P)⁻¹).1)) (P : rowSG Pr sel mu) :
    redGL (R.N j) P.1 (κ P) = 1 := by
  classical
  have h := hκ P
  by_cases hP : P.1 ∈ Pr.vGs
  · have e : κ P = passG ((g, 1, 1) : FrmG Λ Θ) p ⟨P.1, hP⟩ := by
      apply Subtype.ext
      unfold frsF at h
      simp only [dif_pos hP] at h
      show (κ P).1 = ((((g, 1, 1) : FrmG Λ Θ) • p).deco.1.liftFr ⟨P.1, hP⟩)⁻¹ * g.1 * p.deco.1.liftFr ⟨P.1, hP⟩
      rw [h, Subgroup.coe_inv]
      group
    rw [e]
    exact redGL_passG ((g, 1, 1) : FrmG Λ Θ) p ⟨P.1, hP⟩
  · unfold frsF at h
    simp only [dif_neg hP] at h
    have h1 : ((κ P)⁻¹).1 = 1 := by
      have h' : g.1 * (p.fr ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ * ((κ P)⁻¹).1) =
          g.1 * (p.fr ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ * 1) := by
        rw [← h]
        show g.1 * p.fr _ * (((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 = _
        simp [mul_assoc]
      exact mul_left_cancel (mul_left_cancel h')
    have h2 : κ P = 1 := inv_eq_one.1 (Subtype.ext h1)
    rw [h2, map_one]

theorem rho_pass_one (i : ℕ) (κ : GLQ X.E (R.N i) (rowSG Pr sel mu)) (κ' : GLQ X.E (R.N (i + 1)) (rowSG Pr sel mu))
    (hκ : ∀ P : rowSG Pr sel mu, redGL (R.N i) P.1 (κ P) = 1) (hκ' : ∀ P : rowSG Pr sel mu, redGL (R.N (i + 1)) P.1 (κ' P) = 1) :
    ∏ P : rowSG Pr sel mu, (rhoS Ch sel mu i P ((LinearEquiv.det (κ⁻¹ P).1 : X.Eˣ) : X.E) *
      rhoT Ch sel mu i P ((LinearEquiv.det (κ'⁻¹ P).1 : X.Eˣ) : X.E)) = 1 := by
  refine Finset.prod_eq_one fun P _ => ?_
  have h1 : redGL _ P.1 ((κ P)⁻¹) = 1 := by rw [map_inv, hκ P, inv_one]
  have h2 : redGL _ P.1 ((κ' P)⁻¹) = 1 := by rw [map_inv, hκ' P, inv_one]
  rw [Pi.inv_apply, Pi.inv_apply]
  unfold rhoS rhoT
  rw [unitV_det_red_one _ ((κ P)⁻¹) h1, unitV_det_red_one _ ((κ' P)⁻¹) h2, mul_one]

theorem xiEntry_rat {u : Pr.Word} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S ∧ ∀ k, Pr.g k ∈ S)
    (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1))
    (g : UF X.E (R.N i)) (g' : UF X.E (R.N (i + 1))) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiEntry Ch sel mu cst L i al be
        (((g, 1, 1) : UF X.E (R.N i) × GLG X.E (R.N i) Pr.vGs × GLQ X.E (R.N i) (QE sel (mu : Chr X.F X.E X.K))) • p)
        (((g', 1, 1) : UF X.E (R.N (i + 1)) × GLG X.E (R.N (i + 1)) Pr.vGs × GLQ X.E (R.N (i + 1)) (QE sel (mu : Chr X.F X.E X.K))) • p')
        (g'.1.toLinearMap ∘ₗ x ∘ₗ g.1.symm.toLinearMap) = XiEntry Ch sel mu cst L i al be p p' x := by
  have hd := (tilOk_of_avoid (mu := mu) hPr hsel u hS).2.2
  have e1 : (((g, 1, 1) : UF X.E (R.N i) × GLG X.E (R.N i) Pr.vGs × GLQ X.E (R.N i) (QE sel (mu : Chr X.F X.E X.K))) • p) =
      ((g, 1, 1) : FrmG (L.levG i al) (L.levQ i al)) • p := rfl
  have e2 : (((g', 1, 1) : UF X.E (R.N (i + 1)) × GLG X.E (R.N (i + 1)) Pr.vGs × GLQ X.E (R.N (i + 1)) (QE sel (mu : Chr X.F X.E X.K))) • p') =
      ((g', 1, 1) : FrmG (L.levG (i + 1) be) (L.levQ (i + 1) be)) • p' := rfl
  rw [e1, e2]
  obtain ⟨κ, c, hκ, hc, ec⟩ := exists_pass hd ((g, 1, 1) : FrmG (L.levG i al) (L.levQ i al)) p
  obtain ⟨κ', c', hκ', hc', ec'⟩ := exists_pass hd ((g', 1, 1) : FrmG (L.levG (i + 1) be) (L.levQ (i + 1) be)) p'
  have key := GlobalTheory.MatLaw.xiEntry_law hX hPr hsel hL hi hκ hκ' hc hc' x (phiT_act _ _ _ _ _ _ _)
  rw [rho_pass_one i κ κ' (red_pass_one g p κ hκ) (red_pass_one g' p' κ' hκ'), mul_one, ec, ec'] at key
  rw [key]
  simp

end GlobalTheory.RatEntry

namespace GlobalTheory.RatEntry

theorem xiPt_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), i < t.m2 → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG t.X.E (D.R.N (i + 1)) t.Pr.vGs × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _hT i hi hlt β β' x x' p p' _hp _hp' g g' w
  unfold xiPt
  rw [dif_pos hlt, dif_pos hlt]
  exact GlobalTheory.RatEntry.xiEntry_rat hP.fields.ok t.pr_ok hP.sel ⟨hP.avoid.2, hP.avoid.1⟩ (t.idx_ok μ) hlt _ _ g g' p p' w

end GlobalTheory.RatEntry
