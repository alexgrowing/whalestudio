import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocK
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepFinitelyManyCellsUniformProoStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubleDescentOfParity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QFinOneAt

set_option maxHeartbeats 4000000 in

theorem core {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} (hψ : IsStdChar D c.ψ (-1)) (hv : v.Is) (ht : t.Is)
    {χ : ℕ → (AE D)ˣ →* Circle} (Q' : QAt v χ) (χz : (AE D)ˣ →* Circle) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (V₁ : (t.sBF j (σ + 1) h).χV = χ j * χz) (W₁ : (t.sBF j (σ + 1) h).χW = χ j)
    (V₂ : (t.sFB j σ h).χV = χ (j + 1)) (W₂ : (t.sFB j σ h).χW = χ (j + 1) * χz)
    (ka : IsWeilDatumO c.ψ _ _ (χ j) (χ j) (t.kom j)) (kb : IsWeilDatumO c.ψ _ _ (χ (j + 1)) (χ (j + 1)) (t.kom (j + 1)))
    (a : GL (Q'.X j ⊕ Fin (2 * σ + 2 + 1)) Q'.k) :
    ∃ T : Finset (GL (Q'.X (j + 1) ⊕ Fin (2 * σ + 2)) Q'.k), ∀ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Q'.q.v) f₁ →
      ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = Q'.q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = Q'.q.v), ∀ x,
        flatBF (t.sBF j (σ + 1) h) (t.om j (g * Q'.gl j (2 * σ + 2 + 1) (by have := Q'.hs; omega) a,
          h₁ * Q'.gl (j + 1) (2 * σ + 2) (by have := Q'.hs; omega) x) (comb c.ψ _ _ (Q'.eL j) f₁)) ≠ 0 →
        ∃ τ ∈ T, ∃ r, Q'.gl (j + 1) (2 * σ + 2) (by have := Q'.hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧
          ∃ κ ∈ (Q'.T.lev (j + 1) (2 * σ + 2) (by have := Q'.hs; omega)).J, x = r * τ * κ := by
  classical
  haveI := Q'.unitVol.1
  have e0 : j + (2 * σ + 2 + 1) = Q'.s + 1 := by have := Q'.hs; omega
  have e1 : j + 1 + (2 * σ + 2) = Q'.s + 1 := by have := Q'.hs; omega
  have e2 : j + 1 + 1 + (2 * σ + 1) = Q'.s + 1 := by have := Q'.hs; omega
  have e01 : j + (2 * σ + 2) = Q'.s := by have := Q'.hs; omega
  have e12 : j + 1 + (2 * σ + 1) = Q'.s := by have := Q'.hs; omega
  let S : Dbl2 c.ψ σ :=
    { B := c.B j (σ + 1) h, J := c.J j (σ + 1) h, B' := c.B (j + 1 + 1) σ (idx_step h),
      s₁ := t.sBF j (σ + 1) h, s₂ := t.sFB j σ h, l := c.lnk j σ h, vL := c.vL j σ h,
      χ₁ := χ j, χ₂ := χ (j + 1), χz := χz, oma := t.kom j, omb := t.kom (j + 1),
      V₁ := V₁, W₁ := W₁, V₂ := V₂, W₂ := W₂, weila := ka, weilb := kb }
  let Fd : Dbl (ofSplit Q'.q) S.B S.J S.B' (Q'.X j) (Q'.X (j + 1)) (Q'.X (j + 1 + 1)) (2 * σ) :=
    { s := Q'.sc j, s_ne := Q'.sc_ne j, F₀ := Q'.FX j (by omega), F₁ := Q'.FX (j + 1) (by omega),
      F₂ := Q'.FX (j + 1 + 1) (by omega), G₀ := Q'.FY j _ e0, G₁ := Q'.FY (j + 1) _ e1, G₂ := Q'.FY (j + 1 + 1) _ e2,
      bes := Q'.bes j (σ + 1) h _ e0, jac := Q'.jac j (σ + 1) h _ e1,
      bes' := by rw [← Q'.sc_step j]; exact Q'.bes (j + 1 + 1) σ (idx_step h) _ e2 }
  have reg1 := (Q'.reg.2.2 (j + 1) _ e1)
  have reg2 := (Q'.reg.2.2 (j + 1 + 1) _ e2)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, A₁, A₂, cov₁, cov₂, d₁, d₂, ent₁, ent₂, e₀, e₂, one₀, one₂, m₁, m₂, haar₁, haar₂,
      vol₁, vol₂, -, -, -⟩ :=
    GlobalTheory.QPl.Inhab.exists_qstep hψ S Q'.ν Q'.unitVol Q'.q Q'.ψk Q'.char Q'.cond (Q'.X j) (Q'.X (j + 1)) (Q'.X (j + 1 + 1))
      (2 * σ) Fd (Q'.T.mu (j + 1)) (Q'.T.mu (j + 1 + 1)) (Q'.mu j (by omega)).1 (Q'.mu (j + 1) (by omega)).1
      (Q'.mu j (by omega)).2 (Q'.mu (j + 1) (by omega)).2 (Q'.T.lev j _ e0) (Q'.T.lev (j + 1) _ e1) (Q'.T.lev (j + 1 + 1) _ e2)
      (Q'.reg.2.2 j _ e0).1 ⟨reg1.1, reg1.2.1⟩ ⟨reg2.1, reg2.2.1⟩ (Q'.le _ _ e1) (Q'.le _ _ e2)
      ⟨Q'.T.Phi j _ e01, Q'.reg.1 _ _ e01⟩ ⟨Q'.T.Phi (j + 1) _ e12, Q'.reg.1 _ _ e12⟩ (Q'.laws.1 j _ e01) (Q'.laws.1 (j + 1) _ e12)
      a 1 1
  let Q : QStep S :=
    { k := Q'.k, ν := Q'.ν, unitVol := Q'.unitVol, q := Q'.q, ψk := Q'.ψk, char := Q'.char, cond := Q'.cond,
      n₀ := Q'.X j, n₁ := Q'.X (j + 1), n₂ := Q'.X (j + 1 + 1), c := 2 * σ, F := Fd,
      gl₀ := Q'.gl j _ e0, gl₁ := Q'.gl (j + 1) _ e1, gl₂ := Q'.gl (j + 1 + 1) _ e2,
      loc₀ := Q'.gl_loc j _ e0, loc₁ := Q'.gl_loc (j + 1) _ e1, loc₂ := Q'.gl_loc (j + 1 + 1) _ e2,
      μ₁ := Q'.T.mu (j + 1), μ₂ := Q'.T.mu (j + 1 + 1), comp₁ := (Q'.mu j (by omega)).1, comp₂ := (Q'.mu (j + 1) (by omega)).1,
      open₁ := (Q'.mu j (by omega)).2, open₂ := (Q'.mu (j + 1) (by omega)).2,
      L₀ := Q'.T.lev j _ e0, L₁ := Q'.T.lev (j + 1) _ e1, L₂ := Q'.T.lev (j + 1 + 1) _ e2,
      co₁ := ⟨reg1.1, reg1.2.1⟩, co₂ := ⟨reg2.1, reg2.2.1⟩, le₁ := Q'.le _ _ e1, le₂ := Q'.le _ _ e2,
      Φ₁ := ⟨Q'.T.Phi j _ e01, Q'.reg.1 _ _ e01⟩, Φ₂ := ⟨Q'.T.Phi (j + 1) _ e12, Q'.reg.1 _ _ e12⟩,
      ty₁ := Q'.laws.1 j _ e01, ty₂ := Q'.laws.1 (j + 1) _ e12,
      D₁ := Q'.eL j, D₂ := Q'.eL (j + 1), dat₁ := Q'.eL_at j _ e01, dat₂ := Q'.eL_at (j + 1) _ e12,
      α := a, A₁ := A₁, A₂ := A₂, cov₁ := cov₁, cov₂ := cov₂, d₁ := d₁, d₂ := d₂, ent₁ := ent₁, ent₂ := ent₂,
      e₀ := e₀, e₂ := e₂, one₀ := one₀, one₂ := one₂, m₁ := m₁, m₂ := m₂, haar₁ := haar₁, haar₂ := haar₂,
      vol₁ := vol₁, vol₂ := vol₂ }
  obtain ⟨T₁, hT₁, -⟩ := GlobalTheory.T.splitPlaceDoubleStepFinitelyManyCellsUniform_proof D c.ψ hψ σ S Q a
  refine ⟨T₁, fun f₁ hf₁ g hg h₁ hh₁ x hx => ?_⟩
  obtain ⟨Tm, hTm, hTmO⟩ := (GlobalTheory.LocMod.indicator_vac D Q'.k Q'.q Q'.unit (Q'.X (j + 1) ⊕ Fin (2 * σ + 2)) (Q'.X j ⊕ Fin (2 * σ + 2 + 1))
    (c.V j) (c.V (j + 1)) (Q'.FY j _ e0) (Q'.FY (j + 1) _ e1) c.ψ Q'.ψk hψ Q'.char Q'.cond (v.N j) (v.N (j + 1))
    (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) (Q'.latY j _ e0) (Q'.latY (j + 1) _ e1)).2 f₁ hf₁
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Q'.k) (Y := Q'.X (j + 1) ⊕ Fin (2 * σ + 2)) (Y' := Q'.X j ⊕ Fin (2 * σ + 2 + 1))
  obtain ⟨f₀, f₂, -, -, -, -, hv2⟩ := GlobalTheory.QPl.Inhab.exists_vac hψ (ι := Unit) (fun _ => Q) (fun _ _ _ => rfl)
  have hvac : Q.Vac f₁ f₂ := ⟨⟨Tm, O, hTm, hO, hTmO O hO⟩, (hv2 ()).2⟩
  have hom := (ht.sBF j (σ + 1) h).1
  obtain ⟨τ, hτ, r, hr, κ, hκ, hx'⟩ := hT₁ f₁ f₂ hvac g hg h₁ hh₁ x (by
    change flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om _ _) ≠ 0
    rw [hom]; exact hx)
  exact ⟨τ, hτ, r, hr, κ, hκ, hx'⟩

theorem finOne_pin : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) (a : GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∃ T : Finset (GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k), ∀ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ → ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v), ∀ x, flatBF (t.sBF j (σ + 1) h) (t.om j (g * (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a, h₁ * (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) x) (comb c.ψ _ _ ((F.Q i).eL j) f₁)) ≠ 0 → ∃ τ ∈ T, ∃ r, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧ ∃ κ ∈ ((F.Q i).T.lev (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega)).J, x = r * τ * κ := by
  intro D c v t w F hc ht hv _ hP j σ h i a
  obtain ⟨χz, V₁, W₁, V₂, W₂⟩ := hP.mid j σ h
  exact core hc.std hv ht (F.Q i) χz j σ h V₁ W₁ V₂ W₂ (hP.kom j (by omega)) (hP.kom (j + 1) (by omega)) a

end GlobalTheory.QFinOneAt
end
