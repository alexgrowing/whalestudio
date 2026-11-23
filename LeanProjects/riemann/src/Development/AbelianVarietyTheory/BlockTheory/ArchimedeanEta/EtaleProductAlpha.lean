import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsBlockProd
import Formalism.LocalToGlobal.ProjectiveLattices.EtArchPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusPin

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EtaleProductIsoRefl

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

section Iso

open ReciprocityTheory.ChartRestriction.G.I2

variable {E : Type} [Field E] [NumberField E]

def IsoPT (X X' : PT E) (e : Vsp X.dim ≃ₗ[ℂ] Vsp X'.dim) : Prop :=
  (∀ v, e v ∈ X'.L ↔ v ∈ X.L) ∧ (∀ v w, Hf (e v) (e w) = Hf v w) ∧
    (∀ v ∈ X.L, X'.eps (e v) = X.eps v) ∧ ∀ (a : 𝓞 E) v, e (act a v) = act a (e v)

end Iso

variable {D : D7}

def IsAlphaM (T : Top D) (α : 𝓞 D.host.E) : Prop :=
  α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {T.Q.H.bar α}

def EtProdA {T : Top D} (h : LawsP T) (r1 Nc nt : ℕ) (j i : ℕ)
    (η : (recB h.toLawsCore).Cusp j (wEt D j i)) : Prop :=
  ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ((T.U j σ).X k).dom),
    (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm x.1 τ' i'‖ = 1) →
    ∀ (W : UnfAt (T.U j σ) k x) (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x.1)
      (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim), TorusPins W Wu A L →
      ∃ (c : Fin (2 * r1 ^ 4 * i) → Fin nt → ℤ)
        (a : Fin (2 * r1 ^ 4 * i) → Fin nt → Fin A.T.r → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim),
        (∀ g t, |c g t| ≤ (Nc : ℤ)) ∧ (∀ g t, TrOK A.T r1 (a g t)) ∧
        recNrm (T.U j σ) (xiR D) (wtA (wEt D j i)) (wEt D j i).n η.1 k x.1 ≤
          ∏ g, ∑ t, |(c g t : ℝ)| * thRat A.T A.s (a g t)

def EtArchAlphaSt : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j →
    ∀ (i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)) (DF m r1 Nc nt : ℕ) (R0 tableLineDegreeTwo : ℝ), 2 ≤ r1 →
      EtNum D.host.E D.R.r T.Q.l.M m r1 Nc nt tableLineDegreeTwo →
      EtParRun T j DF T.Q.l.M m R0 →
      EtProdA h r1 Nc nt j i η →
      ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r),
        x ∈ ((T.U j σ).X k).dom →
        recNrm (T.U j σ) (xiR D) (wtA (wEt D j i)) (wEt D j i).n η.1 k x ≤
          Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k)
            (ReciprocityTheory.ChartRestriction.G.I2.th (E := D.host.E) T.Q.l.M R0) x - tableLineDegreeTwo))

example (H : EtArchAlphaSt) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (i : ℕ)
    (η : (recB h.toLawsCore).Cusp j (wEt D j i)) (DF m r1 Nc nt : ℕ) (R0 tableLineDegreeTwo : ℝ) (hr : 2 ≤ r1)
    (hn : EtNum D.host.E D.R.r T.Q.l.M m r1 Nc nt tableLineDegreeTwo) (hp : EtParRun T j DF T.Q.l.M m R0)
    (he : EtProdA h r1 Nc nt j i η) :
    EtArch h (ReciprocityTheory.ChartRestriction.G.I2.th (E := D.host.E) T.Q.l.M R0) tableLineDegreeTwo j i η :=
  H D T h j hj i η DF m r1 Nc nt R0 tableLineDegreeTwo hr hn hp he

example (T : Top D) (h : LawsP T) (j i : ℕ)
    (η : (recB h.toLawsCore).Cusp j (wEt D j i)) (DF m r1 Nc nt : ℕ) (R0 tableLineDegreeTwo : ℝ) (hr : 2 ≤ r1)
    (hn : EtNum D.host.E D.R.r T.Q.l.M m r1 Nc nt tableLineDegreeTwo) (hp : EtParRun T j DF T.Q.l.M m R0)
    (he : EtProdA h r1 Nc nt j i η) (σ) (hσ : GoodEmb T.Q.c σ) (k : (T.U j σ).Comp) (x : ((T.U j σ).X k).dom)
    (hu : ∀ τ' i', ‖dmin ((T.U j σ).X k).Gm x.1 τ' i'‖ = 1)
    (W : UnfAt (T.U j σ) k x) (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x.1)
    (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) (hL : TorusPins W Wu A L) :
    recNrm (T.U j σ) (xiR D) (wtA (wEt D j i)) (wEt D j i).n η.1 k x.1 ≤
      Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k)
        (ReciprocityTheory.ChartRestriction.G.I2.th (E := D.host.E) T.Q.l.M R0) x.1 - tableLineDegreeTwo)) := by
  obtain ⟨c, a, hc, ha, hle⟩ := he σ hσ k x hu W Wu A L hL
  obtain ⟨P, hq, hR, hm⟩ := hp σ hσ k x.1 x.2 A
  have hTr : A.T.r = D.R.r := torusAt_r A
  have hph : P.ph = ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k)
      (ReciprocityTheory.ChartRestriction.G.I2.th (E := D.host.E) T.Q.l.M R0) x.1 := by
    rw [ReciprocityTheory.ChartRestriction.G.I2.Par.ph, hq, hR]
    exact (ReciprocityTheory.ChartRestriction.G.I2.TorusAtPf.torusAtLa1_holds _ _ _ x.1 x.2 A.T
      (ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.torusAtIs_holds _ _ _ x.1 A)).2 _
  refine hle.trans ?_
  have hb := etProd_bound A.T P r1 hr A.s A.s_mem A.s_ne c a hc ha (by rw [hTr, hq, hm]; exact hn)
  rwa [hph] at hb

end GlobalTheory.IndefiniteRowSideFullHecke.EtaleProductIsoRefl
