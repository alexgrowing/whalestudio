import Formalism.LocalToGlobal.ProjectiveLattices.IsBlockProd
import Formalism.LocalToGlobal.ProjectiveLattices.EtArchPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusPin

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
  ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

section Iso

variable {E : Type} [Field E] [NumberField E]

def IsoPT (X X' : ReciprocityTheory.ChartRestriction.G.I2.PT E)
    (e : ReciprocityTheory.ChartRestriction.G.I2.Vsp X.dim ≃ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp X'.dim) : Prop :=
  (∀ v, v ∈ X.L ↔ e v ∈ X'.L) ∧ (∀ v w, ReciprocityTheory.ChartRestriction.G.I2.Hf (e v) (e w) = ReciprocityTheory.ChartRestriction.G.I2.Hf v w) ∧
    (∀ v ∈ X.L, X'.eps (e v) = X.eps v) ∧
    (∀ (a : 𝓞 E) v, e (ReciprocityTheory.ChartRestriction.G.I2.act a v) = ReciprocityTheory.ChartRestriction.G.I2.act a (e v))

end Iso

section I2AtA

variable {D : D7} (T : Top D) (j : ℕ)

def IsAlphaM (α : 𝓞 D.host.E) : Prop :=
  α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {T.Q.H.bar α}

open Classical in

def FrameTieA (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul (T.Q.Xo j) T.Q.c) (uL : WtR D.host.E) (th : ℝ) {n : ℕ}
    (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (α : 𝓞 D.host.E) : Prop :=
  LawsP T → InR D j → IsBlockProd P₁ → (∀ i, wR i ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) uL.1 uL.2) →
  ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r),
    x ∈ ((T.U j σ).X k).dom →
    ∃ x' : ((T.U j σ).X k).dom, (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm x'.1 τ' i'‖ = 1) ∧
      (∀ τ', ReciprocityTheory.ChartRestriction.G.FD.gram τ'.1 ((T.U j σ).X k).Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x'.1 τ') =
        Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn ((T.U j σ).X k).p0 (a : ℕ) : ℝ) : ℂ)) ∧
      (∀ i, recNrm (T.U j σ) xR uL.1 uL.2 (wR i) k x'.1 = recNrm (T.U j σ) xR uL.1 uL.2 (wR i) k x) ∧
      ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x'.1 = ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x ∧
      ∃ (W : UnfAt (T.U j σ) k x') (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x'.1)
        (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim),
        TorusPins W Wu A L ∧ A.T.l2 1 A.s = 1 ∧
        ∃ (X' : ReciprocityTheory.ChartRestriction.G.I2.PT D.host.E)
          (e : ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim ≃ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp X'.dim), IsoPT A.T X' e ∧
          ∃ ρ : (Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ)) → ReciprocityTheory.ChartRestriction.G.I2.Idx X'.dim,
            (∀ y, e (L (Pi.single (W.e.symm y) 1)) =
              ((Real.sqrt (2 * xiR D) : ℝ) : ℂ) • EuclideanSpace.single (ρ y) (1 : ℂ)) ∧
            ∃ (nb : ℕ) (bs : Fin nb → ReciprocityTheory.ChartRestriction.G.I2.Block D.host.E n X'.dim),
              ReciprocityTheory.ChartRestriction.G.I2.Disj bs ∧
              MvPolynomial.rename (fun l : LtN (T.Q.Dw j) n =>
                ((l.2.2, ρ ⟨l.1, l.2.1⟩) : ReciprocityTheory.ChartRestriction.G.I2.Letter n X'.dim))
                  (MvPolynomial.map ((starRingEnd ℂ).comp σ) P₁) = ReciprocityTheory.ChartRestriction.G.I2.P1 bs ∧
              ReciprocityTheory.ChartRestriction.G.I2.DF bs = P₁.totalDegree ∧
              ∃ K, ReciprocityTheory.ChartRestriction.G.I2.IsReps A.T T.Q.l.M n (vspActL α) K

def GenContainA (nab : NabV (T.Q.Xo j) T.Q.c) (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul (T.Q.Xo j) T.Q.c)
    (uL : WtR D.host.E) {n : ℕ} (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (α : 𝓞 D.host.E) : Prop :=
  ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ((T.U j σ).X k).dom),
    (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm x.1 τ' i'‖ = 1) → ∀ (W : UnfAt (T.U j σ) k x)
    (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x.1)
    (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim), TorusPins W Wu A L →
    ∀ K : Finset (Fin n → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim), ReciprocityTheory.ChartRestriction.G.I2.IsReps A.T T.Q.l.M n (vspActL α) K →
    ∃ jb : (Fin n → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) → Fin (N + 1), Set.InjOn jb K ∧
      ∀ b ∈ K, ∃ (xd x2 : Fin n → (T.Q.Dw j).La) (f : T.R j), IsThRule (T.Q.Xo j) T.Q.c nab xd P₁ f ∧
        (∀ b', x2 b' ∈ (Ideal.span {(2 : 𝓞 D.host.E)} *
          (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) ^ 2) •
            (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La)) ∧
        (∀ b', x2 b' - xd b' ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La)) ∧
        (∀ b', vspActL α (b b' - -((((T.Q.l.M : ℂ) ^ 2)⁻¹) •
          L (star (W.Pm (W.F.t (W.ik k) (T.Q.H.bar α • x2 b')))))) ∈ A.T.L) ∧
        (T.Q.l.M : ℝ) ^ ((P₁.totalDegree : ℝ) / 2) * (2 * Real.pi * xR) ^ (-(P₁.totalDegree : ℝ) / 2) *
            ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k x))‖ ≤
          recNrm (T.U j σ) xR uL.1 uL.2 (wR (jb b)) k x.1

def RunParA (th tableLineDegreeFive DF cc : ℝ) {n : ℕ} (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) : Prop :=
  (P₁.totalDegree : ℝ) = DF ∧
  ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ((T.U j σ).X k).dom)
    (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x.1) (X' : ReciprocityTheory.ChartRestriction.G.I2.PT D.host.E)
    (e : ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim ≃ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp X'.dim), IsoPT A.T X' e →
    ∀ (nb : ℕ) (bs : Fin nb → ReciprocityTheory.ChartRestriction.G.I2.Block D.host.E n X'.dim), ReciprocityTheory.ChartRestriction.G.I2.Disj bs →
    ReciprocityTheory.ChartRestriction.G.I2.DF bs = P₁.totalDegree →
    ∃ P : ReciprocityTheory.ChartRestriction.G.I2.Par X' (ReciprocityTheory.ChartRestriction.G.I2.DF bs), P.q = T.Q.l.M ∧
      ReciprocityTheory.ChartRestriction.G.I2.th (E := D.host.E) P.q P.R0 = th ∧
      (1 / 2 : ℝ) * ((ReciprocityTheory.ChartRestriction.G.I2.PT.f D.host.E : ℝ) * X'.r * n * Real.log P.q +
        n * (Real.log 24 + (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := D.host.E) P.m : ℝ) / 2 *
          Real.log (2 * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := D.host.E) P.m : ℝ))) +
        (X'.r + 2) * Real.log 2) ≤ tableLineDegreeFive ∧
      ∃ PP : ℝ, 16200 * Real.pi * n * (P.m : ℝ) ^ 4 *
          (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := D.host.E) P.m : ℝ) ^ 4 ≤ PP ∧
        cc = ReciprocityTheory.ChartRestriction.G.I2.RR (E := D.host.E) * PP * DF ^ 2 / P.q

def I2AtFramePointsAlpha : Prop :=
  ∀ (_hL : LawsP T) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) →
    ∀ (w : WeightFamilies.Wt D j) (P₁ : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA w) w.n →
    IsBlockProd P₁ →
    ∀ (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul (T.Q.Xo j) T.Q.c) (uL : WtR D.host.E) (th tableLineDegreeFive DF cc : ℝ),
    xR = xiR D → (∀ i, wR i ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) uL.1 uL.2) →
    ∀ α : 𝓞 D.host.E, IsAlphaM T α →
    ThetaValCAlphaSt → GenContainA T j nab xR wR uL P₁ α → FrameTieA T j xR wR uL th P₁ α →
    RunParA T j th tableLineDegreeFive DF cc P₁ →
    I2AtFramePoints (T.U j) xR wR uL th tableLineDegreeFive DF cc

end I2AtA

section EtA

variable {D : D7} {T : Top D} (h : LawsP T)

def EtProdA (r1 Nc nt : ℕ) : ∀ j i, (recB h.toLawsCore).Cusp j (wEt D j i) → Prop :=
  fun j i η => ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ((T.U j σ).X k).dom),
    (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm x.1 τ' i'‖ = 1) →
    ∃ (W : UnfAt (T.U j σ) k x) (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x.1)
      (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim), TorusPins W Wu A L ∧
      ∃ c : Fin (2 * r1 ^ 4 * i) → Fin nt → ℤ,
      ∃ a : Fin (2 * r1 ^ 4 * i) → Fin nt → Fin A.T.r → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim,
      (∀ g t, |c g t| ≤ Nc) ∧ (∀ g t, TrOK A.T r1 (a g t)) ∧
      lieFac (T.Q.Dw j) (xiR D) (wtA (wEt D j i)) *
          ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA (wEt D j i)) (wEt D j i).n k) (rdU (T.U j σ) η.1 k) x.1 ≤
        ∏ g, ∑ t, |(c g t : ℝ)| * thRat A.T A.s (a g t)

def EtArchAlphaSt (th tableLineDegreeTwo : ℝ) (j i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)) (DF m r1 Nc nt : ℕ)
    (R0 : ℝ) : Prop :=
  th = ReciprocityTheory.ChartRestriction.G.I2.th (E := D.host.E) T.Q.l.M R0 → 2 ≤ r1 →
    EtNum D.host.E D.R.r T.Q.l.M m r1 Nc nt tableLineDegreeTwo → EtParRun T j DF T.Q.l.M m R0 →
    EtProdA h r1 Nc nt j i η → EtArch h th tableLineDegreeTwo j i η

end EtA

end Formalism.L2.Pj
