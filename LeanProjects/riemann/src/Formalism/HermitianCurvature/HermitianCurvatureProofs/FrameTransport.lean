import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadTopOfRadialExhaustion

noncomputable section

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.PBI

def FrameTransport : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')))
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))),
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    ∀ c : Fin P.r → ℂ, c ∈ Formalism.QuantumDeterminants.OmX P.r →
    ∃ T : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' →ₗ[ℂ]
        Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π',
      (∀ Ψ c' g, (T Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c' g =
        (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g))) ∧
      ∀ (w : List C.Letter), Fr.admitted st₀ (D.positionted w) → Fr.admitted st (D.positionted w) →
      ∀ (Ψ : Wd.Ix (Fin w.length) → Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')
        (e : Wd.Ix (Fin w.length)) (c' : Fin (JC.parLev P P.r).r → ℂ) (g : B.Mat P.k (P.r - P.r)),
        g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g →
        (P5.act (Fr.ofWord L₀ st₀ (D.positionted w)).F Ψ e : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
            c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g)) =
          (P5.act (Fr.ofWord L st (D.positionted w)).F (fun e' => T (Ψ e')) e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c' g

def ParFam {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Par : Type} [NormedAddCommGroup Par]
    [NormedSpace ℝ Par] (k ρ : ℕ) (U₀ : Set (Par × Mt k ρ)) (f : Par × Mt k ρ → E) : Prop :=
  ∀ q₀ ∈ U₀, Matrix.of q₀.2 ∈ Q.Glev k ρ (Fin.last ρ) → ∃ (U : Set (Par × Mt k ρ)) (F : Par × Mt k ρ → E),
    IsOpen U ∧ q₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ q ∈ U, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q = F q

def FrameParam : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    ∀ (w : List C.Letter), Fr.admitted st (D.positionted w) →
    ∀ (Par : Type) [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par] [MeasurableSpace Par]
      [BorelSpace Par] (U₀ : Set (Par × Mt P.k (P.r - P.r))), IsOpen U₀ →
      U₀ ⊆ Set.univ ×ˢ {y | 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)} →
    ∀ (Ψ : Par → Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
        (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
      (Ψf : Par → Wd.Ix (Fin w.length) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp)),
      (∀ Z e c y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
        (Ψ Z e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y) = Ψf Z e y) →
      (∀ e, ParFam P.k (P.r - P.r) U₀ (fun q => Ψf q.1 e q.2)) →
      ∃ Φf : Par → Wd.Ix (Fin w.length) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp),
        (∀ Z e c y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
          (P5.act (Fr.ofWord L st (D.positionted w)).F (Ψ Z) e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y) = Φf Z e y) ∧
        (∀ e, ParFam P.k (P.r - P.r) U₀ (fun q => Φf q.1 e q.2)) ∧
        (∀ (K : Set (Par × Mt P.k (P.r - P.r))),
          (∀ e q, Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → q ∉ K → Ψf q.1 e q.2 = 0) →
          ∀ e q, q ∈ U₀ → Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → q ∉ closure K → Φf q.1 e q.2 = 0) ∧
        ∀ (ν : Measure Par) [IsFiniteMeasure ν] (Kp : Set Par), IsCompact Kp → ν Kpᶜ = 0 →
        ∀ (Ψi : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
            (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') (y : Mt P.k (P.r - P.r)) (V : Set (Mt P.k (P.r - P.r))),
          IsOpen V → y ∈ V → Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → Kp ×ˢ V ⊆ U₀ →
          (∀ e c y', y' ∈ V → Matrix.of y' ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
            (Ψi e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y') =
              ∫ Z, Ψf Z e y' ∂ν) →
          ∀ e c, (P5.act (Fr.ofWord L st (D.positionted w)).F Ψi e :
              Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y) = ∫ Z, Φf Z e y ∂ν

def RadWord : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'))),
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    ∀ (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base G →
    ∀ (w : List C.Letter), KB.CutWord P p.l0 w →
    ∀ Φ_G : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ_G G →
    ∀ e : Wd.Ix (Fin w.length),
      Top.IsRadOf P p.T.base (P5.act (P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ_G) e)
        (D.uwG P.k P.r p.T.base.z p.T.base.z' G P.r le_rfl w e)

def hcell {r : ℕ} (c : Fin r → ℂ) : C.LPt := List.ofFn fun j => (1, c j)

theorem ptSize_hcell {r : ℕ} (c : Fin r → ℂ) : D.ptSize (hcell c) = r := by
  simp [hcell, D.ptSize, List.map_ofFn, Function.comp_def]

def RadWordSlice : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'))),
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    ∀ (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base G →
    ∀ (w : List C.Letter), KB.CutWord P p.l0 w →
    ∀ Φ_G : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ_G G →
    ∀ (e : Wd.Ix (Fin w.length)) (c : Fin P.r → ℂ), c ∈ Formalism.QuantumDeterminants.OmX P.r →
    ∀ g : B.Mat P.k (P.r - P.r), g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
      0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g →
      (P5.act (P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ_G) e : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
          c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g)) =
        ((∏ j : Fin P.r, ‖c j‖ ^ (2 * (P.r - (j : ℕ)) + P.k) : ℝ) : ℂ) •
          B.JF (p.T.bs P.r) (D.castF (by rw [ptSize_hcell]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z'
            (D.uwG P.k P.r p.T.base.z p.T.base.z' G P.r le_rfl w e) (hcell c))) g

def PicSlice : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base G →
    ∀ Φ_G : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ_G G →
    ∀ (c : Fin P.r → ℂ), c ∈ Formalism.QuantumDeterminants.OmX P.r →
    ∀ g : B.Mat P.k (P.r - P.r), g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
      0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g →
      (Φ_G : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g)) =
        ((∏ j : Fin P.r, ‖c j‖ ^ (2 * (P.r - (j : ℕ)) + P.k) : ℝ) : ℂ) •
          B.JF (p.T.bs P.r) (D.castF (by rw [ptSize_hcell]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G (hcell c))) g

end Formalism.FourierDecayAlt.P.PBI
