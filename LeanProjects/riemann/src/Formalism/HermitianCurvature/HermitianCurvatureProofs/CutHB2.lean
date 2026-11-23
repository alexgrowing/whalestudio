import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenDomP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UpperMinorOfLevelPoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section defs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def phf {P : M.Par} (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j + 1 ≤ P.r)
    (w : List C.Letter) (h : C.LPt) (hs : D.ptSize h = j) (γ : B.Mat P.k (P.r - (j + 1))) (v : XH h)
    (e : Wd.Ix (Fin w.length)) (τ : ℂ) : Wq →L[ℂ] Wp :=
  D.uwG P.k P.r p.T.base.z p.T.base.z' (pbT p j (by omega) F) j (by omega) w e (x0 P.k P.r j hj (zxH h j hs v) τ γ)

open Classical in

def phx {P : M.Par} (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j + 1 ≤ P.r)
    (w : List C.Letter) (h : C.LPt) (hs : D.ptSize h = j) (γ : B.Mat P.k (P.r - (j + 1))) (v : XH h)
    (e : Wd.Ix (Fin w.length)) : V1 (Wq →L[ℂ] Wp) :=
  if hc : ContDiffOn ℝ ∞ (phf p F j hj w h hs γ v e) {τ | τ ≠ 0} then ⟨phf p F j hj w h hs γ v e, hc⟩ else 0

end defs

def GoodFam {E X S : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Φ : X → S → V1 E) : Prop :=
  (∀ e, ContDiffOn ℝ ∞ (fun q : X × ℂ => (Φ q.1 e : ℂ → E) q.2) (Set.univ ×ˢ {τ | τ ≠ 0})) ∧
    ∀ K : Set ℂ, IsCompact K → K ⊆ {τ | τ ≠ 0} →
      ∃ C : Set X, IsCompact C ∧ ∀ v ∉ C, ∀ τ ∈ K, ∀ e, (Φ v e : ℂ → E) τ = 0

def RulesEq : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r), KB.CptCoef p.T.base F →
    (∀ g ∈ Q.Glev P.k P.r 0 ∩ domP P.k P.r j p.T.base.z p.T.base.z', ∀ n ∈ QuantumDeterminants.Nset P.k P.r,
      g * n ∈ domP P.k P.r j p.T.base.z p.T.base.z' ∧
        pbT p j (by omega) F (g * n) = psi P.k P.r p.T.base.z' cStd n • pbT p j (by omega) F g) ∧
    ∀ g ∈ Q.Glev P.k P.r 0 ∩ domP P.k P.r j p.T.base.z p.T.base.z', ∀ a : Fin j → ℂ,
      nL P.k P.r j hj a * g ∈ domP P.k P.r j p.T.base.z p.T.base.z' ∧
        pbT p j (by omega) F (nL P.k P.r j hj a * g) = psi P.k P.r p.T.base.z cStd (nL P.k P.r j hj a) • pbT p j (by omega) F g

def WordSmooth : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter), KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ e : Wd.Ix (Fin w.length), Q.SmoothLev P.k P.r 0 (domP P.k P.r j p.T.base.z p.T.base.z')
      (D.uwG P.k P.r p.T.base.z p.T.base.z' (pbT p j (by omega) F) j (by omega) w e)

def Pts : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j + 1 ≤ P.r) (h : C.LPt) (hh : D.IsLocPt h j) (γ : B.Mat P.k (P.r - (j + 1))),
    γ ∈ B.GV P.k (P.r - (j + 1)) → γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ v : XH h, (zxH h j hh.2 v).det ≠ 0 ∧
      ∀ τ : ℂ, τ ≠ 0 → x0 P.k P.r j hj (zxH h j hh.2 v) τ γ ∈ domP P.k P.r j p.T.base.z p.T.base.z'

def CurveSmooth : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (h : C.LPt) (hh : D.IsLocPt h j) (γ : B.Mat k (r - (j + 1))),
    ContDiffOn ℝ ∞ (fun q : XH h × ℂ => x0 k r j hj (zxH h j hh.2 q.1) q.2 γ) (Set.univ ×ˢ {τ | τ ≠ 0})

def Supp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ K : Set ℂ, IsCompact K → K ⊆ {τ | τ ≠ 0} →
      ∃ C : Set (XH h), IsCompact C ∧ ∀ v ∉ C, ∀ τ ∈ K, ∀ e, phf p F j hj w h hh.2 γ v e τ = 0

def Side0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ (e : Wd.Ix (Fin w.length)) (τ : ℂ), τ ≠ 0 →
      B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 e) (mLev P j hj τ γ) =
        ∫ v, ellH h v (phf p F j hj w h hh.2 γ v e τ)

def Side1 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
      B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
        ∫ v, ellH h v (D.uwG P.k P.r p.T.base.z p.T.base.z' (pbT p j (by omega) F) (j + 1) hj w e
          (x0 P.k P.r j hj (zxH h j hh.2 v) t γ))

def Side0Pos : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))), 1 ≤ j →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ (e : Wd.Ix (Fin w.length)) (τ : ℂ), τ ≠ 0 →
      B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 e) (mLev P j hj τ γ) =
        ∫ v, ellH h v (phf p F j hj w h hh.2 γ v e τ)

def Side0Zero : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))), j = 0 →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ (e : Wd.Ix (Fin w.length)) (τ : ℂ), τ ≠ 0 →
      B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 e) (mLev P j hj τ γ) =
        ∫ v, ellH h v (phf p F j hj w h hh.2 γ v e τ)

def Side1Pos : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))), 1 ≤ j →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
      B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
        ∫ v, ellH h v (D.uwG P.k P.r p.T.base.z p.T.base.z' (pbT p j (by omega) F) (j + 1) hj w e
          (x0 P.k P.r j hj (zxH h j hh.2 v) t γ))

def Side1Zero : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))), j = 0 →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
      B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
        ∫ v, ellH h v (D.uwG P.k P.r p.T.base.z p.T.base.z' (pbT p j (by omega) F) (j + 1) hj w e
          (x0 P.k P.r j hj (zxH h j hh.2 v) t γ))

theorem side_zero_of_positive_and_zero (hp : Side0Pos) (hz : Side0Zero) : Side0 := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hF hw hγ hΩ e τ hτ
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · exact hz Wp Wq P p F j hj w h hh γ h0 hF hw hγ hΩ e τ hτ
  · exact hp Wp Wq P p F j hj w h hh γ h0 hF hw hγ hΩ e τ hτ

theorem side_one_of_positive_and_zero (hp : Side1Pos) (hz : Side1Zero) : Side1 := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hF hw hγ hΩ t ht e
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · exact hz Wp Wq P p F j hj w h hh γ h0 hF hw hγ hΩ t ht e
  · exact hp Wp Wq P p F j hj w h hh γ h0 hF hw hγ hΩ t ht e

def OneBTInt : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (X : Type) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] (ℓ : X → E →L[ℂ] E), Continuous ℓ →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (κ : ℂ) (w : List (Wd.Letter ℂ S)) (Φ : X → Wd.Ix S → V1 E),
      GoodFam Φ → ∀ f : Wd.Ix S → V1 E, (∀ e τ, τ ≠ 0 → (f e : ℂ → E) τ = ∫ v, ℓ v ((Φ v e : ℂ → E) τ) ∂μ) →
      ∀ t : ℂ, t ≠ 0 → ∀ e, (oneBT κ w f e : ℂ → E) t = ∫ v, ℓ v ((oneBT κ w (Φ v) e : ℂ → E) t) ∂μ

section asm

theorem cont_lowW {p : ℕ} (σ : Equiv.Perm (Fin p)) : Continuous (U.lowW σ) := by
  unfold U.lowW
  refine continuous_const.add ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem cont_lhOf {p : ℕ} (σ : Equiv.Perm (Fin p)) : Continuous (LeftFubiniLemmas.lhOf σ) := by
  unfold LeftFubiniLemmas.lhOf
  exact (continuous_const.matrix_mul (cont_lowW σ)).matrix_mul continuous_const

theorem cont_subS {p : ℕ} : Continuous (U.subS (p := p)) := by
  unfold U.subS
  refine continuous_finset_sum _ fun i _ => ?_
  split_ifs
  · exact (continuous_apply i).comp (continuous_apply _)
  · exact continuous_const

theorem cont_ellH {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (h : C.LPt) : Continuous (ellH (Wp := Wp) (Wq := Wq) h) := by
  have hs : Continuous fun v : XH h => G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf (D.ptPerm h) v)) := by
    unfold G.psi
    refine Complex.continuous_exp.comp (continuous_const.mul ?_)
    refine Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul ?_))
    exact cont_subS.comp (cont_lhOf _)
  unfold ellH
  exact hs.smul continuous_const

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jointSmooth (hW : WordSmooth) (hP : Pts) (hC : CurveSmooth) {P : M.Par} (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))) (hF : KB.CptCoef p.T.base F) (hw : KB.CutWord P p.l0 w)
    (hγ : γ ∈ B.GV P.k (P.r - (j + 1)))
    (hΩ : γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z') (e : Wd.Ix (Fin w.length)) :
    ContDiffOn ℝ ∞ (fun q : XH h × ℂ => phf p F j hj w h hh.2 γ q.1 e q.2) (Set.univ ×ˢ {τ | τ ≠ 0}) := by
  have hcur := hC P.k P.r j hj h hh γ
  have hsm := hW Wp Wq P p F j hj w hF hw e
  have hGl : ∀ y : XH h × ℂ, y.2 ≠ 0 →
      x0 P.k P.r j hj (zxH h j hh.2 y.1) y.2 γ ∈ Q.Glev P.k P.r 0 ∩ domP P.k P.r j p.T.base.z p.T.base.z' := by
    intro y hy
    obtain ⟨hdet, hdom⟩ := hP Wp Wq P p j hj h hh γ hγ hΩ y.1
    exact ⟨⟨LevelPointCoordinates.x0_GV hj hdet hy hγ, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hdom y.2 hy⟩
  refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
  obtain ⟨U, G, hU, hqU, hGs, hGe⟩ := hsm _ (hGl q hq.2)
  obtain ⟨V, hV, hVeq⟩ := (continuousOn_iff'.1 hcur.continuousOn) U hU
  have hqV : q ∈ V ∩ (Set.univ ×ˢ {τ : ℂ | τ ≠ 0}) := by
    rw [← hVeq]
    exact ⟨hqU, hq⟩
  have hmap : Set.MapsTo (fun y : XH h × ℂ => x0 P.k P.r j hj (zxH h j hh.2 y.1) y.2 γ)
      ((Set.univ ×ˢ {τ : ℂ | τ ≠ 0}) ∩ V) U := by
    intro y hy
    have hy' : y ∈ V ∩ (Set.univ ×ˢ {τ : ℂ | τ ≠ 0}) := ⟨hy.2, hy.1⟩
    rw [← hVeq] at hy'
    exact hy'.1
  refine ⟨V, hV, hqV.1, ?_⟩
  refine (hGs.comp (hcur.mono Set.inter_subset_left) hmap).congr fun y hy => ?_
  exact hGe _ (hmap hy) (hGl y hy.1.2).1

theorem phx_eq (hW : WordSmooth) (hP : Pts) (hC : CurveSmooth) {P : M.Par} (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))) (hF : KB.CptCoef p.T.base F) (hw : KB.CutWord P p.l0 w)
    (hγ : γ ∈ B.GV P.k (P.r - (j + 1)))
    (hΩ : γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z') (v : XH h)
    (e : Wd.Ix (Fin w.length)) : (phx p F j hj w h hh.2 γ v e : ℂ → (Wq →L[ℂ] Wp)) = phf p F j hj w h hh.2 γ v e := by
  have hc : ContDiffOn ℝ ∞ (phf p F j hj w h hh.2 γ v e) {τ | τ ≠ 0} := by
    have hj2 := jointSmooth hW hP hC p F j hj w h hh γ hF hw hγ hΩ e
    have hg : ContDiffOn ℝ ∞ (fun τ : ℂ => ((v, τ) : XH h × ℂ)) {τ : ℂ | τ ≠ 0} :=
      contDiffOn_const.prodMk contDiffOn_id
    have hm : Set.MapsTo (fun τ : ℂ => ((v, τ) : XH h × ℂ)) {τ : ℂ | τ ≠ 0}
        (Set.univ ×ˢ {τ : ℂ | τ ≠ 0}) := fun τ hτ => Set.mk_mem_prod (Set.mem_univ v) hτ
    have hk := hj2.comp hg hm
    exact hk.congr fun τ _ => rfl
  unfold phx
  rw [dif_pos hc]

end asm

theorem headBridge_of (hR : RulesEq) (hW : WordSmooth) (hP : Pts) (hC : CurveSmooth) (hS : Supp) (h0 : Side0)
    (h1 : Side1) (hO : OneBTInt) : LevelPointCoordinates.HeadBridge := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hF hw hγ hΩ φ hφ t ht e
  have hpx : ∀ (v : XH h) (e' : Wd.Ix (Fin w.length)),
      (phx p F j hj w h hh.2 γ v e' : ℂ → (Wq →L[ℂ] Wp)) = phf p F j hj w h hh.2 γ v e' :=
    fun v e' => phx_eq hW hP hC p F j hj w h hh γ hF hw hγ hΩ v e'
  have hsm : SmoothLev P.k P.r 0 (domP P.k P.r j p.T.base.z p.T.base.z') (pbT p j (by omega) F) := by
    have hcw : KB.CutWord P p.l0 [] := ⟨fun a => a.elim0, fun a => a.elim0⟩
    exact hW Wp Wq P p F j hj [] hF hcw (fun i => i.elim0)
  have hRl := hR Wp Wq P p F j hj hF
  have htne : t ≠ 0 := (ht.1 (1, t) (by simp)).2
  have hGood : GoodFam (fun v : XH h => phx p F j hj w h hh.2 γ v) := by
    refine ⟨fun e' => ?_, fun K hK hKs => ?_⟩
    · exact (jointSmooth hW hP hC p F j hj w h hh γ hF hw hγ hΩ e').congr
        fun q _ => congrFun (hpx q.1 e') q.2
    · obtain ⟨C, hC', hCv⟩ := hS Wp Wq P p F j hj w h hh γ hF hw hγ hΩ K hK hKs
      refine ⟨C, hC', fun v hv τ hτ e' => ?_⟩
      rw [hpx v e']
      exact hCv v hv τ hτ e'
  have hf : ∀ (e' : Wd.Ix (Fin w.length)) (τ : ℂ), τ ≠ 0 →
      (φ e' : ℂ → (Wq →L[ℂ] Wp)) τ =
        ∫ v, ellH h v ((phx p F j hj w h hh.2 γ v e' : ℂ → (Wq →L[ℂ] Wp)) τ) := by
    intro e' τ hτ
    rw [hφ e' τ hτ, h0 Wp Wq P p F j hj w h hh γ hF hw hγ hΩ e' τ hτ]
    congr 1
    funext v
    rw [hpx v e']
  refine ⟨XH h, inferInstance, MeasureTheory.volume, ellH h, fun v => zxH h j hh.2 v,
    fun _ => pbT p j (by omega) F, domP P.k P.r j p.T.base.z p.T.base.z',
    fun v => phx p F j hj w h hh.2 γ v, isOpen_domP _ _ _ _ _, minorDomain_subset _ _ _ hj _ _,
    fun _ => ⟨hsm, hRl.1, hRl.2⟩, fun v => hP Wp Wq P p j hj h hh γ hγ hΩ v, ?_, ?_, ?_⟩
  · intro v e' τ _
    rw [hpx v e']
    rfl
  · exact h1 Wp Wq P p F j hj w h hh γ hF hw hγ hΩ t ht e
  · exact hO (Wq →L[ℂ] Wp) (XH h) MeasureTheory.volume (ellH h) (cont_ellH h) (Fin w.length) (kapJ P j)
      (D.positionted w) (fun v => phx p F j hj w h hh.2 γ v) hGood φ hf t htne e

end Formalism.FourierDecayAlt.P.CutHB
