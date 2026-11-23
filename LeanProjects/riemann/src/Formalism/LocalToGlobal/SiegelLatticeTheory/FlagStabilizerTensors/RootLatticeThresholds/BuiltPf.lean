import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Built

open Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def chiStd (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

theorem isCut0_chiStd : Formalism.FourierDecayAlt.C6.IsCut0 chiStd := by
  unfold Formalism.FourierDecayAlt.C6.IsCut0
  refine ⟨?_, ⟨1 / 2, by norm_num, fun x hx => ?_⟩, fun x hx => ?_⟩
  · show ContDiff ℝ _ (Real.smoothTransition ∘ fun x : ℝ => 2 * x - 1)
    exact Real.smoothTransition.contDiff.comp (by fun_prop)
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · exact Real.smoothTransition.one_of_one_le (by linarith)

section tower

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def towerOf (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : Formalism.FourierDecayAlt.D.LevTower k r Wp Wq :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose

theorem towerOf_base (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : (towerOf B h1 h2 h3).base = B :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose_spec.1

theorem towerOf_norm (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : Formalism.FourierDecayAlt.D.TowerNormalised (towerOf B h1 h2 h3) :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose_spec.2

end tower

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

abbrev par (I : CarrierIn X u u') (v : Fin I.nf) : Formalism.FourierDecayAlt.M.Par := Formalism.FourierDecayAlt.D.parOf (sOf I) v

def sgOf {nf : ℕ} (G : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (pl : Fin nf ≃ InfinitePlace D.host.E)
    (T T' : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (v : Fin nf) : ℂ :=
  Formalism.FourierDecayAlt.M.sgn ⟨G.k, G.r, T, T', (G.place (pl v)).u de, (G.place (pl v)).u de'⟩ l

theorem sg_of (I : CarrierIn X u u')
    (h : I.sg = sgOf I.G I.pl ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) I.de I.de' (I.l + 1)) :
    ∀ v, I.sg v = Formalism.FourierDecayAlt.M.sgn (par I v) ((sOf I).l + 1) := by
  intro v
  rw [h]
  rfl

def ParNums (I : CarrierIn X u u') : Prop :=
  ∀ v, (∀ i ∈ Finset.Icc 1 (par I v).k, ∃ n : ℤ, (par I v).u i - (par I v).u 1 = n) ∧
    (∀ i ∈ Finset.Icc 1 (par I v).k, ∃ n : ℤ, (par I v).u' i - (par I v).u 1 = n) ∧
    ∀ i ∈ Finset.Icc 1 ((par I v).k - 1), (par I v).lo i ≤ (par I v).hi i

def Types (I : CarrierIn X u u') : Prop :=
  ∀ v, Formalism.FourierDecayAlt.Q.IsType I.G.k I.G.r (I.T v).base.z (I.T v).base.π (par I v).u ∧
    Formalism.FourierDecayAlt.Q.IsType I.G.k I.G.r (I.T v).base.z' (I.T v).base.π' (par I v).u'

def Frames (I : CarrierIn X u u') : Prop := ∀ v, Formalism.FourierDecayAlt.D.IsBaseFrame (I.T v).base (I.ν' v) (I.m₀ v)

def CoefCC (I : CarrierIn X u u') : Prop := ∀ v (m : ℕ), Formalism.FourierDecayAlt.B.InCC I.A₀ m (I.fc v)

def CoefCap (I : CarrierIn X u u') : Prop :=
  ∀ v (Y : ℝ), ∀ g ∈ Formalism.FourierDecayAlt.B.GV I.G.k I.G.r,
    Formalism.FourierDecayAlt.Q.CV I.G.k I.G.r (Y : ℂ) (I.fc v) g = (((sOf I).P v Y : ℝ) : ℂ) • I.fc v g

theorem isPlace_of (I : CarrierIn X u u') (hN : ParNums I) (hty : Types I) (v : Fin I.nf) :
    Formalism.FourierDecayAlt.Q.IsPlace (par I v) (I.T v).base.z (I.T v).base.z' (I.T v).base.π (I.T v).base.π' := by
  unfold Formalism.FourierDecayAlt.Q.IsPlace
  obtain ⟨h1, h2, h3⟩ := hN v
  obtain ⟨t1, t2⟩ := hty v
  obtain ⟨e1, e2⟩ := I.hT v
  have p1 := (I.T v).base.T_pos
  have p2 := (I.T v).base.T'_pos
  rw [e1] at p1
  rw [e2] at p2
  exact ⟨⟨(I.T v).base.k_pos, p1, p2, h1, h2, h3⟩, (I.T v).base.z_mem, (I.T v).base.z'_mem, e1, e2, t1, t2⟩

def FramesExist : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (I : CarrierIn X u u') (Mo : ModelsFor (sOf I))
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k), (CarrierOf I Mo).FromX → (∀ v, i0 v = i0' v) →
    ∃ (ν' : Fin I.nf → Fin (2 * I.G.r + I.G.k + 1) → ℂ) (m₀ : Fin I.nf → Formalism.FourierDecayAlt.B.Mat I.G.k I.G.r),
      Formalism.L2.SG.RealObj.BaseFromX X (sOf I) u u' i0 i0' I.τ I.Q I.Qi ν' m₀ ∧
        ∀ v, Formalism.FourierDecayAlt.D.IsBaseFrame (I.T v).base (ν' v) (m₀ v)

end Formalism.L2.SG.Pf.Built
