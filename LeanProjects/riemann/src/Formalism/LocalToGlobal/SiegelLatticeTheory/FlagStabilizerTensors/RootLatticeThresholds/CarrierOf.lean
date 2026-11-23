import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergy

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

structure CarrierIn {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Type 1 where
  Wp : InfinitePlace D.host.E → Type
  Wq : InfinitePlace D.host.E → Type
  [pN : ∀ x, NormedAddCommGroup (Wp x)]
  [pI : ∀ x, InnerProductSpace ℂ (Wp x)]
  [qN : ∀ x, NormedAddCommGroup (Wq x)]
  [qI : ∀ x, InnerProductSpace ℂ (Wq x)]
  [pF : ∀ x, FiniteDimensional ℂ (Wp x)]
  [qF : ∀ x, FiniteDimensional ℂ (Wq x)]
  nf : ℕ
  pl : Fin nf ≃ InfinitePlace D.host.E
  emb : Fin nf → (D.host.E →+* ℂ)
  hemb : ∀ v, InfinitePlace.mk (emb v) = pl v
  G : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)
  CA : ℝ
  de : ℕ → ℝ
  de' : ℕ → ℝ
  l : ℕ
  grid : Fin nf → ℕ → Finset ℝ
  grid1 : Fin nf → Finset ℝ
  hv : G.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2
  T : ∀ j : Fin nf, Formalism.FourierDecayAlt.D.LevTower G.k G.r (Wp (pl j)) (Wq (pl j))
  hT : ∀ j, Formalism.QuantumDeterminants.Tz G.k G.r (T j).base.z = ((D.mem u).A.T : ℝ) ∧
    Formalism.QuantumDeterminants.Tz G.k G.r (T j).base.z' = ((D.mem u').A.T : ℝ)
  fc : ∀ j : Fin nf, Formalism.FourierDecayAlt.B.Mat G.k G.r → (Wq (pl j) →L[ℂ] Wp (pl j))
  χ : ℝ → ℝ
  sg : Fin nf → ℂ
  ν' : Fin nf → Fin (2 * G.r + G.k + 1) → ℂ
  m₀ : Fin nf → Formalism.FourierDecayAlt.B.Mat G.k G.r
  top : ∀ j : Fin nf, (Formalism.FourierDecayAlt.B.Mat G.k G.r → (Wq (pl j) →L[ℂ] Wp (pl j))) → List Formalism.FourierDecayAlt.C.Letter →
    Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ
  A₀ : ℝ
  τ : Fin nf ≃ InfinitePlace X.B.I.F
  Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * G.r + G.k + 1)) ℂ
  Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * G.r + G.k + 1)) (Fin X.B.I.n) ℂ
  eP : ∀ v, Wp (pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v
  eQ : ∀ v, Wq (pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v

attribute [instance] CarrierIn.pN CarrierIn.pI CarrierIn.qN CarrierIn.qI CarrierIn.pF CarrierIn.qF

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def sOf (I : CarrierIn X u u') : Formalism.FourierDecayAlt.C.HidaSetting D.host.E I.Wp I.Wq where
  f := I.nf
  pl := I.pl
  emb := I.emb
  hemb := I.hemb
  G := I.G
  CA := I.CA
  de := I.de
  de' := I.de'
  T := ((D.mem u).A.T : ℝ)
  T' := ((D.mem u').A.T : ℝ)
  l := I.l
  grid := I.grid
  grid1 := I.grid1
  pd := fun j => Formalism.FourierDecayAlt.D.componentFamilySetting_ofSetting (I.T j) (I.fc j) I.χ (I.sg j) (I.ν' j) (I.m₀ j) (I.top j)
    ((I.G.g1 * I.G.g2 : ℕ) : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E) 1
  hv := I.hv
  hT := I.hT

structure ModelsFor {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) where
  L : ∀ v : Fin S.f, Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.MA.A (Formalism.FourierDecayAlt.D.parOf S v)
    (Formalism.FourierDecayAlt.MA.DQ (Formalism.FourierDecayAlt.D.parOf S v))) (Formalism.FourierDecayAlt.D.parOf S v).r
  j : ∀ v : Fin S.f, Formalism.FourierDecayAlt.M.Ty (Formalism.FourierDecayAlt.D.parOf S v) →
    Formalism.FourierDecayAlt.MA.SmQ (Formalism.FourierDecayAlt.D.parOf S v).r (Formalism.FourierDecayAlt.D.parOf S v).TT
  lam : ∀ v : Fin S.f, Fin ((Formalism.FourierDecayAlt.D.parOf S v).k + 2 * (Formalism.FourierDecayAlt.D.parOf S v).r + 1) → ℝ
  c : Formalism.FourierDecayAlt.LE.Cut
  Cm : Fin S.f → ℝ
  σ : Fin S.f → ℝ
  Lw : ℕ → Fin S.f → ℝ
  Ll : ℕ → ℕ → Fin S.f → ℝ
  Ll' : ℕ → ℕ → Fin S.f → ℝ

def CarrierOf (I : CarrierIn X u u') (Mo : ModelsFor (sOf I)) : Parts X u u' where
  Wp := I.Wp
  Wq := I.Wq
  S := sOf I
  T := I.T
  f := I.fc
  χ := I.χ
  ν' := I.ν'
  m₀ := I.m₀
  top := I.top
  A₀ := I.A₀
  τ := I.τ
  Q := I.Q
  Qi := I.Qi
  eP := I.eP
  eQ := I.eQ
  L := Mo.L
  j := Mo.j
  lam := Mo.lam
  c := Mo.c
  Cm := Mo.Cm
  σ := Mo.σ
  Lw := Mo.Lw
  Ll := Mo.Ll
  Ll' := Mo.Ll'

theorem pins_carrierOf (I : CarrierIn X u u') (Mo : ModelsFor (sOf I))
    (hr : I.G.r = D.R.rS) (hk : I.G.k = D.R.k) (hg1 : I.G.g1 = D.host.g 0) (hg2 : I.G.g2 = D.host.g 1)
    (hf : I.nf = D.R.f) : (CarrierOf I Mo).Pins I.CA I.G I.de I.de' I.l :=
  ⟨rfl, rfl, rfl, rfl, rfl, hr, hk, hg1, hg2, rfl, rfl, hf⟩

theorem built_carrierOf (I : CarrierIn X u u') (Mo : ModelsFor (sOf I))
    (hsg : ∀ v, I.sg v = Formalism.FourierDecayAlt.M.sgn (Formalism.FourierDecayAlt.D.parOf (sOf I) v) ((sOf I).l + 1))
    (hrest : Formalism.FourierDecayAlt.C6.IsCut0 I.χ ∧ ∀ v,
      Formalism.FourierDecayAlt.D.TowerNormalised (I.T v) ∧ Formalism.FourierDecayAlt.D.IsBaseFrame (I.T v).base (I.ν' v) (I.m₀ v) ∧
      Formalism.FourierDecayAlt.Q.IsPlace (Formalism.FourierDecayAlt.D.parOf (sOf I) v) (I.T v).base.z (I.T v).base.z' (I.T v).base.π (I.T v).base.π' ∧
      (∀ m : ℕ, Formalism.FourierDecayAlt.B.InCC I.A₀ m (I.fc v)) ∧
      ∀ Y : ℝ, ∀ g ∈ Formalism.FourierDecayAlt.B.GV I.G.k I.G.r, Formalism.FourierDecayAlt.Q.CV I.G.k I.G.r (Y : ℂ) (I.fc v) g =
        (((sOf I).P v Y : ℝ) : ℂ) • I.fc v g) :
    (CarrierOf I Mo).Built := by
  refine ⟨hrest.1, fun v => ⟨?_, (hrest.2 v).1, (hrest.2 v).2.1, (hrest.2 v).2.2.1,
    (hrest.2 v).2.2.2.1, (hrest.2 v).2.2.2.2⟩⟩
  exact congrArg (fun t => Formalism.FourierDecayAlt.D.componentFamilySetting_ofSetting (I.T v) (I.fc v) I.χ t (I.ν' v) (I.m₀ v) (I.top v)
    ((I.G.g1 * I.G.g2 : ℕ) : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E) 1) (hsg v)

end Formalism.L2.SG.Pf.Carrier
