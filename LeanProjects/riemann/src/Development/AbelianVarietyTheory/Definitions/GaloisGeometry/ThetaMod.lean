import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub

noncomputable section

namespace GlobalTheory.NPin

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 400000 in

structure Pin (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) where
  cf : CharFrame D
  C : NChoice D
  tp : TupTied D cf C
  chr : NCharTied D cf C tp
  val : ValLL0 D cf
  Q_eq : ∀ i, D.nd.Q i = C.Q (D.nd.w i)
  T : WDTie D.nd D.naut
  lab : LabTrue D T
  cg : CGTrue hL D T
  M : MtFam D
  H : HeckeOpen D M tp.tup
  au : AUTrue hL D T H.au
  rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r
  rep_inj : ∀ σ σ', (rep σ).Iso (rep σ') → σ = σ'
  row : ∀ i, RowTrue hL D rep (fun σ w => T.e w (D.naut.locW i σ w)) (D.naut.satW i)
  locW_eq : ∀ i i' σ w, D.naut.locW i σ w = D.naut.locW i' σ w
  jE : D.host.E →+* Qb
  ty : TypesOpen D jE
  wd : WDSide D T
  wdOf : ∀ (i : D.nd.Loc) a (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) w,
    D.naut.wdOf i r w = wd.wdOf (D.nd.l i) (D.naut.iotaQC i) r w ∧
    (D.naut.IsCrysW i r w ↔ wd.IsCrysW (D.nd.l i) (D.naut.iotaQC i) r w) ∧
    (D.naut.IsPotCrysW i r w ↔ wd.IsPotCrysW (D.nd.l i) (D.naut.iotaQC i) r w) ∧
    (D.naut.IsdRW i r w ↔ wd.IsdRW (D.nd.l i) (D.naut.iotaQC i) r w) ∧
    ∀ τ, D.naut.jumpsW i r τ = wd.jumpsW (D.nd.l i) (D.naut.iotaQC i) r τ

def rcAt (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (w : PlE D.host) (n : ℕ) (π : Irr (w.adicCompletion D.host.E) n) :
    GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w) :=
  GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls π.toIrrRep)

def IsComp {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E))
    (ξ : (w.adicCompletion E)ˣ →* ℂˣ) : Prop :=
  IsSmoothChar ξ ∧ ∀ x : Eˣ, ξ (Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom x) = χ.locK w x

structure IsTrue {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (P : Pin hL D) (S : Reading P.T) : Prop where
  rc : ∀ i w hw, (S i w hw).rc = rcAt hL D w
  row : ∀ i (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w) σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ →
    IsLocS (P.rep σ).S s ((S i s.w hw).row σ).toIrrRep
  rep : ∀ i (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w) Q,
    IsLocS (n := D.R.nV) (P.H.av.S i Q) s ((S i s.w hw).rep Q).toIrrRep
  mu : ∀ i w hw (j : Fin D.R.m), j.1 + 1 = D.nd.j i → IsComp (P.tp.tup (D.nd.mu i) j) w (S i w hw).mu
  eta : ∀ i w hw, IsComp P.cf.eta w (S i w hw).eta

def MtForm (D : D7) (M : MtFam D) (i : D.nd.Loc) : Prop :=
  ∃ B : (GAf D.host.E D.R.nV → (M.loc i).wt.W) →ₗ⋆[ℂ] (GAf D.host.E D.R.nV → (M.loc i).wt.W) →ₗ[ℂ] ℂ,
    (∀ f ∈ NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ, ∀ f' ∈ NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ,
      B f f' = starRingEnd ℂ (B f' f) ∧ (f ≠ 0 → 0 < (B f f).re) ∧
        ∀ h, B (NG.rt D.host.E D.R.nV h f) (NG.rt D.host.E D.R.nV h f') = B f f') ∧
    ∀ x y, inner ℂ x y = B ((M.loc i).real x) ((M.loc i).real y)

structure RowMod (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (j : ℕ) : Type 1 where
  A : Type
  [acg : AddCommGroup A]
  [mod : Module ℂ A]
  ρ : GAf D.host.E D.R.r →* Module.End ℂ A
  C : Submodule ℂ A
  B : A → A → ℂ
  lin : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z
  herm : ∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)
  pos : ∀ x ∈ C, x ≠ 0 → 0 < (B x x).re
  stab : ∀ h, ∀ x ∈ C, ρ h x ∈ C
  inv : ∀ h, ∀ x ∈ C, ∀ y ∈ C, B (ρ h x) (ρ h y) = B x y
  smooth : ∀ x ∈ C, ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → ρ κ x = x
  adm : ∀ N : ℕ, 0 < N →
    FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → ρ κ x = x})
  φ : D.what₂.Mj j →ₗ[ℂ] A
  φ_mem : ∀ y, φ y ∈ C
  φ_inner : ∀ x y, inner ℂ x y = B (φ x) (φ y)
  isot : ∀ σ y, y ∈ D.what₂.isot j σ ↔ φ y ∈ Formalism.IndefR.principalLevelFrame.isotIn (D := D) ρ C (rep σ)

attribute [instance] RowMod.acg RowMod.mod

def IsLinAt {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ} {Ω : Type} [AddCommGroup Ω] [Module ℂ Ω]
    (ω : GAf E n × GAf E r →* Module.End ℂ Ω) (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ)
    (ι : SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Ω) : Prop :=
  ∃ c : s.v.adicCompletion (maximalRealSubfield E) ≃+* s.w.adicCompletion E, Continuous c ∧
    (∀ x : E, c (s.i x) = algebraMap E (s.w.adicCompletion E) x) ∧
    ∀ (h : GAf E n) (g : GAf E r), TrivOutside {s.v} h → TrivOutside {s.v} g →
      ∀ Φ Φ' : SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)),
      (Φ' : Matrix (Fin n) (Fin r) (s.w.adicCompletion E) → ℂ) =
        om μ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g)) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) Φ →
      ω (h, g) (ι Φ) =
        ((η (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h))) : ℂˣ) : ℂ) • ι Φ'

structure ThetaMod (D : D7) (M : MtFam D) (i : D.nd.Loc) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (X : RowMod D rep (D.nd.j i)) (μ η : HChar D.host.E) : Type 1 where
  Ω : Type
  [acg : AddCommGroup Ω]
  [mod : Module ℂ Ω]
  ω : GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ Ω
  Λ : Ω →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ) →ₗ[ℂ] ↥X.C →ₗ⋆[ℂ] ℂ
  inv : ∀ h g φ (F F' : ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)) (y y' : ↥X.C),
    (F' : GAf D.host.E D.R.nV → (M.loc i).wt.W) = NG.rt D.host.E D.R.nV h F → (y' : X.A) = X.ρ g y →
    Λ (ω (h, g) φ) F' y' = Λ φ F y
  φ₀ : Ω
  read : ∀ x y (F : ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)),
    (F : GAf D.host.E D.R.nV → (M.loc i).wt.W) = (M.loc i).real x →
    inner ℂ y (D.what₂.thetaP (D.nd.mu i) (D.nd.j i) x) = Λ φ₀ F ⟨X.φ y, X.φ_mem y⟩
  loc : ∀ (s : SplitPlace D.host.E) μw ηw, IsComp μ s.w μw → IsComp η s.w ηw →
    φ₀ ∈ ⨆ (ι : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] Ω)
      (_ : IsLinAt ω s μw ηw ι), LinearMap.range ι

structure Join {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (P : Pin hL D) : Type 1 where
  form : ∀ i, MtForm D P.M i
  rowM : ∀ i : D.nd.Loc, RowMod D P.rep (D.nd.j i)
  th : ∀ (i : D.nd.Loc) (j : Fin D.R.m), j.1 + 1 = D.nd.j i →
    ThetaMod D P.M i (rowM i) (P.tp.tup (D.nd.mu i) j) P.cf.eta

end GlobalTheory.NPin

end
