import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc

namespace Formalism.L2.SG.NGData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Def

variable {D : D7}

def NRat {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {n | n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ j, ∀ x ∈ Xflag F (j + 1), n x - x ∈ Xflag F j) ∧
    (∀ x ∈ orth (VS D) (Xsp F), n x - x ∈ Xsp F)}

abbrev NuC (D : D7) : Type := Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)

variable {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

def nmlOf (t : TauC Y u u') : NuC D :=
  {δ | ∃ n ∈ NRat (lf D (X.Fu u)), ∃ n' ∈ NRat (lf D (X.Fu u')), δ = n * t.lin * n'}

def Jw (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (w : Point D.host.E (D.R.rS + 1)) : X.Vpi u' →L[ℂ] X.Vpi u :=
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  ((scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) •
    OO (νq (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' w)

def J2of (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (γ : PN.Pts D.host.E D.R.rS) : ℝ :=
  if h : ∃ w : Point D.host.E (D.R.rS + 1), toPts w = γ ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g then
    ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' νq h.choose)‖ ^ 2
  else 0

def grpC (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :=
  ∑' t : TauC Y u u', ((Y.tO u u').ngSet ∩ {t | clsOf Y u u' t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = ν}).indicator
    (Y.tO u u').vec t

def a2C (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) : ℝ :=
  ‖grpC Y u u' c γ ν‖ ^ 2 / J2of Y u u' νq γ

def NOf2 (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) :
    PN.NGData (TauC Y u u') D.host.E D.R.rS (Set (TauC Y u u')) (NuC D) where
  cls := clsOf Y u u'
  pt := ptPN
  nml := nmlOf Y u u'
  a2 := a2C Y u u' νL
  J2loc := J2of Y u u' νL
  jacobianSquareBound := J2of Y u u' νB
  n := nPt D.host.rdE D.R.k ((Tu D u : ℕ) * (Tu D u' : ℕ))
  NG := NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ))
  ND := NDPt D.host.rdE
  Hh := HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u' : ℕ))
  ngen := ng

theorem grp_eq (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :
    PN.grp (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν = grpC Y u u' c γ ν := rfl

def AmpVanish (νL : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ c γ ν, J2of Y u u' νL γ = 0 → grpC Y u u' c γ ν = 0

theorem ampInput_of_vanish (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (h : AmpVanish Y u u' νL) : PN.AmpInput (Y.tO u u') (NOf2 Y u u' νL νB ng) := by
  have hJ : ∀ γ, 0 ≤ J2of Y u u' νL γ := by
    intro γ
    unfold J2of
    split_ifs
    · positivity
    · exact le_refl 0
  refine ⟨?_, ?_, ?_⟩
  · intro c γ ν
    show 0 ≤ a2C Y u u' νL c γ ν
    unfold a2C
    exact div_nonneg (by positivity) (hJ γ)
  · intro γ
    exact hJ γ
  · intro c γ ν
    show ‖grpC Y u u' c γ ν‖ ^ 2 ≤ a2C Y u u' νL c γ ν * J2of Y u u' νL γ
    unfold a2C
    by_cases h0 : J2of Y u u' νL γ = 0
    · rw [h c γ ν h0, h0]
      simp
    · rw [div_mul_cancel₀ _ h0]

end Def

section Cut

def NGCut2C : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ (C1 C0n A : ℕ) (CB CSt Cgs CTs : ℝ), 0 ≤ CB ∧ 0 ≤ CSt ∧ 0 ≤ Cgs ∧ 0 ≤ CTs ∧
    C1 + C0n + 38 ≤ A ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie X Y →
      ∃ (P : Type) (_ : Fintype P) (B : S3.MassData P) (cSt e1 Irat Ire : ℝ)
        (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        Formalism.L2.SG.RealObj.NuQOK X u u' νL ∧ Formalism.L2.SG.RealObj.NuQOK X u u' νB ∧
        (Y.tO u u').Gam1 = B.Gam1 ∧ B.d * B.d' / B.Dstar = ddC X Y u u' ∧ PN.NormInputs B ∧
        PN.FrameInputs B (2 * D.host.v) (X.B.g : ℝ) D.R.rS D.R.k D.R.f Irat Ire ∧
        PN.NGSizes Cgs CTs CSt D.R.rS D.R.f large₂.sc.b (2 * D.host.v) (X.B.g : ℝ)
          (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) cSt e1 ∧
        Formalism.L2.SG.RowsOther.NGFin (Y.tO u u') (NOf2 Y u u' νL νB ng) D.R.k D.R.f C1 C0n (2 * D.host.v)
          (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) e1 ∧
        Formalism.L2.SG.RowsOther.NGReal (Y.tO u u') (NOf2 Y u u' νL νB ng) D.R.f A CB large₂.sc.b cSt Ire

theorem counting_bound_of_joint_chain (hR : PN.RowNGJoint) (hC : PN.NGChain) (hc : NGCut2C) : RowNGC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, C0n, A, CB, CSt, Cgs, CTs, h1, h2, h3, h4, hA, C'₀, Cl₀, h⟩ := hc Cg cb Cw cT CT C0
  obtain ⟨Cn, hCn, hK⟩ := Formalism.L2.SG.RowsOther.rowNG_of_cut hR hC C1 C0n A CB CSt Cgs CTs h1 h2 h3 h4 hA
  refine ⟨Cn, hCn, C'₀, Cl₀, fun C' Cl a b D large₂ X Y u u' h0 hs hT ha => ?_⟩
  obtain ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, _, _, hG, hdd, hN, hF, hS, hFin, hRe⟩ :=
    h C' Cl a b D large₂ X Y u u' h0 hs hT
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u') _ _ _ _ (Y.tO u u') D.R.rS D.R.k (Set (TauC Y u u')) (NuC D)
    (NOf2 Y u u' νL νB ng) P B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ))
    cSt e1 Irat Ire
  rw [hcard] at key
  have r := key ha hG hN hF hS hFin hRe
  rw [hdd] at r
  exact r

end Cut

end Formalism.L2.SG.NGData
