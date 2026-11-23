import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def conjId (D : D7) : (AE D)ˣ →* (AE D)ˣ := Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom

def IsHeckeCharF (D : D7) (χ : (AF D.host.F)ˣ →* Circle) : Prop :=
  Continuous χ ∧ ∀ a : D.host.Fˣ, χ (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom a) = 1

structure ConjDat {D : D7} (V : HSp D) where
  P : Matrix (Fin V.rank) (Fin V.rank) D.host.E
  rel : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * V.gram * P =
    V.gram.map (D.sp.cm.sig : D.host.E →+* D.host.E)
  aut : GA D V ≃* GA D V
  aut_mt : ∀ g, HMul.hMul (mt V (aut g)) (P.map (incA D)) = HMul.hMul (P.map (incA D)) (cM (mt V g))

structure LocWTied (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (L : Formalism.MainNotions.KudlaSiegelWeil.LocW D X) where

  sR : L.sR = true

  eG : ∀ V, L.G V ≃* GA D V
  eG_meas : ∀ V, Measurable (eG V)

  gf : ∀ V g, g ∈ L.GF V ↔ eG V g ∈ GQ V

  muC : HSp D → ℝ
  muC_pos : ∀ V, 0 < muC V

  mu : ∀ V : HSp D, V.SigOK → ∀ μ 𝓕, IsVolPair D V μ 𝓕 →
    Measure.map (eG V) (L.μG V) = ENNReal.ofReal (muC V) • μ

  cj : ∀ V : HSp D, ConjDat V

  om : ∀ (V W : HSp D) χ χ' g h, V.rank ≠ W.rank → L.om V W χ χ' (g, h) =
    if V.rank < W.rank then Wl.om V W χ χ' ((cj V).aut (eG V g), eG W h)
    else Wl.om V W χ χ' (eG V g, (cj W).aut (eG W h))

  thF : ∀ V W Φ, L.thF V W Φ = Wl.evS V W Φ 0

  eChrF : L.ChrF →* ((AF D.host.F)ˣ →* Circle)
  eChrF_inj : Function.Injective eChrF
  eChrF_mem : ∀ χ, IsHeckeCharF D (eChrF χ)

  res : ∀ χ a, eChrF (L.res χ) a = T.eChr χ (idF D a)

  eta : IsEta D (eChrF L.eta)

  cc : ∀ χ x, T.eChr (L.cc χ) x = T.eChr χ (conjId D x)

def LocalWhittakerKFiniteCompatibility {D : D7} {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T} {L : Formalism.MainNotions.KudlaSiegelWeil.LocW D X}
    (h : LocWTied D X T Wl L) (Kf : KfinTied Wl) : Prop :=
  AllSome (IsInfFam (D := D)) fun θ => ∀ V : HSp D, V.SigOK →
    (∀ g, g ∈ L.Gk V ↔ ∃ a ∈ GfC V, ∃ k, IsKinf θ V (Kf.cpt V) k ∧ h.eG V g = a * k) ∧
    ∀ k, IsKinf θ V (Kf.cpt V) k → IsKinf θ V (Kf.cpt V) ((h.cj V).aut k)

def CjOfBas {D : D7} {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T} {L : Formalism.MainNotions.KudlaSiegelWeil.LocW D X}
    (h : LocWTied D X T Wl L) (Kf : KfinTied Wl) : Prop :=
  ∀ V : HSp D, V.SigOK → (h.cj V).P * (Kf.bas V).map (D.sp.cm.sig : D.host.E →+* D.host.E) = Kf.bas V

theorem LocWTied.ePlus {D : D7} {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T} {L : Formalism.MainNotions.KudlaSiegelWeil.LocW D X}
    (h : LocWTied D X T Wl L) (τ : D.what₂.Tau) : Formalism.MainNotions.KudlaSiegelWeil.ePlus L τ :=
  ⟨fun _ => h.sR, fun _ => xi_zero_im_pos D τ⟩

end Formalism.L2.Theta

end
