import Formalism.LocalToGlobal.HermitianForms.TiedTwSym
import Formalism.LocalToGlobal.HermitianForms.TiedTwP

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

variable {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

set_option maxHeartbeats 4000000 in

structure SymmetricTwistedTiltedData {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} {W : TwFormsTiedS D Tw T J F}
    (Lv : SymmetricTwistedLevelData W) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) (h1 : 1 ≤ D.R.m)
    (K : ClassesAtPrimes (Tw.fm u μ) (badQ D (T.Q μ))) where
  z0 : Fin (D.R.N D.R.m) → D.host.E
  lastCoordinateUniformizerVector_spans_orthogonal_line : ∃ a : D.host.E, z0 = a • zc D
  hermitianForm_lastCoordinateUniformizerVector_self : hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) z0 z0 = ((D.mem u).A.T : D.host.E)
  ga : (Tw.fm u μ).clsP → UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
  til_lat : ∀ c, mulLat (ga c).1.1 (latCrd D D.R.m le_rfl (T.lat u μ D.R.m ((Tw.fm u μ).til c))) =
    (K.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0}
  til_fv : ∀ v c (x : ↥(LdG D D.R.m le_rfl (latCrd D D.R.m le_rfl (T.lat u μ D.R.m ((Tw.fm u μ).til c))))) (r : 𝓞 D.host.E),
    (r : D.host.E) = hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) z0 ((ga c).1.1 *ᵥ x.1) →
    (Tw.fm u μ).fv D.R.m v ((Tw.fm u μ).til c) ((Lv.lv u μ hμ D.R.m h1 le_rfl).pr v _ x) = (W.atT u μ).res (F u).atT v r

  stabMap : ∀ c s, IsExt D z0 (RingHom.id D.host.E) (K.stabI c s).1.1
    ((ga c).1.1 * ((W.ch u μ hμ D.R.m h1 le_rfl (T.chOf u μ D.R.m ((Tw.fm u μ).til c))).stabI ⟨(Tw.fm u μ).til c, rfl⟩
      ((Tw.fm u μ).stabMap c s)).1.1 * ((ga c)⁻¹).1.1)

  ka : ∀ c, (W.ch u μ hμ D.R.m h1 le_rfl (T.chOf u μ D.R.m ((Tw.fm u μ).til c))).lev.U
  til_ad : ∀ c (g : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    IsExt D z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (K.y c).1.1 g.1 →
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (ga c).1 *
      ((W.ch u μ hμ D.R.m h1 le_rfl (T.chOf u μ D.R.m ((Tw.fm u μ).til c))).y ⟨(Tw.fm u μ).til c, rfl⟩).1 = g * (ka c).1

set_option maxHeartbeats 4000000 in

structure TwPTiedS {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} {W : TwFormsTiedS D Tw T J F} (Lv : SymmetricTwistedLevelData W) where

  cls : ∀ u μ, μ ≠ D.what₂.mu0 → ClassesAtPrimes (Tw.fm u μ) (badQ D (T.Q μ))

  Lb : ∀ u μ hμ, (cls u μ hμ).lev.Lb = (F u).clsP.lev.Lb

  chi_fin : ∀ u μ hμ, ∃ n : ℕ, 0 < n ∧ ∀ κ, (cls u μ hμ).lev.chi κ ^ n = 1

  val : ∀ u μ hμ, ValuationAtPrimes (cls u μ hμ) (okPT D (T.Q μ) (D.mem u).A.T)

  norm : ∀ u μ hμ, NormPTieG (val u μ hμ)

  til : ∀ u μ hμ (h1 : 1 ≤ D.R.m), SymmetricTwistedTiltedData Lv u μ hμ h1 (cls u μ hμ)

structure TwPAtGS {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} {W : TwFormsTiedS D Tw T J F} {Lv : SymmetricTwistedLevelData W} (P : TwPTiedS Lv) : Prop where
  Uloc_g : ∀ u μ hμ v, v ∈ badG D → (P.cls u μ hμ).lev.Uloc v = (F u).clsP.lev.Uloc v
  chi_g : ∀ u μ hμ (κ : (P.cls u μ hμ).lev.U) (κ' : (F u).clsP.lev.U), κ.1 = κ'.1 →
    (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) → (P.cls u μ hμ).lev.chi κ = (F u).clsP.lev.chi κ'

set_option maxHeartbeats 4000000 in

structure TwPEvzS {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} {W : TwFormsTiedS D Tw T J F} {Lv : SymmetricTwistedLevelData W} (P : TwPTiedS Lv) where
  eWz : ∀ u μ, (D.PTw u μ).Wz ≃ₗ[ℂ] ((Tw.fm u μ).clsP → (D.chTw u μ).Y D.R.m → ℂ)
  evz : ∀ u μ (hμ : μ ≠ D.what₂.mu0) (h1 : 1 ≤ D.R.m) (φ : (D.chTw u μ).cls D.R.m → (D.chTw u μ).Y D.R.m → ℂ) c s s',
    IsTr (atInf (embT D) ((P.til u μ hμ h1).ga c).1.1) (twYS T F u μ D.R.m le_rfl s') (twYS T F u μ D.R.m le_rfl s) →
    eWz u μ ((D.PTw u μ).evz φ) c s =
      ((((W.ch u μ hμ D.R.m h1 le_rfl (T.chOf u μ D.R.m ((Tw.fm u μ).til c))).lev.chi ((P.til u μ hμ h1).ka c))⁻¹ : ℂˣ) : ℂ) *
        φ ((Tw.fm u μ).til c) s'
  jM : ∀ u μ, (D.PTw u μ).Mt →ₛₗ[starRingEnd ℂ] (D.PTw u μ).Wrow
  per : ∀ u μ, μ ≠ D.what₂.mu0 →
    (∀ z ∈ (Tw.fm u μ).ptC, ∃ G, jM u μ G = z) ∧ (∀ G, jM u μ G ∈ (Tw.fm u μ).ptC) ∧
      ∀ w G, (D.PTw u μ).period w G = (Tw.fm u μ).ipP (jM u μ G) w

theorem TwPTiedS.sg_eq {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} {W : TwFormsTiedS D Tw T J F} {Lv : SymmetricTwistedLevelData W} (P : TwPTiedS Lv)
    (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) :
    (Tw.fm u μ).sg = (D.fm u).sg := by
  funext τ

  have hw : ((Tw.fm u μ).sg τ).w = ((D.fm u).sg τ).w := by
    funext i
    have h1 := (P.val u μ hμ).sg τ i
    have h2 := (F u).valP.sg τ i
    exact_mod_cast h1.trans h2.symm
  revert hw
  generalize (Tw.fm u μ).sg τ = a
  generalize (D.fm u).sg τ = b
  intro hw
  cases a
  cases b
  cases hw
  rfl

end Formalism.L2.Forms

end
