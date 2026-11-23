import Formalism.LocalToGlobal.HermitianForms.TiedTwPGen

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

def okPT (D : D7) (Q : Finset (HeightOneSpectrum (𝓞 D.host.F))) (T : ℕ) (w : D.what₂.places.Pl) : Prop :=
  okQ D Q w ∨ D.what₂.places.resChar w = T

set_option maxHeartbeats 4000000 in

structure TwistedTiltedData {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {F : ∀ u, FormsTied D u} {W : TwFormsTied D Tw T F}
    (Lv : TwistedLevelData W) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) (h1 : 1 ≤ D.R.m)
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

structure TwPTied {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {F : ∀ u, FormsTied D u} {W : TwFormsTied D Tw T F}
    (Lv : TwistedLevelData W) where

  cls : ∀ u μ, μ ≠ D.what₂.mu0 → ClassesAtPrimes (Tw.fm u μ) (badQ D (T.Q μ))

  Lb : ∀ u μ hμ, (cls u μ hμ).lev.Lb = (F u).clsP.lev.Lb

  chi_fin : ∀ u μ hμ, ∃ n : ℕ, 0 < n ∧ ∀ κ, (cls u μ hμ).lev.chi κ ^ n = 1

  val : ∀ u μ hμ, ValuationAtPrimes (cls u μ hμ) (okPT D (T.Q μ) (D.mem u).A.T)

  norm : ∀ u μ hμ, NormPTieG (val u μ hμ)

  til : ∀ u μ hμ (h1 : 1 ≤ D.R.m), TwistedTiltedData Lv u μ hμ h1 (cls u μ hμ)

structure TwPAtG {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {F : ∀ u, FormsTied D u} {W : TwFormsTied D Tw T F}
    {Lv : TwistedLevelData W} (P : TwPTied Lv) : Prop where
  Uloc_g : ∀ u μ hμ v, v ∈ badG D → (P.cls u μ hμ).lev.Uloc v = (F u).clsP.lev.Uloc v
  chi_g : ∀ u μ hμ (κ : (P.cls u μ hμ).lev.U) (κ' : (F u).clsP.lev.U), κ.1 = κ'.1 →
    (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) → (P.cls u μ hμ).lev.chi κ = (F u).clsP.lev.chi κ'

theorem TwPTied.latT {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {F : ∀ u, FormsTied D u} {W : TwFormsTied D Tw T F}
    {Lv : TwistedLevelData W} (P : TwPTied Lv) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) (w : D.what₂.places.Pl)
    (hw : D.what₂.places.resChar w = (D.mem u).A.T) (x : (Tw.fm u μ).ptLat.V) :
    x ∈ (Tw.fm u μ).SP w ↔
      ∀ (c : (Tw.fm u μ).clsP) (B : GL (Fin (D.R.N D.R.m - 1)) D.host.E),
        IsLocBasis (D.what₂.places.resChar w) ((P.cls u μ hμ).lat c : Set _) B →
        ∃ Pc ∈ IntSpan D w (Tw.fm u μ).sg, (P.val u μ hμ).eW ((Tw.fm u μ).ptEmb x) c =
          fnOf _ (shiftOf (sgTG (Tw.fm u μ))) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N D.R.m - 1)) D.host.E).1) Pc :=
  (P.val u μ hμ).lat w (Or.inr hw) x

theorem TwPTied.sg_eq {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {F : ∀ u, FormsTied D u} {W : TwFormsTied D Tw T F}
    {Lv : TwistedLevelData W} (P : TwPTied Lv) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) :
    (Tw.fm u μ).sg = (D.fm u).sg := by
  funext τ
  have h : ((Tw.fm u μ).sg τ).w = ((D.fm u).sg τ).w := by
    funext i
    have h1 := (P.val u μ hμ).sg τ i
    have h2 := (F u).valP.sg τ i
    exact_mod_cast h1.trans h2.symm
  cases h1 : (Tw.fm u μ).sg τ
  cases h2 : (D.fm u).sg τ
  simp only [h1, h2] at h
  subst h
  rfl

end Formalism.L2.Forms

end
