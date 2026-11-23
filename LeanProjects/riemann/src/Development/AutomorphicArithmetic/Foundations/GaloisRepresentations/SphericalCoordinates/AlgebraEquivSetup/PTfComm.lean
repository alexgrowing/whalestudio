import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem comm_conv (hRing : ConvRing) {X : Type} [Group X] {K : Subgroup X} (hK : IsCommensurated K)
    {f g h : X → ℂ} (hf : f ∈ Hecke ℂ K) (hg : g ∈ Hecke ℂ K) (hh : h ∈ Hecke ℂ K)
    (c₁ : conv K f h = conv K h f) (c₂ : conv K g h = conv K h g) :
    conv K (conv K f g) h = conv K h (conv K f g) := by
  calc conv K (conv K f g) h = conv K f (conv K g h) := (hRing X K hK f hf g hg).2 h hh
    _ = conv K f (conv K h g) := by rw [c₂]
    _ = conv K (conv K f h) g := ((hRing X K hK f hf h hh).2 g hg).symm
    _ = conv K (conv K h f) g := by rw [c₁]
    _ = conv K h (conv K f g) := (hRing X K hK h hh f hf).2 g hg

private theorem comm_cen (hAdm : TfAdm) (hCen : TfMulCen) (hRing : ConvRing) {X M : Type} [Group X] [Group M]
    (T : TyLev X M) {a b z z' : X} (ha : T.L.pr a = 1) (hb : T.L.pr b = 1) (hz : T.Cen z) (hz' : T.Cen z')
    (hab : conv T.K₀ (T.tf a) (T.tf b) = conv T.K₀ (T.tf b) (T.tf a)) :
    conv T.K₀ (T.tf (a * z)) (T.tf (b * z')) = conv T.K₀ (T.tf (b * z')) (T.tf (a * z)) := by
  have hK := T.cms
  have mA := (hAdm X M T a ha).1.1
  have mB := (hAdm X M T b hb).1.1
  have mZ := (hAdm X M T z hz.2).1.1
  have mZ' := (hAdm X M T z' hz'.2).1.1
  have cz := hCen X M T a z ha hz
  have cz' := hCen X M T b z' hb hz'
  have eBZ : conv T.K₀ (T.tf b) (T.tf z) = conv T.K₀ (T.tf z) (T.tf b) :=
    (hCen X M T b z hb hz).2.trans (hCen X M T b z hb hz).1.symm
  have eAZ' : conv T.K₀ (T.tf a) (T.tf z') = conv T.K₀ (T.tf z') (T.tf a) :=
    (hCen X M T a z' ha hz').2.trans (hCen X M T a z' ha hz').1.symm
  have eZZ' : conv T.K₀ (T.tf z) (T.tf z') = conv T.K₀ (T.tf z') (T.tf z) :=
    (hCen X M T z z' hz.2 hz').2.trans (hCen X M T z z' hz.2 hz').1.symm
  have mAZ := (hRing X T.K₀ hK _ mA _ mZ).1
  have h1 := comm_conv hRing hK mA mZ mB hab eBZ.symm
  have h2 := comm_conv hRing hK mA mZ mZ' eAZ' eZZ'
  have h3 := comm_conv hRing hK mB mZ' mAZ h1.symm h2.symm
  rw [← cz.2, ← cz'.2]
  exact h3.symm

theorem UpperTheory.Gal.W2.Seed.pTfComm : TfAdm → ConvRing → TfMulCen → TfMulL → TfMulR → TfLoc → TfComm := by
  intro hAdm hRing hCen hL hR hLoc X M M' M'' _ _ _ _ T L' Kw hF hAp z z' hz hz' t
  refine ⟨fun L'' t' h1 h2 => ?_, fun t' hc => ?_⟩
  · have ha : T.L.pr (L'.loc t) = 1 := hAp.1 t
    have hb : T.L.pr (L''.loc t') = 1 := h1.1 t'
    have hb' : L'.pr (L''.loc t') = 1 := h2.1 t'
    exact comm_cen hAdm hCen hRing T ha hb hz hz'
      ((hL X M M' T L' Kw hF hAp t _ hb hb').trans (hR X M M' T L' Kw hF hAp t _ hb hb').symm)
  · have ha : T.L.pr (L'.loc t) = 1 := hAp.1 t
    have hb : T.L.pr (L'.loc t') = 1 := hAp.1 t'
    refine comm_cen hAdm hCen hRing T ha hb hz hz' ?_
    funext g
    rw [hLoc X M M' T L' Kw hF hAp t t' g, hLoc X M M' T L' Kw hF hAp t' t g, hc]
