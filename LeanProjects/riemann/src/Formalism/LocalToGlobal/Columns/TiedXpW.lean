import Formalism.LocalToGlobal.Columns.TiedXpU

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (hQ : PtSurj d)

theorem ufGL_tilMv (u : d.what₂.Word) (c : PCl d) :
    ufGL d.X.E (d.R.N d.R.m) (d.tilMv u c).1 = (d.tilGa u c).1 := by
  have h := vfi_ufGL_ratHom d.sp.cm (d.R.N d.R.m) (d.tilGa u c)
  have e : ratHom d.sp.cm (d.R.N d.R.m) (d.tilGa u c) = (d.tilMv u c).1 :=
    (ratEquiv d.sp.cm (d.R.N d.R.m)).apply_symm_apply _
  rw [e] at h
  exact h

theorem chi_ka (u : d.what₂.Word) (hM : TilMove a u) (c : PCl d) :
    ((((classAgreement a hS hH hQ u d.R.m le_rfl).lev.chi ((tilAd a hS hH hP hQ u hM).ka c))⁻¹ : ℂˣ) : ℂ) =
      d.σ₀ (((d.lev d.R.m).chr (d.tilMv u c).2 : d.X.Kˣ) : d.X.K) := by
  have h1 := xp_clsG_chi d.sp.cm d.hX d.hPr d.σ₀ u (d.lev d.R.m) (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m) (d.repr u d.R.m)
    (hQ u d.R.m) (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.spec c) (stepCrd a hS hH u d.R.m le_rfl)
    ((tilAd a hS hH hP hQ u hM).ka c) (hM c).choose.2
  have h2 : (classAgreement a hS hH hQ u d.R.m le_rfl).lev.chi ((tilAd a hS hH hP hQ u hM).ka c) =
      levTyp ((Units.map d.σ₀.toMonoidHom).comp (d.lev d.R.m).chr) (hM c).choose := h1
  rw [h2, ← map_inv, vfi_typ d.sp.cm d.σ₀ (d.lev d.R.m), inv_inv, (hM c).choose_spec.1]

theorem evz_core (u : d.what₂.Word) (c : PCl d) (s s' : FrS d.X d.σ₀ (d.R.N d.R.m))
    (h : IsTr (atInf (embAt d.σ₀ d.X.emb) (d.tilGa u c).1.1) s' s) :
    frMul d.σ₀ (ufGL d.X.E (d.R.N d.R.m) (d.tilMv u c).1)⁻¹ s = s' := by
  rw [ufGL_tilMv]
  exact vfi_frMul_of_isTr d.σ₀ _ s s' h

theorem evzTied (u : d.what₂.Word) (hM : TilMove a u)
    (W : CF.ValTied (D := d.colRec a) u (atTTied a hH u).eV d.R.m le_rfl (classAgreement a hS hH hQ u d.R.m le_rfl))
    (hW : ∀ s, (W.eY s).1 = s.1) :
    CF.EvzTie (tilAd a hS hH hP hQ u hM) W (tieEWz a u) := by
  intro φ c s s' hTr
  have hs : frMul d.σ₀ (ufGL d.X.E (d.R.N d.R.m) (d.tilMv u c).1)⁻¹ s = s' := by
    refine evz_core u c s s' fun τ => ?_
    have h := hTr τ
    have e1 := congrFun (hW s) τ
    have e2 := congrFun (hW s') τ
    have e3 := embT_eq a hH
    rw [e1, e2, e3] at h
    exact h
  refine Eq.trans ?_ (congrArg (fun t => t * φ (((d.colRec a).fm u).til c) s') (chi_ka a hS hH hP hQ u hM c).symm)
  refine Eq.trans ?_ (congrArg (fun t => d.σ₀ (((d.lev d.R.m).chr (d.tilMv u c).2 : d.X.Kˣ) : d.X.K) *
    φ (((d.colRec a).fm u).til c) t) hs)
  rfl

end Rec

end Formalism.L2.Col
