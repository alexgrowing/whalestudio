import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSmoothProjectiveVarietyProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleBaseChangeFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingOfNadelPairsStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VanishEmbedded

open GlobalTheory.HSCore.VanishNumberField

theorem subsingleton_coh_canon_tens : GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingPair → ∀ (F : Type) [Field F], Nonempty (F →+* ℂ) → ∀ (X : Scheme.{0}) (p : X ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → ∀ (K : CanonLB p D) (N : LB X), (letI := algebraΓOfHom p; IsNef F N) → (letI := algebraΓOfHom p; IsBig F N) → ∀ q : ℕ, 0 < q → Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  intro hNum hNad F _ ⟨σ⟩ X p D hsm hp hgc K N hnef hbig q hq
  letI := σ.toAlgebra
  let X' := pullback p (spMap (algebraMap F ℂ))
  let π : X' ⟶ X := pullback.fst _ _
  let p' : X' ⟶ Sp ℂ := pullback.snd _ _
  have H : IsPullback π p' p (spMap (algebraMap F ℂ)) := IsPullback.of_hasPullback _ _
  obtain ⟨hI, -, hsm', hp', -⟩ := GlobalTheory.BaseChangeVariety.baseChange_props F ℂ X X' p p' π D H hp hgc
  haveI : Nonempty X := ⟨π (Classical.arbitrary X')⟩
  letI := algebraΓOfHom p
  letI := algebraΓOfHom p'
  obtain ⟨hprop, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have hL := LB.isLB_pull hnef.isLB π
  have hnef' : IsNef ℂ (N.pull π) := GlobalTheory.NefFieldExt.isNef_baseChange hNum F ℂ X X' p p' π H hp N hnef
  have hbig' : IsBig ℂ (N.pull π) := by
    obtain ⟨D₀, hD₀, c, hc, hm⟩ := hbig.3
    have hD : topologicalKrullDim X = D := topologicalKrullDim_eq_of_smooth p D hsm
    obtain rfl : D₀ = D := by exact_mod_cast hD₀.symm.trans hD
    refine (isBig_iff (f := p') (fun _ => rfl) hp'
      (topologicalKrullDim_eq_of_smooth _ D₀ hsm')).2 ⟨hL, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ ?_)⟩
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL m) (LB.isLB_pull (isLB_lbPow hbig.1 m) π)
      (by rw [cls_lbPow hL, cls_pull hbig.1, cls_pull (isLB_lbPow hbig.1 m), cls_lbPow hbig.1, map_nsmul])]
    exact (FieldChangeInter.hdim_pull H (isLB_lbPow hbig.1 m) 0).symm
  have hKV := GlobalTheory.T.kawamataViehweg_vanishing_of_nadel_pairs hNad X' p' D hp' hI (K.baseChange H) (N.pull π) hnef' hbig' q hq
  have hM : (tens K.bundle N).IsLB := isLB_tens K.isLB hnef.isLB
  have hK' := LB.isLB_pull K.isLB π
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (structureModule X') (LB.isLB_pull hM π) (isLB_tens hK' hL)
    (by rw [cls_pull hM π, cls_tens K.isLB hnef.isLB, cls_tens hK' hL, cls_pull K.isLB π, cls_pull hnef.isLB π, map_add])
  exact subsingleton_coh_of_pull (f := p) (f' := p') H hM q
    ((cohOn.mapIso Γ(X', ⊤) ⊤ q i).toEquiv.subsingleton_congr.2 hKV)

end GlobalTheory.VanishEmbedded
