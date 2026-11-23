import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimFieldBaseChangeLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeNonnegOfCurveDegreeNonnegOverZmod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefFieldDescent

theorem interNum_one_nonneg_of_isNef {k : Type} [Field k] {V : Scheme.{0}} [Algebra k Γ(V, ⊤)]
    (hp : IsProjOver (strHom k V)) (hd : topologicalKrullDim V ≤ 1) {N : LB V} (hN : IsNef k N) :
    0 ≤ interNum k (GlobalTheory.structureModule V) ![N] := by
  refine CurveDevissage.interNum_one_nonneg hp hd hN.isLB (fun Z i hi hZ _ ha hdZ => ?_) _ inferInstance
  have hpr : IsProper (strHom k V) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  have h := (isNef_iff_isClosedImmersion.1 hN).2 Z i hi hZ hdZ inferInstance
  rw [interNumOn, interNum_pushforward_of_isClosedImmersion ha _ (isLB_vecOne hN.isLB)] at h
  rw [topSelf_def]
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j; rfl

theorem isNef_of_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → ∀ L : LB Y, L.IsLB → (letI := algebraΓOfHom q; IsNef E (L.pull π)) → (letI := algebraΓOfHom p; IsNef k L) := by
  intro k E _ _ _ Y X p q π H hp L hL hN
  letI := algebraΓOfHom p
  letI := algebraΓOfHom q
  refine ⟨hL, fun C hC => ?_⟩
  have H₁ : IsPullback (pullback.fst (redι C) π) (pullback.snd (redι C) π ≫ q) (redι C ≫ p)
      (spMap (algebraMap k E)) := (IsPullback.of_hasPullback (redι C) π).paste_vert H
  have hpC : IsProjOver (redι C ≫ p) := ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
  have hpr : IsProper (redι C ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hpC).1
  have hp' := ProjSpace.isProjOver_of_isPullback_spMap _ H₁ hpC
  have hd : topologicalKrullDim (pullback (redι C) π : Scheme.{0}) ≤ 1 :=
    (FieldExtDim.topologicalKrullDim_baseChange_le k E _ _ _ _ _ H₁).trans
      ((topologicalKrullDim_red C).trans hC.2).le
  have hLC := LB.isLB_pull hL (redι C)
  have key := FieldChangeInter.interNum_pull H₁ (isLB_vecOne hLC)
  letI := algebraΓOfHom (pullback.snd (redι C) π ≫ q)
  have hN' : IsNef E ((L.pull π).pull (pullback.snd (redι C) π)) :=
    hN.pull_of_isClosedImmersion _ fun _ => rfl
  have h0 := interNum_one_nonneg_of_isNef (k := E)
    (by rw [strHom_eq (f := pullback.snd (redι C) π ≫ q) fun _ => rfl]; exact hp') hd hN'
  rw [interNumRed_one_eq hL]
  refine (h0.trans_eq ?_).trans_eq key
  refine interNum_congr_cls E _ (isLB_vecOne hN'.isLB)
    (fun i => LB.isLB_pull (isLB_vecOne hLC i) _) fun i => ?_
  fin_cases i
  change pull _ (pull π (cls L hL)) = pull _ (pull (redι C) (cls L hL))
  simp only [← pull_comp, pullback.condition]

end GlobalTheory.NefFieldDescent
