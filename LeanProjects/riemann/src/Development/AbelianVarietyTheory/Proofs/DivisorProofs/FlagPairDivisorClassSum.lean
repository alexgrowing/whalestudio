import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoDivisorClassIsoInvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitResGEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoShortExactCompatStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsFrame Chart det)
open GlobalTheory.LB (resG_resG resG_self val_res)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.Vert

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : GlobalTheory.Vert.Model O}

theorem VertDiv.isSum_of_local {P P' P'' : VertDiv Z}
    (H : ∀ x : Z.X, ∃ (V : Z.X.Opens) (i : P.M.ι) (j : P'.M.ι) (k : P''.M.ι) (hi : V ≤ P.M.U i)
      (hj : V ≤ P'.M.U j) (hk : V ≤ P''.M.U k), x ∈ V ∧
      P''.eqn k (inf_le_inf_left Z.gen hk) =
        P.eqn i (inf_le_inf_left Z.gen hi) * P'.eqn j (inf_le_inf_left Z.gen hj)) :
    VertDiv.IsSum P P' P'' := by
  intro i j k
  have hi : P.M.U i ⊓ P'.M.U j ⊓ P''.M.U k ≤ P.M.U i := inf_le_left.trans inf_le_left
  have hj : P.M.U i ⊓ P'.M.U j ⊓ P''.M.U k ≤ P'.M.U j := inf_le_left.trans inf_le_right
  have hk : P.M.U i ⊓ P'.M.U j ⊓ P''.M.U k ≤ P''.M.U k := inf_le_right
  suffices h : ∀ (U : Z.X.Opens) (hi : U ≤ P.M.U i) (hj : U ≤ P'.M.U j) (hk : U ≤ P''.M.U k),
      ∃ u : Γ(Z.X, U)ˣ, P''.eqn k (inf_le_inf_left Z.gen hk) =
        resG Z.X inf_le_right u.val * (P.eqn i (inf_le_inf_left Z.gen hi) *
          P'.eqn j (inf_le_inf_left Z.gen hj)) from h _ hi hj hk
  intro U hi hj hk
  obtain ⟨w, hw⟩ := ((P.isUnit_eqn i (inf_le_inf_left Z.gen hi)).mul
    (P'.isUnit_eqn j (inf_le_inf_left Z.gen hj))).exists_left_inv
  have hf : P''.eqn k (inf_le_inf_left Z.gen hk) = (P''.eqn k (inf_le_inf_left Z.gen hk) * w) *
      (P.eqn i (inf_le_inf_left Z.gen hi) * P'.eqn j (inf_le_inf_left Z.gen hj)) := by
    rw [mul_assoc, hw, mul_one]
  obtain ⟨u, hu⟩ := GlobalTheory.GenUnitGlue.exists_unit_resG_eq Z (U := U) (P''.eqn k (inf_le_inf_left Z.gen hk) * w) (by
    intro x hx
    obtain ⟨V, i', j', k', hi', hj', hk', hxV, e⟩ := H x
    have a₁ : V ⊓ U ≤ P.M.U i' ⊓ P.M.U i := inf_le_inf hi' hi
    have a₂ : V ⊓ U ≤ P'.M.U j' ⊓ P'.M.U j := inf_le_inf hj' hj
    have a₃ : V ⊓ U ≤ P''.M.U k ⊓ P''.M.U k' :=
      le_inf (inf_le_right.trans hk) (inf_le_left.trans hk')
    refine ⟨V ⊓ U, inf_le_right, ⟨hxV, hx⟩,
      res a₃ (P''.M.g k k') * (res a₁ (P.M.g i' i) * res a₂ (P'.M.g j' j)), ?_⟩
    have b : Z.gen ⊓ (V ⊓ U) ≤ Z.gen ⊓ U := inf_le_inf_left _ inf_le_right
    have b' : Z.gen ⊓ (V ⊓ U) ≤ Z.gen ⊓ V := inf_le_inf_left _ inf_le_left
    have hf' := congrArg (resG Z.X b) hf
    have e' := congrArg (resG Z.X b') e
    rw [map_mul, map_mul _ (P.eqn _ _)] at hf'
    simp only [map_mul, VertDiv.resG_eqn] at e'
    rw [VertDiv.resG_eqn, VertDiv.resG_eqn, VertDiv.resG_eqn] at hf'
    refine ((P.isUnit_eqn i (b.trans (inf_le_inf_left Z.gen hi))).mul
      (P'.isUnit_eqn j (b.trans (inf_le_inf_left Z.gen hj)))).mul_right_cancel ?_
    refine Eq.trans ?_ hf'
    rw [P''.eqn_rel k k' _ (b'.trans (inf_le_inf_left Z.gen hk')) (inf_le_right.trans a₃), e',
      P.eqn_rel i' i _ (b.trans (inf_le_inf_left Z.gen hi)) (inf_le_right.trans a₁),
      P'.eqn_rel j' j _ (b.trans (inf_le_inf_left Z.gen hj)) (inf_le_right.trans a₂)]
    simp only [Units.val_mul, map_mul, val_res, resG_resG]
    ring)
  exact ⟨u, by rw [hu]; exact hf⟩

theorem Model.GenIso.cls_div_shortExact {S S' : ShortComplex Z.X.Modules} (hS : S.ShortExact)
    (hS' : S'.ShortExact) {r s : ℕ} (h₁ : IsVB S.X₁ r) (h₂ : IsVB S.X₂ (r + s)) (h₃ : IsVB S.X₃ s)
    (h₁' : IsVB S'.X₁ r) (h₂' : IsVB S'.X₂ (r + s)) (h₃' : IsVB S'.X₃ s)
    (g₁ : Z.GenIso S.X₁ S'.X₁) (g₂ : Z.GenIso S.X₂ S'.X₂) (g₃ : Z.GenIso S.X₃ S'.X₃)
    (e₁ : g₁.hom ≫ Z.genRes.map S'.f = Z.genRes.map S.f ≫ g₂.hom)
    (e₂ : g₂.hom ≫ Z.genRes.map S'.g = Z.genRes.map S.g ≫ g₃.hom) :
    (g₂.div h₂ h₂').cls = (g₁.div h₁ h₁').cls + (g₃.div h₃ h₃').cls := by
  have := h₁.isQuasicoherent
  have := h₂.isQuasicoherent
  have := h₃.isQuasicoherent
  have := h₁'.isQuasicoherent
  have := h₂'.isQuasicoherent
  have := h₃'.isQuasicoherent
  refine VertDiv.IsSum.cls_eq (VertDiv.isSum_of_local fun x => ?_)
  obtain ⟨a, ha⟩ := VBExt.exists_adaptedChart hS h₁ h₃ x
  obtain ⟨a', ha'⟩ := VBExt.exists_adaptedChart hS' h₁' h₃' x
  refine ⟨a.U ⊓ a'.U, (a.sub, a'.sub), (a.quot, a'.quot), (a.mid hS, a'.mid hS'), le_rfl, le_rfl,
    le_rfl, ⟨ha, ha'⟩, (Model.genEquiv inf_le_left).injective ?_⟩
  rw [map_mul]
  refine (g₂.genEquiv_eqn_div h₂ h₂' (a.mid hS) (a'.mid hS') _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (g₁.genEquiv_eqn_div h₁ h₁' a.sub a'.sub _)
    (g₃.genEquiv_eqn_div h₃ h₃' a.quot a'.quot _)).symm
  exact congrArg Units.val (GlobalTheory.T.generic_iso_short_exact_compat hS hS' g₁ g₂ g₃ e₁ e₂ a a' _)

theorem Flag.isIso_π_zero {X : Scheme.{0}} {E : X.Modules} {N : ℕ} (fl : Flag E (N + 1)) :
    IsIso (fl.π 0) := by
  have h : fl.step 0 = 0 := (VB.isVB_zero_iff.1 (fl.isVB 0)).eq_of_src _ _
  exact cokernel.π_of_zero h

theorem Model.FlagPair.cls_div_add_rank_two : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (B : GlobalTheory.Vert.Model O) (W W' : B.X.Modules) (ψ : B.GenIso W W')
    (R : GlobalTheory.Vert.Model.FlagPair ψ 2),
    (R.div 0).cls + (R.div 1).cls = (ψ.div R.fl.isVB_self R.fl'.isVB_self).cls := by
  intro O _ _ _ B W W' ψ R
  have := R.fl.isIso_π_zero
  have := R.fl'.isIso_π_zero
  have e₂ := Model.GenIso.cls_div_eq_of_iso O B _ _ _ _ 2 (R.fl.isVB (Fin.last 2))
    (R.fl'.isVB (Fin.last 2)) R.fl.isVB_self R.fl'.isVB_self (R.gen (Fin.last 2)) ψ
    (asIso (R.fl.ι _)) (asIso (R.fl'.ι _)) (R.gen_ι _)
  have e₁ := Model.GenIso.cls_div_eq_of_iso O B _ _ _ _ 1 (R.fl.isVB (Fin.succ 0))
    (R.fl'.isVB (Fin.succ 0)) (R.fl.isVB_gr 0) (R.fl'.isVB_gr 0) (R.gen (Fin.succ 0)) (R.grIso 0)
    (asIso (R.fl.π 0)) (asIso (R.fl'.π 0)) (R.π_grIso_hom 0).symm
  have e := Model.GenIso.cls_div_shortExact (VMetric.stepSeq_shortExact R.fl 1)
    (VMetric.stepSeq_shortExact R.fl' 1) (r := 1) (s := 1) (R.fl.isVB (Fin.castSucc 1))
    (R.fl.isVB (Fin.succ 1)) (R.fl.isVB_gr 1) (R.fl'.isVB (Fin.castSucc 1))
    (R.fl'.isVB (Fin.succ 1)) (R.fl'.isVB_gr 1) (R.gen (Fin.castSucc 1)) (R.gen (Fin.succ 1))
    (R.grIso 1) (R.gen_step 1).symm (R.π_grIso_hom 1).symm
  exact (congrArg (· + _) e₁.symm).trans (e.symm.trans e₂)

end GlobalTheory.Vert
