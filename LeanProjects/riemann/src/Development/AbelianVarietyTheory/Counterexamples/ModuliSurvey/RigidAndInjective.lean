import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BeTransSymmOfWitData
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsWitDataLevelAgree
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkInjectiveClosed

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DataRigid

open GlobalTheory.MatchRigid

theorem dataRigid_of_laws (hL : Laws) : DataRigidSt := by
  intro E _ _ _ H D l c k _ bF a P _ oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ d₁ d₂ hlev
  have W₁ : GlobalTheory.LN.Match a PowerSeries.C PowerSeries.X P.toPre oP φ₁ he₁ w₁ e₁ := d₁
  have W₂ : GlobalTheory.LN.Match a PowerSeries.C PowerSeries.X P.toPre oP φ₂ he₂ w₂ e₂ := d₂
  obtain ⟨F, _, _, _, _, hF⟩ := GlobalTheory.HostModel.exists_common_field k
  have : CharZero k := charZero_of_injective_ringHom bF.injective
  have : CharZero F := charZero_of_injective_ringHom ((algebraMap (FractionRing k) F).comp (algebraMap k _)).injective
  have hM : (l.M : F) ≠ 0 := Nat.cast_ne_zero.2 (lt_of_lt_of_le three_pos l.three_le).ne'
  have hrz : ∃ r z : c.F, ((RingHom.id c.F r : c.F) : ℂ) = H.rt0 ∧ ((RingHom.id c.F z : c.F) : ℂ) = zeta l.A :=
    ⟨⟨H.rt0, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩,
      ⟨zeta l.A, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩, rfl, rfl⟩
  have hl := fun v hv q₀ q₁ q₂ hq (t₁ : IsTransport a w₁ e₁ _ q₀ q₁) (t₂ : IsTransport a w₂ e₂ _ q₀ q₂) =>
    hlev F _ hF rfl l.M (a.eta v) (Or.inr ⟨rfl, v, hv, HEq.rfl⟩) q₀ q₁ q₂ hq t₁.1 t₂.1 t₁.2 t₂.2
  have hφ := map_eq P.tau_bimult W₁ W₂ hF rfl hrz hl hL hM
  refine ⟨hφ, lattice_eq P.tau_bimult W₁ W₂ hF rfl hrz hl hL hM fun y => ?_, ?_⟩
  · exact GlobalTheory.ThetaShiftProofs.be_self_eq_of_witData a P oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ d₁ d₂ _ _ (by simp)
  · subst hφ
    exact heq_of_eq (rigidified_iso_unique hL.globalFns P.toPre.P a.D₀.P.isLB φ₁ w₁ w₂ W₁.2.1 W₂.2.1 _ _ W₁.2.2.1
      W₂.2.2.1)

theorem dataRigid : DataRigidSt := dataRigid_of_laws GlobalTheory.abelianSchemeLaws_all.1

theorem rigid_and_injective : DataRigidSt ∧ QkToAkInjSt :=
  ⟨dataRigid, GlobalTheory.TorsionMapInj.qkToAk_injective_closed⟩

end GlobalTheory.DataRigid
