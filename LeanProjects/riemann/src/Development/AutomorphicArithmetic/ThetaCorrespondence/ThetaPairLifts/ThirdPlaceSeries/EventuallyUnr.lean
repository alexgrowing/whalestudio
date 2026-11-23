import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip
open GlobalTheory.Mem.Chr hiding HChar
namespace GlobalTheory.CuspRep.ParLaws
section Group
variable {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
end Group
section Local
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]
end Local
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section Par
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)} {a : ℕ}
variable {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h}
theorem reciprocity_unramified_iff_spherical (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) (σ : IrrRep (GL (Fin a) (w.adicCompletion E))) :
    (rc (cls σ)).unr ↔ IsSpherical σ.ρ := by
  first | (have hOpn := UpperTheory.One.M.opn _ (H); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := H
  rw [← H.sph]
  exact ⟨fixed_ne_bot_of_equiv (equivRep σ).symm, fixed_ne_bot_of_equiv (equivRep σ)⟩
theorem reciprocity_eq_diagonal_inv_of_has_satake (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {σ : IrrRep (GL (Fin a) (w.adicCompletion E))} {α : Fin a → ℂˣ}
    (hα : HasSatake σ.ρ α) : rc (cls σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (H); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := H
  have φ := equivRep σ
  exact H.sat (cls σ) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩
variable [IsTotallyComplex E]
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
theorem local_parameter_eq_reciprocity_of_is_local_component {π : CuspSub E a} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ)
    (h : IsPlaceOver A w) : _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π) h = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls (toRep σ)) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [_root_.GlobalTheory.CuspRep.ParLawsT.locParT, CG.IsLoc.unique E a _ w _ _ h1.loc h1]
  rfl
theorem dim_local_parameter_eq_rank (π : CG E a) (h : IsPlaceOver A w) : (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).lpDim = a := by
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  exact H.dim _
include hF in
theorem eventually_unramified_local_parameter (π : CG E a) : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w), (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).unr := by
  induction π using Quotient.inductionOn with | _ π =>
  filter_upwards [LocSph.locComp_spherical E a π] with w hw A h
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  obtain ⟨v, h0, hv⟩ := hw σ hσ
  refine (_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ h).symm ▸ (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) _).2 ((Submodule.ne_bot_iff _).2 ⟨v, fun x => ?_, h0⟩)
  obtain ⟨x, hx⟩ := x
  rw [SphCompletion.KO_completion] at hx
  obtain ⟨g, rfl⟩ := hx
  exact (hv g).trans (one_smul _ _).symm
theorem local_parameter_of_hecke_character_eq_reciprocity (χ : HChar E) (h : IsPlaceOver A w) :
    _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (.ofChar (χ.loc w) (isSmoothChar_loc χ w)) :=
  _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL (CG.isLoc_ofChar χ w) h
end Par
section Conj
end Conj
section Host
end Host
end GlobalTheory.CuspRep.ParLaws
end
end
