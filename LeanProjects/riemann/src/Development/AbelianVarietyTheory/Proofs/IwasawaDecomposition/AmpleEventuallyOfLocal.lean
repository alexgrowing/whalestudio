import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineOpenOfLocalSectionCombinationLocus
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

namespace GlobalTheory.AmpleTwistBase

theorem ample_nsmul_add : ∀ {F : Type} [Field F] (Y : Var F) {S T : Scheme.{0}} (f : Y.X ⟶ S) (g : S ⟶ T), IsAffineHom g → ∀ (H : LB T), IsAmpleLB H → ∀ (Δ Λ : Y.Dv), LBIso (Y.lb Δ) (H.pull (f ≫ g)) → (∀ z : S, ∃ V : S.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB ((Y.lb Λ).pull (f ⁻¹ᵁ V).ι)) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Y.ample (n • Δ + Λ) := by
  intro F _ Y S T f g _ H hH Δ Λ hΔ hV
  have hO := Y.isAmple_projective_O_one
  have : CompactSpace Y.X := hO.compactSpace
  have : QuasiSeparatedSpace Y.X := hO.quasiSeparatedSpace
  have hH' : IsAmpleLB (H.pull g) := hH.pull_of_isAffineHom g
  have : CompactSpace S := hH'.compactSpace
  have hL : (Y.lb Λ).IsLB := isLB_toLB Λ
  choose V hzV hVa hVL using hV
  have loc : ∀ z : S, ∃ n, 1 ≤ n ∧ ∃ s : (lbPow (H.pull g) n).Sec, z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ∧
      ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ≤ V z ∧ IsAffineOpen (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) :=
    fun z => hH'.exists_affine_le (hzV z)
  choose n hn s hzs hsV hsa using loc
  obtain ⟨T₀, hT₀⟩ := exists_finset_iSup_eq_top (fun z => ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z)) hzs
  obtain ⟨N, hN, t, ht⟩ := exists_common_pow (fun z : T₀ => n z) (fun z => hn z) (fun z => s z)
  have hHN := isLB_lbPow hH'.isLB N
  have hG : ((lbPow (H.pull g) N).pull f).IsLB := LB.isLB_pull hHN f
  have hGgen : IsGenerated ((lbPow (H.pull g) N).pull f) :=
    (isGenerated_of_finite t (by simp only [ht]; exact hT₀)).pull f
  have hLN := isLB_lbPow hL N
  obtain ⟨c, hc⟩ := RelAmpleQProj.exists_isAmpleLB_tw hLN hG fun y => by
    obtain ⟨z, hz⟩ := TopologicalSpace.Opens.mem_iSup.1 (hT₀.ge (Set.mem_univ (f y)))
    refine ⟨secPull (t z) f, f ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z), by rw [nonzeroLocus_secPull, ht], hz, ?_⟩
    have := GlobalTheory.ZH.CombLocus.isAffineHom_homOfLE f (hsV z) (hsa z) (hVa z)
    have h₁ : IsAmpleLB (((Y.lb Λ).pull (f ⁻¹ᵁ V z).ι).pull (Y.X.homOfLE (f.preimage_mono (hsV z)))) :=
      (hVL z).pull_of_isAffineHom _
    have h₂ : IsAmpleLB ((Y.lb Λ).pull (f ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z)).ι) :=
      h₁.of_lbIso (LB.isLB_pull hL _) (GenSpread.lbIso_pull_pull hL _ (Scheme.homOfLE_ι _ _).symm)
    exact ((isAmpleLB_pow_iff (LB.isLB_pull hL _) hN).2 h₂).of_lbIso (LB.isLB_pull hLN _)
      (lbIso_lbPow_pull hL _ N).symm
  refine ⟨c, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hD := isLB_toLB ((c + k) • Δ + Λ)
  refine (isAmpleLB_pow_iff hD hN).1 ?_
  have hT := AbLaw.isLB_tw hLN hG (c : ℤ)
  have hK := isLB_lbPow hG k
  have eG : CechPic.cls _ hG = N • toPic Δ := by
    rw [toPic_apply, (CechPic.cls_eq_iff (isLB_toLB Δ) (LB.isLB_pull hH.isLB (f ≫ g))).2 hΔ,
      CechPic.cls_pull hH.isLB, CechPic.pull_comp, CechPic.cls_pull hHN f, CechPic.cls_lbPow hH'.isLB,
      CechPic.cls_pull hH.isLB g, map_nsmul]
  have eT : CechPic.cls _ hT = CechPic.cls _ hLN + (c : ℤ) • CechPic.cls _ hG := by
    have e := CechPic.cls_div hLN (AbLaw.isLB_pw hG (-(c : ℤ))) hT
    rw [AmpleStabFinite.cls_pw] at e
    exact e.trans (by rw [neg_smul, sub_neg_eq_add])
  refine hc.tensor_isGenerated (hGgen.pow k) (isLB_lbPow hD N) ((CechPic.cls_eq_zero_iff (LB.isLB_div (LB.isLB_div (isLB_lbPow hD N) hT) hK)).1 ?_)
  rw [CechPic.cls_div (LB.isLB_div (isLB_lbPow hD N) hT) hK, CechPic.cls_div (isLB_lbPow hD N) hT,
    CechPic.cls_lbPow hD, CechPic.cls_lbPow hG, eT, CechPic.cls_lbPow hL, eG, ← toPic_apply, ← toPic_apply,
    map_add, map_nsmul]
  module

end GlobalTheory.AmpleTwistBase
