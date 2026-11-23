import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineOpenOfLocalSectionCombinationLocus
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.AmpleTwistLB

theorem ample_pow_div : ∀ {W S : Scheme.{0}} [CompactSpace W] [QuasiSeparatedSpace W] (f : W ⟶ S) (A : LB S), IsAmpleLB A → ∀ (N M : LB W) (hN : N.IsLB) (hM : M.IsLB), GlobalTheory.CechPic.cls M hM = -GlobalTheory.CechPic.cls N hN → (∀ z : S, ∃ V : S.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB (M.pull (f ⁻¹ᵁ V).ι)) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsAmpleLB (LB.div (lbPow (A.pull f) n) N) := by
  intro W S _ _ f A hA N M hN hM hcls hV
  have : CompactSpace S := hA.compactSpace
  choose V hzV hVa hVL using hV
  have loc : ∀ z : S, ∃ n, 1 ≤ n ∧ ∃ s : (lbPow A n).Sec, z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ∧
      ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ≤ V z ∧ IsAffineOpen (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) :=
    fun z => hA.exists_affine_le (hzV z)
  choose n hn s hzs hsV hsa using loc
  obtain ⟨T₀, hT₀⟩ := exists_finset_iSup_eq_top (fun z => ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z)) hzs
  obtain ⟨K, hK, t, ht⟩ := exists_common_pow (fun z : T₀ => n z) (fun z => hn z) (fun z => s z)
  have hAK := isLB_lbPow hA.isLB K
  have hG : ((lbPow A K).pull f).IsLB := LB.isLB_pull hAK f
  have hGgen : IsGenerated ((lbPow A K).pull f) :=
    (isGenerated_of_finite t (by simp only [ht]; exact hT₀)).pull f
  have hMK := isLB_lbPow hM K
  obtain ⟨c, hc⟩ := RelAmpleQProj.exists_isAmpleLB_tw hMK hG fun y => by
    obtain ⟨z, hz⟩ := TopologicalSpace.Opens.mem_iSup.1 (hT₀.ge (Set.mem_univ (f y)))
    refine ⟨secPull (t z) f, f ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z), by rw [nonzeroLocus_secPull, ht], hz, ?_⟩
    have := GlobalTheory.ZH.CombLocus.isAffineHom_homOfLE f (hsV z) (hsa z) (hVa z)
    have h₁ : IsAmpleLB ((M.pull (f ⁻¹ᵁ V z).ι).pull (W.homOfLE (f.preimage_mono (hsV z)))) :=
      (hVL z).pull_of_isAffineHom _
    have h₂ : IsAmpleLB (M.pull (f ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s z)).ι) :=
      h₁.of_lbIso (LB.isLB_pull hM _) (GenSpread.lbIso_pull_pull hM _ (Scheme.homOfLE_ι _ _).symm)
    exact ((isAmpleLB_pow_iff (LB.isLB_pull hM _) hK).2 h₂).of_lbIso (LB.isLB_pull hMK _)
      (lbIso_lbPow_pull hM _ K).symm
  refine ⟨c, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hAf : (A.pull f).IsLB := LB.isLB_pull hA.isLB f
  have hD : (LB.div (lbPow (A.pull f) (c + k)) N).IsLB := LB.isLB_div (isLB_lbPow hAf (c + k)) hN
  refine (isAmpleLB_pow_iff hD hK).1 ?_
  have hT := AbLaw.isLB_tw hMK hG (c : ℤ)
  have hGk := isLB_lbPow hG k
  have eG : CechPic.cls _ hG = K • CechPic.cls _ hAf := by
    rw [CechPic.cls_pull hAK f, CechPic.cls_lbPow hA.isLB, map_nsmul, ← CechPic.cls_pull hA.isLB f]
  have eT : CechPic.cls _ hT = CechPic.cls _ hMK + (c : ℤ) • CechPic.cls _ hG := by
    have e := CechPic.cls_div hMK (AbLaw.isLB_pw hG (-(c : ℤ))) hT
    rw [AmpleStabFinite.cls_pw] at e
    exact e.trans (by rw [neg_smul, sub_neg_eq_add])
  refine hc.tensor_isGenerated (hGgen.pow k) (isLB_lbPow hD K) ((CechPic.cls_eq_zero_iff (LB.isLB_div (LB.isLB_div (isLB_lbPow hD K) hT) hGk)).1 ?_)
  rw [CechPic.cls_div (LB.isLB_div (isLB_lbPow hD K) hT) hGk, CechPic.cls_div (isLB_lbPow hD K) hT,
    CechPic.cls_lbPow hD, CechPic.cls_lbPow hG, eT, CechPic.cls_lbPow hM, eG, CechPic.cls_div (isLB_lbPow hAf (c + k)) hN hD,
    CechPic.cls_lbPow hAf, hcls]
  module

end GlobalTheory.AmpleTwistLB
