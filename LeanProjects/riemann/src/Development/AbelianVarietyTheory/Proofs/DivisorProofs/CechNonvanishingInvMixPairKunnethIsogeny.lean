import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiMapFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietySquareLinearEndomorphismFiniteLocaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowEqMumfordFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowMulMixedSplitStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankCechLBHomologyExtProd
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechComplexAcyclicAdditiveLineBundleNoSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinFreeAwayOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

set_option autoImplicit false

noncomputable section

section Lemmas
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGen

open GlobalTheory.CechPic in

theorem cls_tw_one {X : Scheme.{0}} {M H : LB X} (hM : M.IsLB) (hH : H.IsLB) :
    cls (GlobalTheory.AbLaw.tw M H 1) (GlobalTheory.AbLaw.isLB_tw hM hH 1) = cls M hM + cls H hH := by
  refine (cls_div (A := M) (B := GlobalTheory.AbLaw.pw H (-1)) hM (GlobalTheory.AbLaw.isLB_pw hH _) (GlobalTheory.AbLaw.isLB_tw hM hH 1)).trans ?_
  rw [GlobalTheory.AmpleStabFinite.cls_pw hH]
  simp

open GlobalTheory.CechPic in

theorem cls_mix_pull {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    {T : Over (Sp K)} (z : T ⟶ A) (a b : ℤ) :
    cls ((mix A L a b).pull z.left) (LB.isLB_pull (LB.isLB_linComb hL _ _) _) =
      a • pull z.left (cls L hL) + b • pull (z⁻¹).left (cls L hL) := by
  refine (cls_pull (L := LB.LinComb L ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![a, b])
    (LB.isLB_linComb hL _ _) _ _).trans ?_
  rw [cls_linComb hL, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_zsmul, pull_id, ← pull_comp,
    ← Over.comp_left, Hom.inv_def]

end GlobalTheory.AmpleGen
end Lemmas

section RowLatticeBoundForBasis
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AmpleGen
open GlobalTheory.CechPic in

theorem lbIso_pull_psiMap {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (a₁ b₁ a₂ b₂ : ℤ) (hs : a₁ * b₁ + a₂ * b₂ = 0) {L : LB A.left} (hL : L.IsLB) (a b : ℤ) :
    LBIso ((GlobalTheory.AbLaw.tw ((mix A L a b).pull (fst A A).left) ((mix A L a b).pull (snd A A).left) 1).pull
        (psiMap A a₁ b₁ a₂ b₂).left)
      (GlobalTheory.AbLaw.tw ((mix A L (a * tri a₁ + b * tri (-a₁) + a * tri a₂ + b * tri (-a₂))
                   (a * tri (-a₁) + b * tri a₁ + a * tri (-a₂) + b * tri a₂)).pull (fst A A).left)
        ((mix A L (a * tri b₁ + b * tri (-b₁) + a * tri b₂ + b * tri (-b₂))
          (a * tri (-b₁) + b * tri b₁ + a * tri (-b₂) + b * tri b₂)).pull (snd A A).left) 1) := by
  haveI := hA.comm
  have hP' : ∀ a b : ℤ, (mix A L a b).IsLB := fun _ _ => LB.isLB_linComb hL _ _
  have h₁ := GlobalTheory.AbLaw.isLB_tw (LB.isLB_pull (hP' a b) (fst A A).left) (LB.isLB_pull (hP' a b) (snd A A).left) 1
  refine (cls_eq_iff (LB.isLB_pull h₁ _) (GlobalTheory.AbLaw.isLB_tw (LB.isLB_pull (hP' _ _) _)
    (LB.isLB_pull (hP' _ _) _) 1)).1 ?_
  rw [cls_pull h₁, cls_tw_one, cls_tw_one, cls_mix_pull A hL, cls_mix_pull A hL, cls_mix_pull A hL,
    cls_mix_pull A hL]
  simp only [map_add, map_zsmul, ← pull_comp, ← Over.comp_left, GrpObj.comp_inv, psiMap, lift_fst, lift_snd]
  set c := cls L hL
  set x := fst A A
  set y := snd A A
  have e₁ := GlobalTheory.T.cechPicardPullback_zpow_mul_mixed_split K A hA L hL _ x y a₁ b₁ a b
  have e₂ := GlobalTheory.T.cechPicardPullback_zpow_mul_mixed_split K A hA L hL _ x y a₂ b₂ a b
  have f (z : A ⊗ A ⟶ A) (n : ℤ) := GlobalTheory.T.cechPicardPullback_zpow_eq_mumford_formula K A hA L hL _ z n
  have g (z : A ⊗ A ⟶ A) (n : ℤ) : pull ((z ^ n)⁻¹).left c = tri (-n) • pull z.left c + tri n • pull (z⁻¹).left c := by
    rw [← zpow_neg, f, neg_neg]
  rw [e₁, e₂, f x a₁, g x a₁, f x a₂, g x a₂, f y b₁, g y b₁, f y b₂, g y b₂]
  have hl : ((a + b) * (a₁ * b₁)) • lam c x y + ((a + b) * (a₂ * b₂)) • lam c x y = 0 := by
    rw [← add_smul, ← mul_add, hs, mul_zero, zero_smul]
  linear_combination (norm := module) hl
  all_goals exact LB.isLB_pull (hP' _ _) _
end GlobalTheory.AmpleGen
end RowLatticeBoundForBasis

section MainAux
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AmpleGen

theorem finrank_pos_of_not_exactAt {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {M : LB X} {κ : Type} [LinearOrder κ] {D : κ → X.Opens} {n : ℕ}
    [Module.Finite K ((cechLB f M D).homology n)] (h : ¬ (cechLB f M D).ExactAt n) :
    0 < Module.finrank K ((cechLB f M D).homology n) := by
  have : Nontrivial ((cechLB f M D).homology n) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact h ((HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (ModuleCat.isZero_of_subsingleton _))
  exact Module.finrank_pos

theorem exists_nonvanishing_invMix_pair_isogeny (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (a₁ b₁ a₂ b₂ : ℤ) (hs : a₁ * b₁ + a₂ * b₂ = 0) (hd : ((a₁ * b₂ - b₁ * a₂ : ℤ) : K) ≠ 0)
    (L : LB A.left) (hL : L.IsLB) (a b j : ℕ) (hN : NV A (mix A L a b) j) :
    ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧
      NV A (mix A L (a * tri a₁ + b * tri (-a₁) + a * tri a₂ + b * tri (-a₂))
        (a * tri (-a₁) + b * tri a₁ + a * tri (-a₂) + b * tri a₂)) j₁ ∧
      NV A (mix A L (a * tri b₁ + b * tri (-b₁) + a * tri b₂ + b * tri (-b₂))
        (a * tri (-b₁) + b * tri b₁ + a * tri (-b₂) + b * tri b₂)) j₂ := by
  haveI := hA.comm
  haveI := hA.proper
  obtain ⟨κ, _, _, W, hW, hWc, hne⟩ := hN
  have hP' : ∀ a b : ℤ, (mix A L a b).IsLB := fun _ _ => LB.isLB_linComb hL _ _
  have hsep : IsSeparated A.hom := inferInstance
  have hproj := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K A hA
  have fin : ∀ M : LB A.left, M.IsLB → ∀ n, Module.Finite K ((cechLB A.hom M W).homology n) :=
    fun M hM => cechLB_homology_finite_of_affine_cover K _ A.hom M κ W hM hsep hproj hW hWc
  have h₀ : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback A.hom A.hom
  have hAA := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  haveI := hAA.comm
  haveI := hAA.proper
  have hsepAA : IsSeparated (A ⊗ A).hom := inferInstance
  have hprojAA := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K (A ⊗ A) hAA
  haveI : CompactSpace (A ⊗ A).left := QuasiCompact.compactSpace_of_compactSpace (A ⊗ A).hom
  obtain ⟨k, E, hE, hEc⟩ := GlobalTheory.PicZeroVan.exists_fin_affine_cover (A ⊗ A).left
  obtain ⟨hfin, hflat, hlfp, r, hr, hr0⟩ := GlobalTheory.T.abelianVarietySquareLinearEndomorphism_finiteLocallyFree K A hA a₁ b₁ a₂ b₂ hd
  set ψ := psiMap A a₁ b₁ a₂ b₂ with hψ
  set P := mix A L a b with hPdef
  have hP := hP' a b
  have hf₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w (fst A A)
  have hfψ : ψ.left ≫ (A ⊗ A).hom = (A ⊗ A).hom := Over.w ψ

  have k₀ := finrank_cechLB_homology_extProd K _ _ _ A.hom A.hom (fst A A).left (snd A A).left P P h₀ hP hP
    hsep hsep κ W κ W (Fin k) E hW hWc hW hWc hE hEc (fin P hP) (fin P hP) (2 * j)
  have hpos : 0 < Module.finrank K ((cechLB A.hom P W).homology j) := by
    haveI := fin P hP j
    exact finrank_pos_of_not_exactAt hne
  have hM : ¬ (cechLB ((fst A A).left ≫ A.hom) (tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1) E).ExactAt
      (2 * j) := by
    intro hex
    have hz : Module.finrank K ((cechLB ((fst A A).left ≫ A.hom)
        (tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1) E).homology (2 * j)) = 0 := by
      have : Subsingleton ((cechLB ((fst A A).left ≫ A.hom)
          (tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1) E).homology (2 * j)) :=
        ModuleCat.subsingleton_of_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hex)
      exact Module.finrank_zero_of_subsingleton
    rw [k₀] at hz
    have := (Finset.sum_eq_zero_iff.1 hz) (j, j) (by simp [two_mul])
    exact (Nat.mul_pos hpos hpos).ne' this

  have hu : IsUnit ((r : ℕ) : Γ((A ⊗ A).left, ⊤)) := by
    have := (GlobalTheory.AbelianMulFin.isUnit_natCast_Sp (K := K) hr0).map (A ⊗ A).hom.appTop.hom
    rwa [map_natCast] at this
  rw [hf₁] at hM
  have hM' : ¬ (cechLB (ψ.left ≫ (A ⊗ A).hom)
      ((tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1).pull ψ.left) (fun i => ψ.left ⁻¹ᵁ E i)).ExactAt
      (2 * j) := fun h => hM ((GlobalTheory.FinTrace.cechLB_retract_and_exactAt ψ.left (A ⊗ A).hom r hr hu _ E).2 _ h)
  rw [hfψ] at hM'
  set P₁ := mix A L (a * tri a₁ + b * tri (-a₁) + a * tri a₂ + b * tri (-a₂))
        (a * tri (-a₁) + b * tri a₁ + a * tri (-a₂) + b * tri a₂) with hP₁def
  set P₂ := mix A L (a * tri b₁ + b * tri (-b₁) + a * tri b₂ + b * tri (-b₂))
        (a * tri (-b₁) + b * tri b₁ + a * tri (-b₂) + b * tri b₂) with hP₂def
  have hP₁ : P₁.IsLB := hP' _ _
  obtain ⟨w, hw⟩ := lbIso_pull_psiMap A hA a₁ b₁ a₂ b₂ hs hL a b
  have hP₂ : P₂.IsLB := hP' _ _
  have hTw : (tw (P₁.pull (fst A A).left) (P₂.pull (snd A A).left) 1).IsLB :=
    isLB_tw (LB.isLB_pull hP₁ _) (LB.isLB_pull hP₂ _) 1
  have hN₂ : ¬ (cechLB (A ⊗ A).hom (tw (P₁.pull (fst A A).left) (P₂.pull (snd A A).left) 1)
      (fun i => ψ.left ⁻¹ᵁ E i)).ExactAt (2 * j) := fun h =>
    hM' (h.of_iso (cechLBCongr _ _ (LB.isLB_pull (isLB_tw (LB.isLB_pull hP _) (LB.isLB_pull hP _) 1) _)
      hTw w hw).symm)

  have hD : ∀ i, IsAffineOpen (ψ.left ⁻¹ᵁ E i) := fun i => (hE i).preimage ψ.left
  have hDc : ⨆ i, ψ.left ⁻¹ᵁ E i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hEc]; rfl
  have k₁ := finrank_cechLB_homology_extProd K _ _ _ A.hom A.hom (fst A A).left (snd A A).left P₁ P₂ h₀ hP₁ hP₂
    hsep hsep κ W κ W (Fin k) (fun i => ψ.left ⁻¹ᵁ E i) hW hWc hW hWc hD hDc (fin P₁ hP₁) (fin P₂ hP₂) (2 * j)
  rw [hf₁] at k₁
  haveI := cechLB_homology_finite_of_affine_cover K _ (A ⊗ A).hom _ (Fin k) (fun i => ψ.left ⁻¹ᵁ E i) hTw hsepAA
    hprojAA hD hDc (2 * j)
  have hpos₂ := finrank_pos_of_not_exactAt hN₂
  rw [k₁] at hpos₂
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos₂.ne'
  have hx' : x.1 + x.2 = 2 * j := by simpa using hx
  refine ⟨x.1, x.2, hx', ⟨κ, inferInstance, inferInstance, W, hW, hWc, fun h => hx0 ?_⟩,
    ⟨κ, inferInstance, inferInstance, W, hW, hWc, fun h => hx0 ?_⟩⟩
  · haveI := fin P₁ hP₁ x.1
    have : Subsingleton ((cechLB A.hom P₁ W).homology x.1) :=
      ModuleCat.subsingleton_of_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 h)
    rw [Module.finrank_zero_of_subsingleton, zero_mul]
  · haveI := fin P₂ hP₂ x.2
    have : Subsingleton ((cechLB A.hom P₂ W).homology x.2) :=
      ModuleCat.subsingleton_of_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 h)
    rw [Module.finrank_zero_of_subsingleton (R := K) (M := (cechLB A.hom P₂ W).homology x.2), mul_zero]

end GlobalTheory.AmpleGen
end MainAux

section Target
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

theorem GlobalTheory.AmpleGen.nv_mix_pair_of_nv : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ α β γ δ : ℤ, α * β + γ * δ = 0 → ((α * δ - β * γ : ℤ) : K) ≠ 0 → ∀ L : LB A.left, L.IsLB → ∀ a b j : ℕ, NV A (mix A L a b) j → ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (a * tri α + b * tri (-α) + a * tri γ + b * tri (-γ)) (a * tri (-α) + b * tri α + a * tri (-γ) + b * tri γ)) j₁ ∧ NV A (mix A L (a * tri β + b * tri (-β) + a * tri δ + b * tri (-δ)) (a * tri (-β) + b * tri β + a * tri (-δ) + b * tri δ)) j₂ := by
  intro K _ _ A _ hA α β γ δ hs hd L hL a b j h
  exact exists_nonvanishing_invMix_pair_isogeny K A hA α β γ δ hs hd L hL a b j h

end Target
