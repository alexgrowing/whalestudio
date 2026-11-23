import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeOfDifferentSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverCuspFormPullbackInjectiveDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCoreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCuspFormPullbackGoodCoverStatement

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC

noncomputable section

namespace GlobalTheory.CoreRing

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem slope_sq_latOver_sub_le : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (T.R j)), LawsJ T → InR D j → Y.Good e o → Dom a n → S ⊆ (T.cuspA j a n : Set (T.R j)) → GoodW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n) → GoodW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict (wtZ a n) → slope_sq (Y.nrm (wtZ a n)) (Y.latOver (wtZ a n) S) - 2 * (Real.log |(discr Y.d.c₂.F : ℝ)| / Module.finrank ℚ Y.d.c₂.F) ≤ slope_sq (normW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n)) (latW (T.U j) (wtZ a n) ⊓ ((Submodule.span T.Q.c.F S).comap (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype).restrictScalars (𝓞 T.Q.c.F)) := by
  intro D T j Y e o a n S hT hj hY hDom hS hG hG₂
  obtain ⟨hLc, hNc⟩ := GlobalTheory.T.principalLevelLiftModuliLaws_of_core D T j hT hj
  obtain ⟨hLd, hGal, hPull⟩ := GlobalTheory.T.deepLevelCover_principalLevel_laws_galois D T j Y e o hT hj hY hY.unit hY.modelW
  letI : Algebra T.Q.c.F Y.d.c₂.F := ((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle)).toAlgebra
  obtain ⟨π, hπP, hπli, hπN, hπlat, -, hπD⟩ := GlobalTheory.T.levelCover_cuspForm_pullback_injective_descent D j _ _ _ (T.Q.Xo j) T.Q.c Y.c' Y.hle (T.U j)
    (coreDict T.toCore j) Y.d Y.U Y.dict hLc hLd hY.lev.1 hGal a n hDom hDom.2
  have hTC : IsTotallyComplex T.Q.c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := T.Q.c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩

  have hSc : ∀ f ∈ S, f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) := fun f hf => by
    rw [cuspW_wtZ]; exact hS hf

  have hPf : ∀ f : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), Y.Pull (f : T.R j) (π f : Rul Y.d.Xo₂ Y.d.c₂) := fun f =>
    (hPull a n _ (cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) a n (by rw [← cuspW_wtZ]; exact f.2)) _).2 (hπP f)

  have p0 : Y.Pull (0 : T.R j) (0 : Rul Y.d.Xo₂ Y.d.c₂) := by
    intro k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    simp only [evR, evalAt_zero]
  have pAdd : ∀ r₁ r₂ : Rul Y.d.Xo₂ Y.d.c₂, Y.Pull (0 : T.R j) r₁ → Y.Pull (0 : T.R j) r₂ →
      Y.Pull (0 : T.R j) (r₁ + r₂) := by
    intro r₁ r₂ hr₁ hr₂ k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hr₁ k hA hk y₂ y' y h1 h2 h3 h4
    have e2 := hr₂ k hA hk y₂ y' y h1 h2 h3 h4
    simp only [evR, evalAt_zero, evalAt_add] at e1 e2 ⊢
    rw [e1, e2, add_zero]
  have pSmul : ∀ (c : Y.d.c₂.F) (r : Rul Y.d.Xo₂ Y.d.c₂), Y.Pull (0 : T.R j) r → Y.Pull (0 : T.R j) (c • r) := by
    intro c r hr k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hr k hA hk y₂ y' y h1 h2 h3 h4
    simp only [evR, evalAt_zero, evalAt_smul] at e1 ⊢
    rw [e1, mul_zero]
  have pSub : ∀ (f : T.R j) (g₁ g₂ : Rul Y.d.Xo₂ Y.d.c₂), Y.Pull f g₁ → Y.Pull f g₂ → Y.Pull (0 : T.R j) (g₁ - g₂) := by
    intro f g₁ g₂ hg₁ hg₂ k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hg₁ k hA hk y₂ y' y h1 h2 h3 h4
    have e2 := hg₂ k hA hk y₂ y' y h1 h2 h3 h4
    have e3 : evR Y.d.Xo₂ Y.d.c₂ (g₁ - g₂) y₂ = evR Y.d.Xo₂ Y.d.c₂ g₁ y₂ - evR Y.d.Xo₂ Y.d.c₂ g₂ y₂ :=
      map_sub (evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂) g₁ g₂
    rw [e3, e1, e2, sub_self]
    simp only [evR, evalAt_zero]
  have pSmul2 : ∀ (c : Y.d.c₂.F) (h : Rul Y.d.Xo₂ Y.d.c₂) (x : Y.V (wtZ a n)),
      Y.Pull (0 : T.R j) (h - (x : Rul Y.d.Xo₂ Y.d.c₂)) →
        Y.Pull (0 : T.R j) (c • h - ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂)) := by
    intro c h x hp k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hp k hA hk y₂ y' y h1 h2 h3 h4
    have es1 : evR Y.d.Xo₂ Y.d.c₂ (h - (x : Rul Y.d.Xo₂ Y.d.c₂)) y₂ =
        evR Y.d.Xo₂ Y.d.c₂ h y₂ - evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) y₂ :=
      map_sub (evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂) h (x : Rul Y.d.Xo₂ Y.d.c₂)
    have es2 : evR Y.d.Xo₂ Y.d.c₂ (c • h - ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂)) y₂ =
        evR Y.d.Xo₂ Y.d.c₂ (c • h) y₂ - evR Y.d.Xo₂ Y.d.c₂ ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂) y₂ :=
      map_sub (evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂) _ _
    have es3 : evR Y.d.Xo₂ Y.d.c₂ (c • h) y₂ = algebraMap Y.d.c₂.F k c * evR Y.d.Xo₂ Y.d.c₂ h y₂ := by
      simp only [evR, evalAt_smul]
    have es4 : evR Y.d.Xo₂ Y.d.c₂ ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂) y₂ =
        algebraMap Y.d.c₂.F k c * evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) y₂ :=
      (map_smul ((evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂).comp (Y.V (wtZ a n)).subtype) c x).trans (Algebra.smul_def c _)
    rw [es2, es3, es4, ← mul_sub, ← es1, e1]
    simp only [evR, evalAt_zero, mul_zero]
  set C : Submodule T.Q.c.F (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)) :=
    (Submodule.span T.Q.c.F S).comap (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype with hC
  have hCspan : C = Submodule.span T.Q.c.F ((cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype ⁻¹' S) := by
    rw [hC, ← Submodule.comap_map_eq_of_injective (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).injective_subtype
      (Submodule.span T.Q.c.F ((cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype ⁻¹' S)), Submodule.map_span,
      Set.image_preimage_eq_of_subset]
    intro f hf
    exact ⟨⟨f, hSc f hf⟩, rfl⟩
  have hCQ : ∀ x ∈ C, π x ∈
      (Submodule.span Y.d.c₂.F {g | ∃ f ∈ S, Y.Pull f g}).comap (Y.V (wtZ a n)).subtype := by
    rw [hCspan]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨(y : T.R j), hy, hPf y⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy => rw [π.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  have key : ∀ h ∈ Submodule.span Y.d.c₂.F {g | ∃ f ∈ S, Y.Pull f g},
      ∃ x : Y.V (wtZ a n), x ∈ Submodule.span Y.d.c₂.F (π '' (C : Set (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)))) ∧
        Y.Pull (0 : T.R j) (h - (x : Rul Y.d.Xo₂ Y.d.c₂)) := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨f, hfS, hpf⟩ := hh
      refine ⟨π ⟨f, hSc f hfS⟩, Submodule.subset_span ⟨⟨f, hSc f hfS⟩, Submodule.subset_span hfS, rfl⟩, ?_⟩
      exact pSub f _ _ hpf (hPf _)
    | zero => exact ⟨0, zero_mem _, by simpa using p0⟩
    | add h₁ h₂ _ _ ih₁ ih₂ =>
      obtain ⟨x₁, hx₁, p₁⟩ := ih₁
      obtain ⟨x₂, hx₂, p₂⟩ := ih₂
      refine ⟨x₁ + x₂, add_mem hx₁ hx₂, ?_⟩
      have : h₁ + h₂ - ((x₁ + x₂ : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂) =
          (h₁ - (x₁ : Rul Y.d.Xo₂ Y.d.c₂)) + (h₂ - (x₂ : Rul Y.d.Xo₂ Y.d.c₂)) := by
        rw [Submodule.coe_add]; abel
      rw [this]
      exact pAdd _ _ p₁ p₂
    | smul c h _ ih =>
      obtain ⟨x, hx, p⟩ := ih
      exact ⟨c • x, Submodule.smul_mem _ _ hx, pSmul2 c h x p⟩
  have hu := GlobalTheory.T.existsUnique_cuspForm_pullback_goodCover D T j Y e o hT hj hY hY.unit hY.modelW a n hDom 0 (zero_mem _)
  have hDiff : ∀ δ ∈ differentIdeal ℤ (𝓞 Y.d.c₂.F), ∀ g ∈ Y.latOver (wtZ a n) S,
      δ • g ∈ Submodule.span (𝓞 Y.d.c₂.F) (π '' ((GlobalTheory.AllWt.latW (T.U j) (wtZ a n) ⊓ C.restrictScalars (𝓞 T.Q.c.F) :
        Submodule (𝓞 T.Q.c.F) (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n))) : Set _)) := by
    intro δ hδ g hg
    have hgl := (Submodule.mem_inf.1 hg).1
    have hgP := (Submodule.mem_inf.1 hg).2
    obtain ⟨x, hx, px⟩ := key _ hgP
    have hgx : ((g : Rul Y.d.Xo₂ Y.d.c₂) - (x : Rul Y.d.Xo₂ Y.d.c₂)) = 0 :=
      hu.unique ⟨sub_mem g.2 x.2, px⟩ ⟨zero_mem _, p0⟩
    have hgx' : g = x := Subtype.ext (sub_eq_zero.1 hgx)
    have h1 := hπD C δ hδ g hgl (hgx' ▸ hx)
    have hset : {f | f ∈ C ∧ f ∈ GlobalTheory.AllWt.latW (T.U j) (wtZ a n)} =
        ((GlobalTheory.AllWt.latW (T.U j) (wtZ a n) ⊓ C.restrictScalars (𝓞 T.Q.c.F) :
          Submodule (𝓞 T.Q.c.F) (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n))) : Set _) := by
      ext f
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem]
      exact And.comm
    rw [hset] at h1
    exact h1
  refine GlobalTheory.SlopeDifferent.slope_sq_sub_le_of_different_smul (K := T.Q.c.F) (K' := Y.d.c₂.F) _ _ π _ _ hG.1 hG₂.1
    ?_ hπli ?_ ?_ ?_ hDiff
  · intro σ f
    rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ]
  · have hle : Y.latOver (wtZ a n) S ≤ GlobalTheory.AllWt.latW Y.U (wtZ a n) := inf_le_left
    haveI := isNoetherian_of_fg_of_noetherian _ hG₂.2.1
    have h1 := (IsNoetherian.noetherian ((Y.latOver (wtZ a n) S).comap (GlobalTheory.AllWt.latW Y.U (wtZ a n)).subtype)).map
      (GlobalTheory.AllWt.latW Y.U (wtZ a n)).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h1
  · intro σ' x
    exact (hπN σ' x).trans (hNc _ _ x)
  · intro x hx
    obtain ⟨hxl, hxC⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨(hπlat x).2 hxl, ?_⟩
    exact hCQ x hxC

end GlobalTheory.CoreRing
