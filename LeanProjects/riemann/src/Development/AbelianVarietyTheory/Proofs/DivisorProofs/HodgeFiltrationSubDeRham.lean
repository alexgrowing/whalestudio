import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientBundleFrameExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFreeLagrangianComplementStatement
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeQuotRank

open GlobalTheory.Published.AbelianDeRham (bcMor)
open GlobalTheory.DeRhamSheaf.VB (exists_transition isAbelianScheme_onAff smooth_onAff bcBasis bcBasis_apply)
open GlobalTheory.Twist (resM resM_resM resM_smul)

theorem span_image_span {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {M M' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (f : M →ₛₗ[σ] M') (s : Set M) :
    Submodule.span R' (f '' Submodule.span R s) = Submodule.span R' (f '' s) := by
  refine le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨m, hm, rfl⟩
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

set_option maxHeartbeats 1000000 in

theorem isVB_cokernel_hodgeSub : GlobalTheory.CovTop.Hypotheses2 → ∀ (p : ℕ) [Fact p.Prime] {T : Scheme.{0}}
    [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∀ F : GlobalTheory.VB.Sub H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ F.sec V ↔ e V hV s ∈ PrimitiveSubmodule (onAff A hV)) →
    GlobalTheory.VB.IsVB (cokernel F.incl) g := by
  intro hP _ _ T _ A _ g hA hg H E hE F hF x
  have hDR := hP.p5
  have hBC := hDR.2.2.1

  have restr : ∀ (D : T.Opens) (hD : IsAffineOpen D)
      (c : Module.Basis (Fin (2 * g)) Γ(T, D) (primDR (onAff A hD))),
      PrimitiveSubmodule (onAff A hD) = Submodule.span Γ(T, D) (c '' {j | (j : ℕ) < g}) →
      ∀ (W : T.Opens) (hW : IsAffineOpen W) (h : W ≤ D),
        ∃ d : Module.Basis (Fin (2 * g)) Γ(T, W) (primDR (onAff A hW)),
          (∀ j, d j = E W hW (resM H h ((E D hD).symm (c j)))) ∧
          PrimitiveSubmodule (onAff A hW) = Submodule.span Γ(T, W) (d '' {j | (j : ℕ) < g}) := by
    intro D hD c hc W hW h
    letI := resAlg h
    obtain ⟨φ, hφ, hφ'⟩ := exists_transition A hD hW h
    obtain ⟨hbc, hF1⟩ := hBC _ (onAff A hD) g (isAbelianScheme_onAff A hA hD) (smooth_onAff A hg hD) _
      (onAff A hW) φ hφ
    have hd : ⇑(bcBasis (bcMor hφ).pull hbc c) = (bcMor hφ).pull ∘ c := funext (bcBasis_apply _ hbc c)
    refine ⟨bcBasis (bcMor hφ).pull hbc c, fun j => ?_, ?_⟩
    · refine (bcBasis_apply _ hbc c j).trans ?_
      rw [hE D W hD hW h φ hφ hφ', LinearEquiv.apply_symm_apply]
    · rw [hF1, hc, span_image_span, hd, Set.image_comp]

  have frame : ∀ (D : T.Opens) (hD : IsAffineOpen D)
      (c : Module.Basis (Fin (2 * g)) Γ(T, D) (primDR (onAff A hD))),
      PrimitiveSubmodule (onAff A hD) = Submodule.span Γ(T, D) (c '' {j | (j : ℕ) < g}) →
      GlobalTheory.VB.IsFrame (F := H) (U := D) fun i => (E D hD).symm (c i) := by
    intro D hD c hc
    refine GlobalTheory.VB.isFrame_of_forall_exists fun V h y hy => ?_
    obtain ⟨W, hW, hyW, hle⟩ := GlobalTheory.QCoh.exists_affine_mem_le y hy
    refine ⟨W, hle, hyW, ?_⟩
    obtain ⟨d, hd, -⟩ := restr D hD c hc W hW (hle.trans h)
    have hl : Fintype.linearCombination Γ(T, W)
        (fun i => resM H (hle.trans h) ((E D hD).symm (c i))) =
          (d.map (E W hW).symm).equivFun.symm.toLinearMap := by
      refine LinearMap.ext fun a => ?_
      rw [Fintype.linearCombination_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply]
      simp only [Module.Basis.map_apply, hd, LinearEquiv.symm_apply_apply]
    rw [hl]
    exact (d.map _).equivFun.symm.bijective

  have affMem : ∀ (D : T.Opens) (hD : IsAffineOpen D)
      (c : Module.Basis (Fin (2 * g)) Γ(T, D) (primDR (onAff A hD))),
      PrimitiveSubmodule (onAff A hD) = Submodule.span Γ(T, D) (c '' {j | (j : ℕ) < g}) →
      ∀ (W : T.Opens) (hW : IsAffineOpen W) (h : W ≤ D) (a : Fin (2 * g) → Γ(T, W)),
        (∑ j, a j • resM H h ((E D hD).symm (c j))) ∈ F.sec W ↔
          ∀ j : Fin (2 * g), g ≤ (j : ℕ) → a j = 0 := by
    intro D hD c hc W hW h a
    obtain ⟨d, hd, hdF⟩ := restr D hD c hc W hW h
    have key : E W hW (∑ j, a j • resM H h ((E D hD).symm (c j))) = ∑ j, a j • d j := by
      simp only [map_sum, map_smul, hd]
    have hrep : ∀ j, d.repr (∑ i, a i • d i) j = a j := fun j => congrFun (d.repr_sum_self a) j
    rw [hF W hW, key, hdF, Module.Basis.mem_span_image]
    constructor
    · intro hs j hj
      by_contra hne
      have := hs (Finsupp.mem_support_iff.2 (by rw [hrep]; exact hne))
      simp only [Set.mem_setOf_eq] at this
      omega
    · intro ha j hj
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hrep] at hj
      simp only [Set.mem_setOf_eq]
      by_contra hlt
      exact hj (ha j (by omega))

  have genMem : ∀ (D : T.Opens) (hD : IsAffineOpen D)
      (c : Module.Basis (Fin (2 * g)) Γ(T, D) (primDR (onAff A hD))),
      PrimitiveSubmodule (onAff A hD) = Submodule.span Γ(T, D) (c '' {j | (j : ℕ) < g}) →
      ∀ (V : T.Opens) (h : V ≤ D) (a : Fin (2 * g) → Γ(T, V)),
        (∑ j, a j • resM H h ((E D hD).symm (c j))) ∈ F.sec V ↔
          ∀ j : Fin (2 * g), g ≤ (j : ℕ) → a j = 0 := by
    intro D hD c hc V h a
    constructor
    · intro hs j hj
      choose W hW hyW hle using fun y : V => GlobalTheory.QCoh.exists_affine_mem_le (y : T) y.2
      refine GlobalTheory.LB.fun_ext_of_cover W hle
        (fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyW _⟩) fun k => ?_
      have hk := F.res_mem (hle k) hs
      have hsum : resM H (hle k) (∑ j, a j • resM H h ((E D hD).symm (c j))) =
          ∑ j, resG T (hle k) (a j) • resM H ((hle k).trans h) ((E D hD).symm (c j)) := by
        simp only [map_sum, resM_smul, resM_resM]
      rw [hsum] at hk
      rw [(affMem D hD c hc (W k) (hW k) ((hle k).trans h) _).1 hk j hj, map_zero]
    · intro ha
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hj : g ≤ (j : ℕ)
      · rw [ha j hj, zero_smul]
        exact Submodule.zero_mem _
      · refine Submodule.smul_mem _ _ (F.res_mem h ?_)
        rw [hF D hD, LinearEquiv.apply_symm_apply, hc]
        exact Submodule.subset_span ⟨j, by simp only [Set.mem_setOf_eq]; omega, rfl⟩

  obtain ⟨V, hV, hxV, -⟩ := GlobalTheory.QCoh.exists_affine_mem_le (U := ⊤) x trivial
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hDR.1
    (isAbelianScheme_onAff A hA hV) (smooth_onAff A hg hV)
  obtain ⟨-, hN, hPfin, hPproj, hPrk⟩ := hDR.2.1 _ (onAff A hV) g (isAbelianScheme_onAff A hA hV)
    (smooth_onAff A hg hV)
  obtain ⟨y, rfl⟩ : ∃ y : V, y.1 = x := ⟨⟨x, hxV⟩, rfl⟩
  obtain ⟨r, hr, hbasis⟩ := GlobalTheory.T.local_free_lagrangian_complement _ _ g (PrimitiveSubmodule (onAff A hV)) hN hfin hproj hrk hPfin hPproj
    hPrk (hV.primeIdealOf y)
  have hD := hV.basicOpen r
  letI := resAlg (T.basicOpen_le r)
  obtain ⟨φ, hφ, -⟩ := exists_transition A hV hD (T.basicOpen_le r)
  obtain ⟨hbc, hF1⟩ := hBC _ (onAff A hV) g (isAbelianScheme_onAff A hA hV) (smooth_onAff A hg hV) _
    (onAff A hD) φ hφ
  letI : Module Γ(T, V) (primDR (onAff A hD)) :=
    Module.compHom _ (algebraMap Γ(T, V) Γ(T, T.basicOpen r))
  haveI : IsScalarTower Γ(T, V) Γ(T, T.basicOpen r) (primDR (onAff A hD)) :=
    ⟨fun a b m => by
      show (a • b) • m = algebraMap Γ(T, V) Γ(T, T.basicOpen r) a • b • m
      rw [Algebra.smul_def, mul_smul]⟩
  let f : primDR (onAff A hV) →ₗ[Γ(T, V)] primDR (onAff A hD) :=
    { toFun := (bcMor hφ).pull
      map_add' := map_add _
      map_smul' := fun a m => (bcMor hφ).pull.map_smulₛₗ a m }
  have hf : IsBaseChange Γ(T, T.basicOpen r) f :=
    IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hbc) fun m => by
      exact (liftSemi_tmul _ 1 m).trans (one_smul _ _)
  haveI := hV.isLocalization_basicOpen r
  have hloc : IsLocalizedModule (Submonoid.powers r) f :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers r) Γ(T, T.basicOpen r) f).2 hf
  obtain ⟨c, hc⟩ := hbasis Γ(T, T.basicOpen r) (primDR (onAff A hD)) f hloc
  have hc' : PrimitiveSubmodule (onAff A hD) = Submodule.span Γ(T, T.basicOpen r) (c '' {j | (j : ℕ) < g}) := by
    rw [hF1, ← hc]
    rfl
  have key := GlobalTheory.VB.exists_isFrame_cokernel_of_frame F _ (frame _ hD c hc') g (by omega)
    (genMem _ hD c hc')
  rw [show 2 * g - g = g by omega] at key
  obtain ⟨e', he'⟩ := key
  exact ⟨_, e', (GlobalTheory.QCoh.mem_primeCompl_primeIdealOf_iff hV y r).1 hr, he'⟩

end GlobalTheory.HodgeQuotRank
