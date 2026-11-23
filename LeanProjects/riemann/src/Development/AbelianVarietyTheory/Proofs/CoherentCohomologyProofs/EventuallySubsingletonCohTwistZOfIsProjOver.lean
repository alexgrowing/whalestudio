import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsResMEqSecHomSecToPow
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegree
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteGrCechHomology
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.VeryAmpleCompactQuasiSeparatedAffineCharts
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemSaturationOfPowSmulMem

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite Filter DirectSum
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.ProjSpace (secRatio)

namespace GlobalTheory

section Algebra

variable {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
  [Module A N]

def submodulePowSat (g : A) (K : Submodule A M) : Submodule A M := GlobalTheory.SubmoduleSaturation.saturation g K

theorem mem_submodulePowSat {g : A} {K : Submodule A M} {m : M} :
    m ∈ submodulePowSat g K ↔ ∃ k : ℕ, g ^ k • m ∈ K := Iff.rfl

theorem le_submodulePowSat (g : A) (K : Submodule A M) : K ≤ submodulePowSat g K :=
  fun m hm => ⟨0, by rwa [pow_zero, one_smul]⟩

theorem mem_submodulePowSat_of_pow_smul_mem {g : A} {K : Submodule A M} {m : M} {l : ℕ}
    (h : g ^ l • m ∈ submodulePowSat g K) : m ∈ submodulePowSat g K := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + l, by rwa [pow_add, mul_smul]⟩

theorem exists_fg_submodulePowSat_eq_top {g : A} (f : M →ₗ[A] N)
    (h₁ : ∀ m, f m = 0 → ∃ k : ℕ, g ^ k • m = 0) (h₂ : ∀ z, ∃ (k : ℕ) (m : M), f m = g ^ k • z)
    {K : Submodule A N} (hK : K.FG) (h : submodulePowSat g K = ⊤) :
    ∃ K' : Submodule A M, K'.FG ∧ submodulePowSat g K' = ⊤ := by
  obtain ⟨T, hT, rfl⟩ := Submodule.fg_def.1 hK
  choose k y hy using h₂
  refine ⟨Submodule.span A (y '' T), Submodule.fg_span (hT.image y), eq_top_iff.2 fun m _ => ?_⟩
  have h₃ : Submodule.span A T ≤ submodulePowSat g ((Submodule.span A (y '' T)).map f) :=
    Submodule.span_le.2 fun t ht =>
      ⟨k t, y t, Submodule.subset_span (Set.mem_image_of_mem y ht), hy t⟩
  obtain ⟨a, ha⟩ : f m ∈ submodulePowSat g (Submodule.span A T) := h ▸ Submodule.mem_top
  obtain ⟨b, m', hm', e⟩ := mem_submodulePowSat_of_pow_smul_mem (h₃ ha)
  obtain ⟨c, hc⟩ := h₁ (g ^ b • m - m') (by rw [map_sub, map_smul, e, sub_self])
  refine ⟨c + b, ?_⟩
  rw [smul_sub, sub_eq_zero] at hc
  rw [pow_add, mul_smul, hc]
  exact Submodule.smul_mem _ _ hm'

end Algebra

theorem exists_fg_isHomogeneous_ge {ι R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
    (ℳ : ℤ → Submodule R M) [Decomposition ℳ] [PolyGradedSMul ι ℳ]
    {K : Submodule (MvPolynomial ι R) M} (hK : K.FG) :
    ∃ K' : Submodule (MvPolynomial ι R) M, K'.FG ∧ K'.IsHomogeneous ℳ ∧ K ≤ K' := by
  obtain ⟨T, hT, rfl⟩ := Submodule.fg_def.1 hK
  choose D hD using exists_sum_grProj ℳ
  refine ⟨Submodule.span _ (⋃ t ∈ T, (fun j => GradedHilbert.proj ℳ j t) '' D t),
    Submodule.fg_span (hT.biUnion fun t _ => (D t).finite_toSet.image _),
    isHomogeneous_span_gr ℳ fun g hg => ?_, Submodule.span_le.2 fun t ht => ?_⟩
  · simp only [Set.mem_iUnion] at hg
    obtain ⟨t, -, j, -, rfl⟩ := hg
    exact ⟨j, GradedHilbert.proj_mem ℳ j t⟩
  · rw [← hD t]
    exact Submodule.sum_mem _ fun j hj =>
      Submodule.subset_span (Set.mem_biUnion ht ⟨j, hj, rfl⟩)

namespace Twist

open MvPolynomial

variable {X : Scheme.{0}} {L : LB X} {ι : Type}
variable (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] (x : ι → LB.Sec L)

def ratioEval (i : ι) : MvPolynomial ι R →+* Γ(X, nonzeroLocus (x i)) :=
  eval₂Hom ((resG X le_top).comp (algebraMap R Γ(X, ⊤))) fun j => secRatio (x i) (x j)

@[simp] theorem ratioEval_C (i : ι) (r : R) :
    ratioEval R x i (C r) = resG X le_top (algebraMap R Γ(X, ⊤) r) := eval₂Hom_C _ _ r

@[simp] theorem ratioEval_X (i j : ι) :
    ratioEval R x i (MvPolynomial.X j) = secRatio (x i) (x j) := eval₂Hom_X' _ _ j

theorem finite_ratioEval_iff (i : ι) : (ratioEval R x i).Finite ↔
    Module.Finite (ratioEval R x i).range Γ(X, nonzeroLocus (x i)) :=
  ⟨fun h => RingHom.Finite.of_comp_finite (f := (ratioEval R x i).rangeRestrict)
      (g := (ratioEval R x i).range.subtype) h,
    fun h => RingHom.Finite.comp (g := (ratioEval R x i).range.subtype) h
      (RingHom.Finite.of_surjective _ (ratioEval R x i).rangeRestrict_surjective)⟩

variable (F : X.Modules)

theorem X_smul_gammaOf_secRatio_smul (i j : ι) (n : ℤ)
    (b : Γ(twistZ F L n, nonzeroLocus (x i))) :
    (MvPolynomial.X i : MvPolynomial ι R) • gammaOf R x F _ n
        ((sectionsOn.toΓ _ _).symm (secRatio (x i) (x j) • b)) =
      (MvPolynomial.X j : MvPolynomial ι R) • gammaOf R x F _ n ((sectionsOn.toΓ _ _).symm b) := by
  rw [GrSum.X_smul_of, GrSum.X_smul_of]
  refine congrArg _ (zsec_ext (F := F) fun k => ?_)
  refine (zcoord_mulSecOfEq_app (zofSec (x i)) rfl (secRatio (x i) (x j) • b) k).trans
    (Eq.trans ?_ (zcoord_mulSecOfEq_app (zofSec (x j)) rfl b k).symm)
  rw [zcoord_smul, zfun_zofSec, zfun_zofSec, smul_smul, mul_comm, ← ProjSpace.secRatio_spec]

theorem exists_fg_submodulePowSat_gammaStar_locus [QCoh.IsFiniteQC F] (hL : L.IsLB) {i : ι}
    (ha : IsAffineOpen (nonzeroLocus (x i))) (hf : (ratioEval R x i).Finite) :
    ∃ K : Submodule (MvPolynomial ι R) (GammaStar R x F (nonzeroLocus (x i))),
      K.FG ∧ submodulePowSat (MvPolynomial.X i) K = ⊤ := by
  have := isFiniteQC_twist (F := F) (isLB_lbZPow hL 0)
  have := QCoh.finite_sections (twistZ F L 0) ha
  letI := (ratioEval R x i).toAlgebra
  letI : Module (MvPolynomial ι R) Γ(twistZ F L 0, nonzeroLocus (x i)) :=
    Module.compHom _ (ratioEval R x i)
  have : IsScalarTower (MvPolynomial ι R) Γ(X, nonzeroLocus (x i))
      Γ(twistZ F L 0, nonzeroLocus (x i)) := ⟨fun p a b => mul_smul _ a b⟩
  have : Module.Finite (MvPolynomial ι R) Γ(X, nonzeroLocus (x i)) := hf
  obtain ⟨T, hT, hs⟩ := Submodule.fg_def.1 (Module.Finite.trans (R := MvPolynomial ι R)
    Γ(X, nonzeroLocus (x i)) Γ(twistZ F L 0, nonzeroLocus (x i))).fg_top
  let o : Γ(twistZ F L 0, nonzeroLocus (x i)) →+ GammaStar R x F (nonzeroLocus (x i)) :=
    (gammaOf R x F _ 0).toAddMonoidHom.comp (sectionsOn.toΓ _ _).symm.toAddMonoidHom
  refine ⟨Submodule.span _ (o '' T), Submodule.fg_span (hT.image o), ?_⟩
  set P := submodulePowSat (MvPolynomial.X i : MvPolynomial ι R) (Submodule.span _ (o '' T))
  have sat : ∀ z, (MvPolynomial.X i : MvPolynomial ι R) • z ∈ P → z ∈ P := fun z hz =>
    mem_submodulePowSat_of_pow_smul_mem (l := 1) (by rwa [pow_one])
  have hsmul : ∀ (p : MvPolynomial ι R) b, o b ∈ P → o (ratioEval R x i p • b) ∈ P := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r =>
      intro b hb
      have e : o (ratioEval R x i (C r) • b) = r • o b := by
        rw [ratioEval_C]
        exact (gammaOf R x F _ 0).map_smul r ((sectionsOn.toΓ _ _).symm b)
      rw [e]
      exact P.smul_of_tower_mem r hb
    | add p q hp hq =>
      intro b hb
      rw [map_add, add_smul, map_add]
      exact P.add_mem (hp b hb) (hq b hb)
    | mul_X p j hp =>
      intro b hb
      rw [map_mul, mul_smul, ratioEval_X]
      refine hp _ (sat _ ?_)
      exact (X_smul_gammaOf_secRatio_smul R x F i j 0 b).symm ▸ P.smul_mem _ hb
  have h₀ : ∀ b, o b ∈ P := fun b => by
    have hb : b ∈ Submodule.span (MvPolynomial ι R) T := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem t ht => exact le_submodulePowSat _ _ (Submodule.subset_span ⟨t, ht, rfl⟩)
    | zero => rw [map_zero]; exact P.zero_mem
    | add a b _ _ ha hb => rw [map_add]; exact P.add_mem ha hb
    | smul p b _ hb => exact hsmul p b hb
  have step : ∀ n : ℤ, (∀ b, gammaOf R x F _ n b ∈ P) ↔ ∀ b, gammaOf R x F _ (n + 1) b ∈ P :=
    fun n => ⟨fun h b => by
      obtain ⟨a, rfl⟩ := (gammaOp_bijective R x F hL (j := i) le_rfl n).2 b
      rw [← GrSum.X_smul_of]
      exact P.smul_mem _ (h a), fun h b => sat _ (by rw [GrSum.X_smul_of]; exact h _)⟩
  have hn : ∀ (n : ℤ) b, gammaOf R x F _ n b ∈ P := fun n => by
    induction n using Int.induction_on with
    | zero => exact fun b => h₀ (sectionsOn.toΓ _ _ b)
    | succ n ih => exact (step n).1 ih
    | pred n ih => exact (step _).2 (by rwa [sub_add_cancel])
  refine eq_top_iff.2 fun z _ => ?_
  induction z using Decomposition.inductionOn (gammaGrading R x F (nonzeroLocus (x i))) with
  | zero => exact P.zero_mem
  | @homogeneous n m => obtain ⟨_, b, rfl⟩ := m; exact hn n b
  | add a b ha hb => exact P.add_mem (ha trivial) (hb trivial)

section System

variable [Finite ι] [QCoh.IsFiniteQC F] (hL : L.IsLB) (hc : ⨆ i, nonzeroLocus (x i) = ⊤)
  (ha : ∀ i, IsAffineOpen (nonzeroLocus (x i))) (hf : ∀ i, (ratioEval R x i).Finite)
include hL hc ha hf

theorem exists_fg_isHomogeneous_submodulePowSat :
    ∃ M : Submodule (MvPolynomial ι R) (GammaStar R x F ⊤), M.FG ∧
      M.IsHomogeneous (gammaGrading R x F ⊤) ∧
      ∀ i, submodulePowSat (MvPolynomial.X i) M = ⊤ := by
  have := VeryAmpleCharts.compactSpace_of_finite_cover _ hc ha
  have := VeryAmpleCharts.quasiSeparatedSpace_of_cover hL x hc ha
  have := Fintype.ofFinite ι
  have H (i : ι) : ∃ K : Submodule (MvPolynomial ι R) (GammaStar R x F ⊤),
      K.FG ∧ submodulePowSat (MvPolynomial.X i) K = ⊤ := by
    obtain ⟨K, hK, e⟩ := exists_fg_submodulePowSat_gammaStar_locus R x F hL (ha i) (hf i)
    have hV : nonzeroLocus (x i) = ⊤ ⊓ ⨅ j ∈ ({i} : Finset ι), nonzeroLocus (x j) := by simp
    refine exists_fg_submodulePowSat_eq_top (gammaRes R x F le_top) (fun m hm => ?_) (fun z => ?_)
      hK e
    · simpa using
        (eventually_xProd_pow_smul_eq_zero R x F hL isCompact_univ le_top hV.ge m hm).exists
    · simpa using (eventually_exists_gammaRes_eq R x F hL isCompact_univ
        isQuasiSeparated_univ le_top hV z).exists
  choose K hK e using H
  obtain ⟨M, hM, hM', hle⟩ := exists_fg_isHomogeneous_ge (gammaGrading R x F ⊤)
    (Submodule.fg_iSup K hK)
  refine ⟨M, hM, hM', fun i => eq_top_iff.2 fun m _ => ?_⟩
  obtain ⟨k, hk⟩ : m ∈ submodulePowSat (MvPolynomial.X i) (K i) := e i ▸ Submodule.mem_top
  exact ⟨k, hle (le_iSup K i hk)⟩

theorem exists_fg_cech_iso_grCech :
    ∃ M : Submodule (MvPolynomial ι R) (GammaStar R x F ⊤), M.FG ∧
      M.IsHomogeneous (gammaGrading R x F ⊤) ∧
      (∀ s : Finset ι, s.Nonempty → ∀ n : ℤ, Function.Bijective
        (homLocMap (isGradedMap_subtype (gammaGrading R x F ⊤) M) s n)) ∧
      ∀ [LinearOrder ι] (n : ℤ), Nonempty (cech R (twistZ F L n) ⊤ (fun j => nonzeroLocus (x j)) ≅
        grCech ι (grSub (gammaGrading R x F ⊤) M) n) := by
  have := VeryAmpleCharts.compactSpace_of_finite_cover _ hc ha
  have := VeryAmpleCharts.quasiSeparatedSpace_of_cover hL x hc ha
  obtain ⟨M, hM, hM', e⟩ := exists_fg_isHomogeneous_submodulePowSat R x F hL hc ha hf
  letI := grSubDecomposition _ hM'
  have h₁ (i : ι) (m : M) (hm : M.subtype m = 0) :
      ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • m = 0 :=
    ⟨0, by rw [show m = 0 from Subtype.ext hm, smul_zero]⟩
  have h₂ (i : ι) (y : GammaStar R x F ⊤) :
      ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y ∈ LinearMap.range M.subtype := by
    rw [Submodule.range_subtype]
    exact mem_submodulePowSat.1 (e i ▸ Submodule.mem_top)
  refine ⟨M, hM, hM', fun s ⟨i, hi⟩ n => homLocMap_bijective_of_X _ hi (h₁ i) (h₂ i) n,
    fun n => ?_⟩
  have := isIso_grCechMap (isGradedMap_subtype (gammaGrading R x F ⊤) M) h₁ h₂ n
  exact ⟨(asIso (grCechMap (isGradedMap_subtype (gammaGrading R x F ⊤) M) n) ≪≫
    gammaCechIso R x F hL isCompact_univ isQuasiSeparated_univ n).symm⟩

theorem exists_fg_coh_equiv_grH [LinearOrder ι] :
    ∃ M : Submodule (MvPolynomial ι R) (GammaStar R x F ⊤), M.FG ∧
      M.IsHomogeneous (gammaGrading R x F ⊤) ∧ ∀ (n : ℤ) (p : ℕ),
        Nonempty (grH ι (grSub (gammaGrading R x F ⊤) M) n p ≃ₗ[R] coh (twistZ F L n) p) := by
  obtain ⟨M, hM, hM', -, e⟩ := exists_fg_cech_iso_grCech R x F hL hc ha hf
  refine ⟨M, hM, hM', fun n p => (e n).elim fun e => ?_⟩
  have := isQuasicoherent_twist (F := F) (isLB_lbZPow hL n)
  exact ⟨(HomologicalComplex.homologyMapIso e p).toLinearEquiv.symm.trans
    (cechHEquivCoh R hc (VeryAmpleCharts.isAffineOpen_biInf_nonzeroLocus hL x ha) _ p)⟩

variable [IsNoetherianRing R]

theorem finite_coh_twistZ (n : ℤ) (p : ℕ) : Module.Finite R (coh (twistZ F L n) p) := by
  classical
  have := Fintype.ofFinite ι
  letI := linearOrderOfSTO (WellOrderingRel (α := ι))
  obtain ⟨M, hM, hM', e⟩ := exists_fg_coh_equiv_grH R x F hL hc ha hf
  letI := grSubDecomposition _ hM'
  have : Module.Finite R (grH ι (grSub (gammaGrading R x F ⊤) M) n p) :=
    finite_grCech_homology ι R M _ (Module.Finite.iff_fg.2 hM) n p
  exact (e n p).elim Module.Finite.equiv

theorem eventually_subsingleton_coh_twistZ :
    ∀ᶠ n : ℤ in atTop, ∀ p, 0 < p → Subsingleton (coh (twistZ F L n) p) := by
  classical
  have := Fintype.ofFinite ι
  letI := linearOrderOfSTO (WellOrderingRel (α := ι))
  obtain ⟨M, hM, hM', e⟩ := exists_fg_coh_equiv_grH R x F hL hc ha hf
  letI := grSubDecomposition _ hM'
  obtain ⟨n₀, h⟩ := cubeComplex_grCube_exactAt_of_finite ι R M
    (grSub (gammaGrading R x F ⊤) M) (Module.Finite.iff_fg.2 hM)
  refine eventually_atTop.2 ⟨n₀, fun n hn p hp => ?_⟩
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have : Subsingleton (grH ι (grSub (gammaGrading R x F ⊤) M) n (p + 1)) :=
    ModuleCat.isZero_iff_subsingleton.1 ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      ((cechComplex_exactAt_succ_iff_cube _ p).2 (h n hn (p + 2))))
  exact (e n (p + 1)).elim fun e => e.symm.injective.subsingleton

theorem finite_coh (p : ℕ) : Module.Finite R (coh F p) :=
  have := finite_coh_twistZ R x F hL hc ha hf 0 p
  Module.Finite.equiv (cohOn.mapIso R ⊤ p (twistZZeroIso F hL)).symm

end System

end Twist

namespace ProjSpace

open MvPolynomial QCoh.Qcqs Cartier

variable {R : Type} [CommRing R] {N : ℕ} {X : Scheme.{0}} {L : LB X}

set_option backward.isDefEq.respectTransparency.types false in

theorem isFinite_iff_pullRatio (φ : X ⟶ PSpace R N) {U : Fin (N + 1) → X.Opens}
    (hU : ∀ i, φ ⁻¹ᵁ chart R N i = U i) :
    IsFinite φ ↔ ∀ i, IsAffineOpen (U i) ∧ RingHom.Finite
      (eval₂Hom (baseRingHom (φ ≫ PSpace.str R N) (U i)).hom (pullRatio φ (U i) i (hU i).ge)) := by
  obtain rfl : (fun i => φ ⁻¹ᵁ chart R N i) = U := funext hU
  have key : ∀ i, RingHom.Finite (eval₂Hom
      (baseRingHom (φ ≫ PSpace.str R N) (φ ⁻¹ᵁ chart R N i)).hom
      (pullRatio φ (φ ⁻¹ᵁ chart R N i) i (hU i).ge)) ↔ (φ.app (chart R N i)).hom.Finite :=
    fun i => by
      rw [← appLE_comp_aeval_ratio, Scheme.Hom.app_eq_appLE]
      exact ⟨RingHom.Finite.of_comp_finite,
        fun h => h.comp (RingHom.Finite.of_surjective _ (aeval_ratio_surjective R N i))⟩
  simp only [key]
  refine ⟨fun _ i => ⟨(isAffineOpen_chart R N i).preimage φ,
    φ.finite_app _ (isAffineOpen_chart R N i)⟩, fun h => ?_⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _ (iSup_chart R N)).2
    fun i => ?_
  rw [MorphismProperty.arrow_mk_iso_iff @IsFinite
    (Arrow.isoMk (h i).1.isoSpec (isAffineOpen_chart R N i).isoSpec
      (Scheme.Opens.toSpecΓ_naturality φ _) :
      Arrow.mk (φ ∣_ chart R N i) ≅ Arrow.mk (Spec.map (φ.app (chart R N i))))]
  exact (IsFinite.SpecMap_iff _).2 (h i).2

theorem isAffineHom_of_isAffineOpen_preimage_chart (φ : X ⟶ PSpace R N)
    (h : ∀ i, IsAffineOpen (φ ⁻¹ᵁ chart R N i)) : IsAffineHom φ :=
  isAffineHom_of_forall_exists_isAffineOpen φ fun y =>
    (exists_mem_chart R N y).elim fun i hi => ⟨_, hi, isAffineOpen_chart R N i, h i⟩

variable (f : X ⟶ Sp R) (s : Fin (N + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤)

theorem isFinite_toProj_of_isProper [IsProper f] (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i))) :
    IsFinite (toProj f s hs) := by
  have := isProper_str R N
  have : IsProper (toProj f s hs ≫ PSpace.str R N) := by rwa [toProj_str]
  exact IsFinite.iff_isProper_and_isAffineHom.2 ⟨IsProper.of_comp _ (PSpace.str R N),
    isAffineHom_of_isAffineOpen_preimage_chart _ fun i => by
      rw [toProj_preimage_chart]; exact ha i⟩

variable [Algebra R Γ(X, ⊤)]
  (hf : ∀ r, algebraMap R Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of R)).inv r))
include hf

theorem isFinite_toProj_iff : IsFinite (toProj f s hs) ↔
    ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧ (Twist.ratioEval R s i).Finite := by
  rw [isFinite_iff_pullRatio _ (toProj_preimage_chart f s hs), toProj_str]
  refine forall_congr' fun i => ?_
  have e : (baseRingHom f (nonzeroLocus (s i))).hom =
      (resG X le_top).comp (algebraMap R Γ(X, ⊤)) := RingHom.ext fun r => by
    rw [RingHom.comp_apply, hf]
    rfl
  rw [funext (pullRatio_toProj f s hs i), e]
  rfl

end ProjSpace

section Proj

open QCoh Twist ProjSpace CechPic

variable {R : Type} [CommRing R] {X : Scheme.{0}} [Algebra R Γ(X, ⊤)] {f : X ⟶ Sp R}
  (hf : ∀ r, algebraMap R Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of R)).inv r))
include hf

theorem ProjSpace.secPull_coord_of_isFinite {N : ℕ} (φ : X ⟶ PSpace R N) [IsFinite φ]
    (hφ : φ ≫ PSpace.str R N = f) :
    ⨆ i, nonzeroLocus (secPull (coord R N i) φ) = ⊤ ∧
      ∀ i, IsAffineOpen (nonzeroLocus (secPull (coord R N i) φ)) ∧
        (ratioEval R (fun j => secPull (coord R N j) φ) i).Finite := by
  subst hφ
  have hs := iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R N) φ
  exact ⟨hs, (isFinite_toProj_iff _ _ hs hf).1 (by rwa [toProj_secPull_coord])⟩

theorem Twist.finite_ratioEval_of_isProper [IsProper f] {L : LB X} {N : ℕ}
    (x : Fin (N + 1) → L.Sec) (hc : ⨆ i, nonzeroLocus (x i) = ⊤)
    (ha : ∀ i, IsAffineOpen (nonzeroLocus (x i))) (i : Fin (N + 1)) :
    (ratioEval R x i).Finite :=
  ((isFinite_toProj_iff f x hc hf).1 (isFinite_toProj_of_isProper f x hc ha) i).2

variable [IsNoetherianRing R] (F : X.Modules) [IsFiniteQC F]

theorem serre_of_isFinite {N : ℕ} (φ : X ⟶ PSpace R N) [IsFinite φ]
    (hφ : φ ≫ PSpace.str R N = f) :
    (∀ (n : ℤ) (p : ℕ), Module.Finite R (coh (twistZ F ((O1 R N).pull φ) n) p)) ∧
      ∀ᶠ n : ℤ in atTop, ∀ p, 0 < p → Subsingleton (coh (twistZ F ((O1 R N).pull φ) n) p) :=
  have h := secPull_coord_of_isFinite hf φ hφ
  have hL := Semi.LB.isLB_pull (O1_isLB R N) φ
  ⟨finite_coh_twistZ R _ F hL h.1 (fun i => (h.2 i).1) fun i => (h.2 i).2,
    eventually_subsingleton_coh_twistZ R _ F hL h.1 (fun i => (h.2 i).1) fun i => (h.2 i).2⟩

theorem IsAmpleLB.finite_coh [IsProper f] {L : LB X} (h : IsAmpleLB L) (p : ℕ) :
    Module.Finite R (coh F p) := by
  obtain ⟨m, -, N, s, hs, ha⟩ := h.exists_cover
  exact Twist.finite_coh R s F (isLB_lbZPow h.isLB m) hs ha
    (finite_ratioEval_of_isProper hf s hs ha) p

theorem IsAmpleLB.eventually_subsingleton_coh_twistZ [IsProper f] {L : LB X} (h : IsAmpleLB L) :
    ∀ᶠ n : ℤ in atTop, ∀ p, 0 < p → Subsingleton (coh (twistZ F L n) p) := by
  obtain ⟨m, hm, N, s, hs, ha⟩ := h.exists_cover
  have hL := h.isLB
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have H (r : Fin m) : ∃ q : ℤ, ∀ n ≥ q, ∀ p, 0 < p →
      Subsingleton (coh (twistZ (twistZ F L r) (lbZPow L m) n) p) :=
    have := isFiniteQC_twist (F := F) (isLB_lbZPow hL r)
    eventually_atTop.1 (Twist.eventually_subsingleton_coh_twistZ R s
      (twistZ F L r) (isLB_lbZPow hL m) hs ha (finite_ratioEval_of_isProper hf s hs ha))
  choose q hq using H
  obtain ⟨Q, hQ⟩ := Finite.exists_le q
  refine eventually_atTop.2 ⟨Q * m, fun n hn p hp => ?_⟩
  obtain ⟨r, hr⟩ : ∃ r : Fin m, ((r : ℕ) : ℤ) = n % m :=
    ⟨⟨(n % m).toNat, by have := Int.emod_lt_of_pos n hm'; omega⟩,
      Int.toNat_of_nonneg (Int.emod_nonneg n hm'.ne')⟩
  have := hq r (n / m) ((hQ r).trans ((Int.le_ediv_iff_mul_le hm').2 hn)) p hp
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq F (isLB_lbZPow hL r)
    (isLB_lbZPow (isLB_lbZPow hL m) (n / m)) (isLB_lbZPow hL n) (by
      rw [cls_lbZPow hL, cls_lbZPow hL, cls_lbZPow (isLB_lbZPow hL m), cls_lbZPow hL, smul_smul,
        ← add_smul, hr, Int.emod_add_ediv_mul])
  exact (cohOn.mapIso R ⊤ p e).symm.injective.subsingleton

theorem IsAmpleLB.eventually_subsingleton_coh_twist [IsProper f] {L : LB X} (h : IsAmpleLB L) :
    ∀ᶠ n : ℕ in atTop, ∀ p, 0 < p → Subsingleton (coh (twist F (lbPow L n)) p) :=
  tendsto_natCast_atTop_atTop.eventually (h.eventually_subsingleton_coh_twistZ hf F)

omit hf [IsNoetherianRing R] [Algebra R Γ(X, ⊤)] in

theorem isProper_and_exists_isAmpleLB_of_isProjOver (h : IsProjOver f) :
    IsProper f ∧ ∃ L : LB X, IsAmpleLB L := by
  obtain ⟨N, φ, _, rfl⟩ := h
  have := isProper_str R N
  exact ⟨inferInstance, _, (isAmple_projective_O_one R N).pull_of_isAffineHom φ⟩

theorem finite_coh_of_isProjOver (h : IsProjOver f) (p : ℕ) : Module.Finite R (coh F p) := by
  obtain ⟨_, L, hL⟩ := isProper_and_exists_isAmpleLB_of_isProjOver h
  exact hL.finite_coh hf F p

theorem finite_coh_twist_of_isProjOver (h : IsProjOver f) {M : LB X} (hM : M.IsLB) (p : ℕ) :
    Module.Finite R (coh (twist F M) p) :=
  have := isFiniteQC_twist (F := F) hM
  finite_coh_of_isProjOver hf _ h p

theorem eventually_subsingleton_coh_twistZ_of_isProjOver (h : IsProjOver f) {L : LB X}
    (hL : IsAmpleLB L) : ∀ᶠ n : ℤ in atTop, ∀ p, 0 < p → Subsingleton (coh (twistZ F L n) p) :=
  have := (isProper_and_exists_isAmpleLB_of_isProjOver h).1
  hL.eventually_subsingleton_coh_twistZ hf F

end Proj

section Field

open QCoh

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {f : X ⟶ Sp k}
  (hf : ∀ r, algebraMap k Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of k)).inv r))
  (F : X.Modules) [IsFiniteQC F]
include hf

theorem IsAmpleLB.finiteCoh [IsProper f] {L : LB X} (h : IsAmpleLB L) : FiniteCoh k F := by
  obtain ⟨m, -, N, s, hs, ha⟩ := h.exists_cover
  exact ⟨h.finite_coh hf F, _, fun n hn => coh.subsingleton_of_card_le hs
    (VeryAmpleCharts.isAffineOpen_biInf_nonzeroLocus (Twist.isLB_lbZPow h.isLB m) s ha) F hn⟩

theorem finiteCoh_of_isProjOver (h : IsProjOver f) : FiniteCoh k F := by
  obtain ⟨_, L, hL⟩ := isProper_and_exists_isAmpleLB_of_isProjOver h
  exact hL.finiteCoh hf F

theorem finiteCohTwists_of_isProjOver (h : IsProjOver f) : FiniteCohTwists k F := fun _ hM =>
  have := Twist.isFiniteQC_twist (F := F) hM
  finiteCoh_of_isProjOver hf _ h

end Field

open QCoh Twist ProjSpace in

theorem serre_finiteness_vanishing (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0})
    [Algebra R Γ(X, ⊤)] (F : X.Modules) [IsFiniteQC F] :
    (∀ (L : LB X) (ι : Type) [Finite ι] (x : ι → L.Sec), L.IsLB → ⨆ i, nonzeroLocus (x i) = ⊤ →
      (∀ i, IsAffineOpen (nonzeroLocus (x i))) →
      (∀ i, Module.Finite (ratioEval R x i).range Γ(X, nonzeroLocus (x i))) →
      (∃ M : Submodule (MvPolynomial ι R) (GammaStar R x F ⊤), M.FG ∧
        M.IsHomogeneous (gammaGrading R x F ⊤) ∧
        (∀ s : Finset ι, s.Nonempty → ∀ n : ℤ, Function.Bijective
          (homLocMap (isGradedMap_subtype (gammaGrading R x F ⊤) M) s n)) ∧
        ∀ [LinearOrder ι] (n : ℤ),
          Nonempty (cech R (twistZ F L n) ⊤ (fun j => nonzeroLocus (x j)) ≅
            grCech ι (grSub (gammaGrading R x F ⊤) M) n)) ∧
      (∀ (n : ℤ) (p : ℕ), Module.Finite R (coh (twistZ F L n) p)) ∧
      ∀ᶠ n : ℤ in atTop, ∀ p, 0 < p → Subsingleton (coh (twistZ F L n) p)) ∧
    ∀ f : X ⟶ Sp R,
      (∀ r, algebraMap R Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) →
      (∀ (N : ℕ) (φ : X ⟶ PSpace R N), IsFinite φ ∨ IsClosedImmersion φ →
        φ ≫ PSpace.str R N = f →
        ⨆ i, nonzeroLocus (secPull (coord R N i) φ) = ⊤ ∧
        (∀ i, IsAffineOpen (nonzeroLocus (secPull (coord R N i) φ))) ∧
        (∀ i, Module.Finite (ratioEval R (fun j => secPull (coord R N j) φ) i).range
          Γ(X, nonzeroLocus (secPull (coord R N i) φ))) ∧
        (∀ (n : ℤ) (p : ℕ), Module.Finite R (coh (twistZ F ((O1 R N).pull φ) n) p)) ∧
        ∀ᶠ n : ℤ in atTop, ∀ p, 0 < p → Subsingleton (coh (twistZ F ((O1 R N).pull φ) n) p)) ∧
      (IsProjOver f ∨ (IsProper f ∧ ∃ A : LB X, IsAmpleLB A) →
        (∀ p, Module.Finite R (coh F p)) ∧
        (∀ M : LB X, M.IsLB → ∀ p, Module.Finite R (coh (twist F M) p)) ∧
        ∀ L : LB X, IsAmpleLB L →
          (∀ (n : ℤ) (p : ℕ), Module.Finite R (coh (twistZ F L n) p)) ∧
          (∀ᶠ n : ℤ in atTop, ∀ p, 0 < p → Subsingleton (coh (twistZ F L n) p)) ∧
          ∀ᶠ n : ℕ in atTop, ∀ p, 0 < p → Subsingleton (coh (twist F (lbPow L n)) p)) := by
  refine ⟨fun L ι _ x hL hc ha h => ?_, fun f hf => ⟨fun N φ hφ e => ?_, fun h => ?_⟩⟩
  · have h' := fun i => (finite_ratioEval_iff R x i).2 (h i)
    exact ⟨exists_fg_cech_iso_grCech R x F hL hc ha h', finite_coh_twistZ R x F hL hc ha h',
      eventually_subsingleton_coh_twistZ R x F hL hc ha h'⟩
  · have : IsFinite φ := hφ.elim id fun _ => inferInstance
    have h := secPull_coord_of_isFinite hf φ e
    exact ⟨h.1, fun i => (h.2 i).1, fun i =>
      (finite_ratioEval_iff R (fun j => secPull (coord R N j) φ) i).1 (h.2 i).2,
      serre_of_isFinite hf F φ e⟩
  · obtain ⟨_, A, hA⟩ := h.elim isProper_and_exists_isAmpleLB_of_isProjOver id
    have H (M : LB X) (hM : M.IsLB) (p : ℕ) : Module.Finite R (coh (twist F M) p) :=
      have := isFiniteQC_twist (F := F) hM
      hA.finite_coh hf _ p
    exact ⟨hA.finite_coh hf F, H, fun L hL => ⟨fun n => H _ (isLB_lbZPow hL.isLB n),
      hL.eventually_subsingleton_coh_twistZ hf F, hL.eventually_subsingleton_coh_twist hf F⟩⟩

example :
    letI := algebraΓOfHom (PSpace.str ℤ 2)
    ∀ᶠ n : ℤ in atTop, ∀ p, 0 < p →
      Subsingleton (coh (twistZ (QCoh.structureModule _) (ProjSpace.O1 ℤ 2) n) p) :=
  letI := algebraΓOfHom (PSpace.str ℤ 2)
  eventually_subsingleton_coh_twistZ_of_isProjOver (f := PSpace.str ℤ 2) (fun _ => rfl) _
    ⟨2, 𝟙 _, inferInstance, Category.id_comp _⟩ (isAmple_projective_O_one ℤ 2)

example (k : Type) [Field k] (N : ℕ) :
    letI := algebraΓOfHom (PSpace.str k N)
    FiniteCohTwists k (QCoh.structureModule (PSpace k N)) :=
  letI := algebraΓOfHom (PSpace.str k N)
  finiteCohTwists_of_isProjOver (f := PSpace.str k N) (fun _ => rfl) _
    ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩

end GlobalTheory
