import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftClosed
open GlobalTheory.QCoh GlobalTheory.Twist

theorem res_eq {X : Scheme.{0}} (I : X.IdealSheafData) {V W : X.Opens} (h : W ≤ V)
    (x : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V)) :
    structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ W)
      (resM ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme)) h
        ((structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ V)).symm x)) =
      (I.subscheme.presheaf.map (homOfLE (fun _ hz => h hz :
        I.subschemeι ⁻¹ᵁ W ≤ I.subschemeι ⁻¹ᵁ V)).op).hom x := rfl

theorem smul_eq {X : Scheme.{0}} (I : X.IdealSheafData) {W : X.Opens} (r : Γ(X, W))
    (m : Γ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme), W)) :
    structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ W) (r • m) =
      (I.subschemeι.app W).hom r * structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ W) m := rfl

theorem epi_toSubscheme {X : Scheme.{0}} (I : X.IdealSheafData) : Epi (toSubscheme I) := by
  rw [epi_iff_forall_affine]
  intro U hU y
  obtain ⟨f, hf⟩ := I.subschemeι_app_surjective ⟨U, hU⟩ ((structureModuleSectionsEquiv _) y)
  refine ⟨(structureModuleSectionsEquiv U).symm f, ?_⟩
  apply (structureModuleSectionsEquiv _).injective
  rw [← hf]
  rfl

theorem exists_twistSec_of_sec {X : Scheme.{0}} (I : X.IdealSheafData) (M : LB X) (σ : (M.pull I.subschemeι).Sec) :
    ∃ b : Γ(twist ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme)) M, ⊤),
    ∀ i, structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i)) (coord b i) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)) := by
  refine ⟨mkSec (fun i => (structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i))).symm
    ((I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)))) ?_,
    fun i => ?_⟩
  · intro i j
    apply (structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j))).injective
    dsimp only
    rw [smul_eq, res_eq, res_eq]
    have hi : ∀ z ∈ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j), z ∈ (M.pull I.subschemeι).U (fun _ => i) :=
      fun z hz => (mem_pull (F := I.subschemeι)).2 hz.1.2
    have hj : ∀ z ∈ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j), z ∈ (M.pull I.subschemeι).U (fun _ => j) :=
      fun z hz => (mem_pull (F := I.subschemeι)).2 hz.2
    refine fn_ext fun z hz => ?_
    have e1 := gs_res (𝟙 I.subscheme) z (fun _ hz => hz.1 : I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j) ≤ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i)) hz
      ((I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)))
    have e1' := gs_res (𝟙 I.subscheme) z (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i)) hz.1 (σ.f (fun _ => i))
    have e2 := gs_res (𝟙 I.subscheme) z (fun _ hz => ⟨hz.1.1, hz.2⟩ : I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j) ≤ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U j)) hz
      ((I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => j)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U j) ≤ (M.pull I.subschemeι).U (fun _ => j))).op).hom (σ.f (fun _ => j)))
    have e2' := gs_res (𝟙 I.subscheme) z (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => j)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U j) ≤ (M.pull I.subschemeι).U (fun _ => j)) ⟨hz.1.1, hz.2⟩ (σ.f (fun _ => j))
    have hz' : I.subschemeι z ∈ M.U i ⊓ M.U j := ⟨hz.1.2, hz.2⟩
    have e3 := gs_pull (𝟙 I.subscheme) I.subschemeι z (⊤ ⊓ M.U i ⊓ M.U j) hz (resG X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (M.g i j : Γ(X, M.U i ⊓ M.U j)))
    have e4 := gs_res (𝟙 I.subscheme ≫ I.subschemeι) z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ⊤ ⊓ M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j) hz (M.g i j : Γ(X, M.U i ⊓ M.U j))
    have e5 := gs_unit (𝟙 I.subscheme ≫ I.subschemeι) z _ hz' (M.g i j)
    have e6 := gs_compat σ (𝟙 _) z (hi z hz) (hj z hz)
    have e7 := gm_pull_g M I.subschemeι (𝟙 _) z (fun _ => i) (fun _ => j) (hi z hz) (hj z hz)
    rw [gs_mul _ z _ hz]
    erw [e1, e1', e2, e2', e3, e4, e5, e6, e7]
  · exact LinearEquiv.apply_symm_apply _ _

theorem secPull_secOfTwist_eq {X : Scheme.{0}} (I : X.IdealSheafData) (M : LB X) (σ : (M.pull I.subschemeι).Sec)
    (b : Γ(twist ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme)) M, ⊤))
    (hb : ∀ i, structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i)) (coord b i) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)))
    (a : Γ(twist (QCoh.structureModule X) M, ⊤)) (ha : (Twist.map M (toSubscheme I)).app ⊤ a = b) :
    GlobalTheory.secPull (Twist.secOfTwist (𝟙 _) a) I.subschemeι = σ := by
  refine DVR.SecOps.sec_ext fun J => ?_
  have h1 := hb (J PUnit.unit)
  rw [← ha, coord_map_app] at h1
  change (I.subschemeι.appLE _ _ _).hom (resG X _ (structureModuleSectionsEquiv _ (coord a (J PUnit.unit)))) = _

  set i := J PUnit.unit
  have hJ : (fun _ : PUnit => i) = J := rfl
  have h2 : (I.subschemeι.app (⊤ ⊓ M.U i)).hom (structureModuleSectionsEquiv _ (coord a i)) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f J) := h1
  have e3 : ∀ y : Γ(X, ⊤ ⊓ M.U i), (I.subschemeι.appLE (M.U i) ((M.pull I.subschemeι).U J)
      (fun z hz => (mem_pull (F := I.subschemeι)).1 hz)).hom (resG X (le_inf le_top le_rfl) y) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => ⟨trivial, (mem_pull (F := I.subschemeι)).1 hz⟩ :
        (M.pull I.subschemeι).U J ≤ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i))).op).hom ((I.subschemeι.app _).hom y) := by
    intro y
    rw [← CommRingCat.comp_apply]
    erw [Scheme.Hom.map_appLE]
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  refine (e3 _).trans ?_
  rw [h2, ← CommRingCat.comp_apply, ← Functor.map_comp]
  exact (congrArg (fun q => (I.subscheme.presheaf.map q).hom (σ.f J)) (Subsingleton.elim _ (𝟙 _))).trans
    (by rw [CategoryTheory.Functor.map_id]; rfl)

theorem exists_secPull_eq_of_subsingleton {X : Scheme.{0}} (I : X.IdealSheafData) (M : LB X) (hM : M.IsLB)
    (h : Subsingleton (coh (twist (idealModule I) M) 1)) (σ : (M.pull I.subschemeι).Sec) :
    ∃ s : M.Sec, GlobalTheory.secPull s I.subschemeι = σ := by
  haveI := epi_toSubscheme I
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (idealModuleι I) (toSubscheme I) (Limits.kernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel _ }
  have hsurj := cohOn.app_surjective (Twist.shortExact_map hM hS) ⊤ h
  obtain ⟨b, hb⟩ := exists_twistSec_of_sec I M σ
  obtain ⟨a, ha⟩ := hsurj b
  exact ⟨_, secPull_secOfTwist_eq I M σ b hb a ha⟩

theorem eventually_exists_secPull_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∀ σ : ((lbPow N l).pull (redι Z)).Sec, ∃ s : (lbPow N l).Sec, GlobalTheory.secPull s (redι Z) = σ := by
  intro X _ _ p hp N Z hN
  letI := algebraΓOfHom p
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  refine (hN.eventually_subsingleton_coh_twist (f := p) (fun _ => rfl)
    (idealModule (Scheme.IdealSheafData.vanishingIdeal Z))).mono fun l hl σ => ?_
  exact exists_secPull_eq_of_subsingleton _ _ (isLB_lbPow hN.isLB l) (hl 1 one_pos) σ

end GlobalTheory.LiftClosed
