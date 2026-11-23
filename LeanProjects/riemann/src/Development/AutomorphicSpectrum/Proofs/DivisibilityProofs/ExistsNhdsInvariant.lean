import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.EdgesRouteSmall
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsSplitPlaceOutsideStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.CompanionTheory.Ar.RT
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo Chars Rep RealMaps FinMaps IsMatched IsTriple IsConst Match PolMatch OneConst Coinv ThetaIntegralsAgree IsRealMaps IsFinMaps RealQuot IsZetaAt At)
open GlobalTheory.WeilM (SB pureA)

namespace GlobalTheory.CompanionTheory.Ar.RT.Move

section Slice

variable {K P : Type} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K] [T2Space K]
  [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P] [T2Space P]

theorem exists_nhds_invariant {g : K → ℂ} (hg : g ∈ SB K) : ∃ V ∈ 𝓝 (0 : K), ∀ x, ∀ u ∈ V, g (x + u) = g x := by
  obtain ⟨hl, hc⟩ := hg
  have hO : IsOpen {p : K × K | g (p.1 + p.2) = g p.1} := by
    have h1 : IsLocallyConstant fun p : K × K => g (p.1 + p.2) - g p.1 :=
      (hl.comp_continuous (continuous_fst.add continuous_snd)).sub (hl.comp_continuous continuous_fst)
    have := h1.isOpen_fiber 0
    simpa [sub_eq_zero, Set.preimage] using this
  have hsub : tsupport g ×ˢ ({0} : Set K) ⊆ {p : K × K | g (p.1 + p.2) = g p.1} := by
    rintro ⟨x, u⟩ ⟨_, hu⟩
    simp only [Set.mem_singleton_iff] at hu
    simp [hu]
  obtain ⟨U, V, hU, hV, hCU, h0V, hUV⟩ := generalized_tube_lemma hc (isCompact_singleton (x := (0 : K))) hO hsub
  have hV0 : V ∈ 𝓝 (0 : K) := hV.mem_nhds (h0V rfl)
  refine ⟨V ∩ Neg.neg ⁻¹' V, inter_mem hV0 (continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hV0)), ?_⟩
  rintro x u ⟨hu, hu'⟩
  by_cases hx : x ∈ tsupport g
  · exact hUV (Set.mk_mem_prod (hCU hx) hu)
  by_cases hxu : x + u ∈ tsupport g
  · have := hUV (Set.mk_mem_prod (hCU hxu) hu')
    simpa using this.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxu]

theorem slice_mem (ε : P →+ K) (π : K →+ P) (hε : Continuous ε) (hπ : Continuous π) (hπε : ∀ y, π (ε y) = y)
    {g : K → ℂ} (hg : g ∈ SB K) (z : K) : (fun y => g (z + ε y)) ∈ SB P := by
  refine ⟨hg.1.comp_continuous (continuous_const.add hε), ?_⟩
  refine HasCompactSupport.intro (K := (fun c => π c - π z) '' tsupport g)
    (hg.2.image (hπ.sub continuous_const)) fun y hy => ?_
  by_contra hne
  exact hy ⟨z + ε y, subset_tsupport _ hne, by simp [hπε]⟩

theorem sb_slice (ε : P →+ K) (π : K →+ P) (hε : Continuous ε) (hπ : Continuous π) (hπε : ∀ y, π (ε y) = y)
    (A : (P → ℂ) →ₗ[ℂ] (P → ℂ)) (hA : ∀ φ ∈ SB P, A φ ∈ SB P) {g : K → ℂ} (hg : g ∈ SB K) :
    (fun x => A (fun y => g (x - ε (π x) + ε y)) (π x)) ∈ SB K := by
  obtain ⟨V, hV, hinv⟩ := exists_nhds_invariant hg
  have hS : ∀ z z', z' - z ∈ V → (fun y => g (z' + ε y)) = fun y => g (z + ε y) := fun z z' h => by
    funext y
    have := hinv (z + ε y) _ h
    rw [← this]
    congr 1
    abel
  have hr : Continuous fun x : K => x - ε (π x) := continuous_id.sub (hε.comp hπ)
  have hrr : ∀ x y, (x - ε (π x) + ε y) - ε (π (x - ε (π x) + ε y)) = x - ε (π x) := fun x y => by
    simp [hπε]
  refine ⟨?_, ?_⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have h1 : ∀ᶠ x' in 𝓝 x, (x' - ε (π x')) - (x - ε (π x)) ∈ V := by
      have hc : Continuous fun x' : K => (x' - ε (π x')) - (x - ε (π x)) := hr.sub continuous_const
      have ht : Tendsto (fun x' : K => (x' - ε (π x')) - (x - ε (π x))) (𝓝 x) (𝓝 0) := by
        have := hc.tendsto x
        simpa only [sub_self] using this
      exact ht hV
    have h2 : ∀ᶠ x' in 𝓝 x, A (fun y => g (x - ε (π x) + ε y)) (π x') = A (fun y => g (x - ε (π x) + ε y)) (π x) :=
      hπ.continuousAt.eventually (((IsLocallyConstant.iff_eventually_eq _).1
        (hA _ (slice_mem ε π hε hπ hπε hg _)).1) (π x))
    filter_upwards [h1, h2] with x' h1' h2'
    rw [hS _ _ h1']
    exact h2'
  · set rC : Set K := (fun x : K => x - ε (π x)) '' tsupport g with hrC
    have hrCc : IsCompact rC := hg.2.image hr
    obtain ⟨Z, hZ, hcov⟩ := hrCc.elim_nhds_subcover (fun z => {w : K | w - z ∈ V}) fun z _ => by
      have hc : Continuous fun w : K => w - z := continuous_id.sub continuous_const
      have ht : Tendsto (fun w : K => w - z) (𝓝 z) (𝓝 0) := by
        have := hc.tendsto z
        simpa only [sub_self] using this
      exact ht hV
    set D : Set P := ⋃ z ∈ Z, tsupport (A fun y => g (z + ε y)) with hD
    have hDc : IsCompact D := Z.isCompact_biUnion fun z _ => (hA _ (slice_mem ε π hε hπ hπε hg z)).2
    refine HasCompactSupport.intro (K := (fun p : K × P => p.1 + ε p.2) '' (rC ×ˢ D))
      ((hrCc.prod hDc).image (continuous_fst.add (hε.comp continuous_snd))) fun x hx => ?_
    by_contra hne
    apply hx
    have hne' : (fun y => g (x - ε (π x) + ε y)) ≠ 0 := fun h0 => hne (by simp [h0])
    obtain ⟨y, hy⟩ := Function.ne_iff.1 hne'
    have hmem : x - ε (π x) ∈ rC := ⟨_, subset_tsupport _ hy, hrr x y⟩
    obtain ⟨z, hz, hzV⟩ := Set.mem_iUnion₂.1 (hcov hmem)
    have hs := hS z _ hzV
    refine ⟨(x - ε (π x), π x), ⟨hmem, Set.mem_iUnion₂.2 ⟨z, hz, ?_⟩⟩, by simp⟩
    rw [hs] at hne
    exact subset_tsupport _ hne

end Slice

section Op

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def epsK (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : (κ → Fv F v) →+ (κ → Af F) where
  toFun y i := GlobalTheory.AdelicU.singleFin v (y i)
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp

def piK (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : (κ → Af F) →+ (κ → Fv F v) where
  toFun x i := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (x i)
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp

theorem continuous_epsK (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Continuous (epsK (κ := κ) v) :=
  continuous_pi fun i => (GlobalTheory.AdelicU.continuous_singleFin v).comp (continuous_apply i)

theorem continuous_piK (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Continuous (piK (κ := κ) v) :=
  continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)

theorem piK_epsK (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (y : κ → Fv F v) : piK v (epsK v y) = y := by
  funext i
  exact GlobalTheory.AdelicU.evalV_singleFin_self v (y i)

def finPart (x : κ → AF F) : κ → Af F := fun i => (x i).2

def repl (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (x : κ → AF F) (y : κ → Fv F v) : κ → AF F :=
  fun i => ((x i).1, (finPart x - epsK v (piK v (finPart x)) + epsK v y) i)

def opF (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (A : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) (g : (κ → Af F) → ℂ) : (κ → Af F) → ℂ :=
  fun x => A (fun y => g (x - epsK v (piK v x) + epsK v y)) (piK v x)

def opL (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (A : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) :
    ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun Ψ := fun x => A (fun y => Ψ (repl v x y)) (piK v (finPart x))
  map_add' Ψ Ψ' := by
    funext x
    change A ((fun y => Ψ (repl v x y)) + fun y => Ψ' (repl v x y)) _ = _
    rw [map_add]
    rfl
  map_smul' c Ψ := by
    funext x
    change A (c • fun y => Ψ (repl v x y)) _ = _
    rw [map_smul]
    rfl

theorem opF_mem (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (A : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ))
    (hA : ∀ φ ∈ SB (κ → Fv F v), A φ ∈ SB (κ → Fv F v)) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    opF v A g ∈ SB (κ → Af F) :=
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  sb_slice (epsK v) (piK v) (continuous_epsK v) (continuous_piK v) (piK_epsK v) A hA hg

theorem opL_pureA (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (A : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) :
    opL v A (pureA F f g) = pureA F f (opF v A g) := by
  funext x
  have : (fun y => pureA F f g (repl v x y)) =
      (f fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) •
        fun y => g (finPart x - epsK v (piK v (finPart x)) + epsK v y) := rfl
  change A (fun y => pureA F f g (repl v x y)) (piK v (finPart x)) = _
  rw [this, map_smul]
  rfl

end Op

section Pure

attribute [local instance] Classical.propDecidable

local notation "pureT" => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure

open GlobalTheory.AdelicU (evFin)

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
  {vac : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ}

theorem finite_mulSupport
    (hv : ∀ᶠ w in cofinite, vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    {φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ} (hφ : ∀ᶠ w in cofinite, φ w = vac w) (x : κ → AF F) :
    (Function.mulSupport fun w => φ w fun i => evFin F w (x i)).Finite := by
  have hint : ∀ᶠ w in cofinite, ∀ i, evFin F w (x i) ∈ (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F).adicCompletionIntegers F :=
    eventually_all.2 fun i => (x i).2.2
  have h : ∀ᶠ w in cofinite, (φ w fun i => evFin F w (x i)) = 1 := by
    filter_upwards [hv, hφ, hint] with w h1 h2 h3
    rw [h2, h1]
    exact Set.indicator_of_mem (show (fun i => evFin F w (x i)) ∈ {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from h3) 1
  exact Filter.eventually_cofinite.1 h

theorem pure_update
    (hv : ∀ᶠ w in cofinite, vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    {φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ} (hφ : ∀ᶠ w in cofinite, φ w = vac w)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (ψ : (κ → Fv F v) → ℂ) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (x : κ → AF F) :
    pureT f (Function.update φ v ψ) x =
      ψ (fun i => evFin F v (x i)) * pureT f (Function.update φ v 1) x := by
  classical
  have hφ1 : ∀ᶠ w in cofinite, Function.update φ v 1 w = vac w := by
    filter_upwards [hφ, Filter.eventually_cofinite_ne v] with w h1 h2
    rw [Function.update_of_ne h2, h1]
  have h1 := finite_mulSupport hv hφ1 x
  set t : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F → ℂ := fun w => if w = v then ψ (fun i => evFin F v (x i)) else 1 with ht
  have hts : (Function.mulSupport t).Finite := (Set.finite_singleton v).subset fun w hw => by
    by_contra h
    exact hw (if_neg h)
  have key : (fun w => Function.update φ v ψ w fun i => evFin F w (x i)) =
      fun w => t w * Function.update φ v 1 w fun i => evFin F w (x i) := by
    funext w
    by_cases h : w = v
    · subst h
      simp [ht]
    · simp [ht, h, Function.update_of_ne h]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [key, finprod_mul_distrib hts h1, finprod_eq_single t v fun w hw => if_neg hw]
  simp only [ht, if_true]
  ring

theorem piK_repl (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (x : κ → AF F) (y : κ → Fv F v) :
    (fun i => evFin F v (repl v x y i)) = y := by
  change piK v (finPart x - epsK v (piK v (finPart x)) + epsK v y) = y
  simp [piK_epsK]

theorem pure_repl
    {φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ}
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (x : κ → AF F) (y : κ → Fv F v) :
    pureT f (Function.update φ v 1) (repl v x y) = pureT f (Function.update φ v 1) x := by
  classical
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  congr 1
  refine finprod_congr fun w => ?_
  by_cases h : w = v
  · subst h
    simp
  · rw [Function.update_of_ne h]
    congr 1
    funext i
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w ((x i).2 - GlobalTheory.AdelicU.singleFin v _ + GlobalTheory.AdelicU.singleFin v _) = _
    rw [map_add, map_sub, GlobalTheory.AdelicU.evalV_singleFin_ne h, GlobalTheory.AdelicU.evalV_singleFin_ne h]
    simp
    rfl

theorem opL_pure
    (hv : ∀ᶠ w in cofinite, vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    {φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ} (hφ : ∀ᶠ w in cofinite, φ w = vac w)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (A : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) :
    opL v A (pureT f φ) = pureT f (Function.update φ v (A (φ v))) := by
  classical
  funext x
  have hs : (fun y => pureT f φ (repl v x y)) = pureT f (Function.update φ v 1) x • φ v := by
    funext y
    have h := pure_update hv hφ v (φ v) f (repl v x y)
    rw [Function.update_eq_self, piK_repl, pure_repl] at h
    rw [h]
    simp [mul_comm]
  change A (fun y => pureT f φ (repl v x y)) (piK v (finPart x)) = _
  rw [hs, map_smul, pure_update hv hφ v (A (φ v)) f x]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_comm]
  rfl

theorem pure_update_mem
    (hv : ∀ᶠ w in cofinite, vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    {φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ} (hφ : ∀ᶠ w in cofinite, φ w = vac w)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (L : Submodule ℂ ((κ → AF F) → ℂ))
    {S : Set ((κ → Fv F v) → ℂ)} (hS : ∀ ψ ∈ S, pureT f (Function.update φ v ψ) ∈ L) {ψ : (κ → Fv F v) → ℂ}
    (hψ : ψ ∈ Submodule.span ℂ S) : pureT f (Function.update φ v ψ) ∈ L := by
  have e : ∀ ψ, pureT f (Function.update φ v ψ) =
      fun x => ψ (fun i => evFin F v (x i)) * pureT f (Function.update φ v 1) x :=
    fun ψ => funext (pure_update hv hφ v ψ f)
  induction hψ using Submodule.span_induction with
  | mem ψ h => exact hS ψ h
  | zero =>
    rw [e]
    convert L.zero_mem using 1
    funext x
    simp
  | add a b _ _ ha hb =>
    rw [e] at ha hb ⊢
    convert L.add_mem ha hb using 1
    funext x
    simp [add_mul]
  | smul c a _ ha =>
    rw [e] at ha ⊢
    convert L.smul_mem c ha using 1
    funext x
    simp [mul_assoc]

end Pure

section Tensor

open scoped TensorProduct

theorem tensor_insert {ι Q : Type} [DecidableEq ι] {Mo : ι → Type} [∀ i, AddCommGroup (Mo i)] [∀ i, Module ℂ (Mo i)]
    [AddCommGroup Q] [Module ℂ Q] (T : Finset ι) (v : ι) (ξ : Mo v) {m m' : ℕ}
    (a : Fin m → Q) (b : Fin m → ∀ i, Mo i) (a' : Fin m' → Q) (b' : Fin m' → ∀ i, Mo i)
    (hb : v ∉ T → ∀ i, b i v = ξ) (hb' : v ∉ T → ∀ j, b' j v = ξ)
    (h : ∑ i, a i ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun w : T => b i w) =
      ∑ j, a' j ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun w : T => b' j w)) :
    ∑ i, a i ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun w : (insert v T : Finset ι) => b i w) =
      ∑ j, a' j ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun w : (insert v T : Finset ι) => b' j w) := by
  by_cases hvT : v ∈ T
  · rw [Finset.insert_eq_of_mem hvT]
    exact h
  let ex : ∀ w, Mo w := Function.update 0 v ξ
  let e : (∀ w : T, Mo w) → ∀ w : (insert v T : Finset ι), Mo w :=
    fun m w => if hw : w.1 ∈ T then m ⟨w.1, hw⟩ else ex w.1
  have hup : ∀ (m : ∀ w : T, Mo w) (i : T) (x : Mo i), e (Function.update m i x) =
      Function.update (e m) ⟨i.1, Finset.mem_insert_of_mem i.2⟩ x := by
    intro m i x
    funext w
    by_cases hw : w = ⟨i.1, Finset.mem_insert_of_mem i.2⟩
    · subst hw
      simp [e]
    · rw [Function.update_of_ne hw]
      have hne : ∀ hw' : w.1 ∈ T, (⟨w.1, hw'⟩ : T) ≠ i := fun hw' h' => hw (Subtype.ext (show w.1 = i.1 from congrArg Subtype.val h'))
      simp only [e]
      split_ifs with hw'
      · rw [Function.update_of_ne (hne hw')]
      · rfl
  let M : MultilinearMap ℂ (fun w : T => Mo w) (PiTensorProduct ℂ fun w : (insert v T : Finset ι) => Mo w) :=
    MultilinearMap.mk' (fun m => PiTensorProduct.tprod ℂ (e m))
      (fun m i x y => by
        simp only [hup, MultilinearMap.map_update_add])
      (fun m i c x => by
        simp only [hup, MultilinearMap.map_update_smul])
  have hM : ∀ c : ∀ i, Mo i, c v = ξ → M (fun w : T => c w) =
      PiTensorProduct.tprod ℂ fun w : (insert v T : Finset ι) => c w := by
    intro c hc
    have hMe : M (fun w : T => c w) = PiTensorProduct.tprod ℂ (e fun w : T => c w) := rfl
    rw [hMe]
    congr 1
    funext w
    rcases w with ⟨w, hw⟩
    by_cases hwT : w ∈ T
    · simp [e, hwT]
    · obtain rfl : w = v := (Finset.mem_insert.1 hw).resolve_right hwT
      simp [e, hwT, ex, hc]
  have := congrArg (LinearMap.lTensor Q (PiTensorProduct.lift M)) h
  simpa only [map_sum, LinearMap.lTensor_tmul, PiTensorProduct.lift.tprod, hM _ (hb hvT _), hM _ (hb' hvT _)] using this

end Tensor

section Main

attribute [local instance] Classical.propDecidable

local notation "pureT" => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_section {V P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P] (p : V →ₗ[ℂ] P) (S : Set V)
    (hs : ∀ ξ, ∃ φ ∈ S, p φ = ξ) : ∃ A : V →ₗ[ℂ] V, (∀ φ, p (A φ) = p φ) ∧ ∀ φ, A φ ∈ Submodule.span ℂ S := by
  choose sec hsec hp using hs
  let b := Module.Basis.ofVectorSpace ℂ P
  let s : P →ₗ[ℂ] V := b.constr ℂ fun i => sec (b i)
  have hps : p ∘ₗ s = LinearMap.id := b.ext fun i => by simp [s, hp]
  refine ⟨s ∘ₗ p, fun φ => LinearMap.congr_fun hps (p φ), fun φ => ?_⟩
  have : LinearMap.range s ≤ Submodule.span ℂ S := by
    rw [Module.Basis.constr_range]
    exact Submodule.span_mono (Set.range_subset_iff.2 fun i => hsec _)
  exact this ⟨p φ, rfl⟩

theorem soLoc_sub {n d : ℕ} {Y : Spc F E n} {Z : Spc F E d} (M : Model σ Y Z) (ψ : AddChar (AF F) ℂ)
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) :
    Submodule.span ℂ (M.SoLoc ψ t) ≤ SB (Fin n × Fin d → Fv F v) :=
  Submodule.span_le.2 fun _ h => h.1

theorem opL_so {n d : ℕ} {Y : Spc F E n} {Z : Spc F E d} (M : Model σ Y Z) (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ)
    {v₁ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t₁ : E →ₐ[F] Fv F v₁) (t : E →ₐ[F] Fv F v) (hne : v ≠ v₁)
    (A : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ))
    (hA : ∀ φ, A φ ∈ Submodule.span ℂ (M.SoLoc ψ t)) {Ψ : (Fin n × Fin d → AF F) → ℂ} (hΨ : Ψ ∈ M.So ψ t₁) :
    opL v A Ψ ∈ M.So ψ t₁ ∧ opL v A Ψ ∈ M.So ψ t := by
  have hle : M.So ψ t₁ ≤ (M.So ψ t₁ ⊓ M.So ψ t).comap (opL v A) := by
    refine Submodule.span_le.2 ?_
    rintro Φ ⟨f, φ, h1, h2, h3, rfl⟩
    have hU : ∀ ψ' ∈ SB (Fin n × Fin d → Fv F v), ∀ w, Function.update φ v ψ' w ∈ SB _ := fun ψ' h' w => by
      by_cases h : w = v
      · subst h
        simpa using h'
      · rw [Function.update_of_ne h]
        exact h1 w
    have hC : ∀ ψ', ∀ᶠ w in cofinite, Function.update φ v ψ' w = M.vac w := fun ψ' => by
      filter_upwards [h2, Filter.eventually_cofinite_ne v] with w h h'
      rw [Function.update_of_ne h', h]
    rw [SetLike.mem_coe, Submodule.mem_comap, opL_pure hM.std h2]
    refine Submodule.mem_inf.2 ⟨Submodule.subset_span ?_, ?_⟩
    · refine ⟨f, _, hU _ (soLoc_sub M ψ t (hA _)), hC _, ?_, rfl⟩
      rw [Function.update_of_ne hne.symm]
      exact h3
    · refine pure_update_mem hM.std h2 v f _ (S := M.SoLoc ψ t) (fun ψ' h' => Submodule.subset_span ?_) (hA _)
      exact ⟨f, _, hU _ h'.1, hC _, by simpa using h', rfl⟩
  exact hle hΨ

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem polMatch_move (hM' : G.M'.IsGood B.ψ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F}
    (hsph : Rf.p v (G.M.vac v) = Rf.p' v (G.M'.vac v))
    (A : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ))
    (hSB : ∀ φ, A φ ∈ SB (Fin a' × Fin (a + a') → Fv F v)) (hp : ∀ φ, Rf.p' v (A φ) = Rf.p' v φ)
    {Φ : (Fin a × Fin (a + a') → AF F) → ℂ} {Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ} (h : PolMatch B G X R Rf Φ Ψ) :
    PolMatch B G X R Rf Φ (opL v A Ψ) := by
  obtain ⟨T, hT, m, m', f, φ, f', φ', h1, h2, rfl, rfl, he⟩ := h
  have hc : ∀ j, ∀ᶠ w in cofinite, φ' j w = G.M'.vac w := fun j => by
    filter_upwards [T.finite_toSet.compl_mem_cofinite] with w hw using (h2 j).2.2 w hw
  have hpu : ∀ j (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F),
      Rf.p' w (Function.update (φ' j) v (A (φ' j v)) w) = Rf.p' w (φ' j w) := fun j w => by
    by_cases h : w = v
    · subst h
      simpa using hp _
    · rw [Function.update_of_ne h]
  refine ⟨insert v T, hT.trans (Finset.subset_insert _ _), m, m', f, φ, f',
    fun j => Function.update (φ' j) v (A (φ' j v)),
    fun i => ⟨(h1 i).1, (h1 i).2.1, fun w hw => (h1 i).2.2 w fun h => hw (Finset.mem_insert_of_mem h)⟩,
    fun j => ⟨(h2 j).1, fun w => ?_, fun w hw => ?_⟩, rfl, ?_, ?_⟩
  · change Function.update (φ' j) v (A (φ' j v)) w ∈ _
    by_cases h : w = v
    · subst h
      simpa using hSB _
    · rw [Function.update_of_ne h]
      exact (h2 j).2.1 w
  · have h : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self _ _)
    change Function.update (φ' j) v (A (φ' j v)) w = _
    rw [Function.update_of_ne h]
    exact (h2 j).2.2 w fun h' => hw (Finset.mem_insert_of_mem h')
  · rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => opL_pure hM'.std (hc j) v A (f' j)
  · simp only [hpu]
    exact tensor_insert T v (Rf.p v (G.M.vac v)) _ (fun i w => Rf.p w (φ i w)) _ (fun j w => Rf.p' w (φ' j w))
      (fun hv i => by simp only [(h1 i).2.2 v hv]) (fun hv j => by simp only [(h2 j).2.2 v hv, hsph]) he

abbrev mv (B : Base F E) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (τ : E →ₐ[F] Fv F v) : Base F E := { B with v₁ := v, τ₁ := τ }

theorem match_move (hM' : G.M'.IsGood B.ψ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (hne : v ≠ B.v₁)
    (hsph : Rf.p v (G.M.vac v) = Rf.p' v (G.M'.vac v))
    (A : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ))
    (hA : ∀ φ, A φ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ τ)) (hp : ∀ φ, Rf.p' v (A φ) = Rf.p' v φ)
    {Φ : (Fin a × Fin (a + a') → AF F) → ℂ} {Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ} (h : Match B G X R Rf Φ Ψ) :
    Match B G X R Rf Φ (opL v A Ψ) ∧ Match (mv B v τ) G X R Rf Φ (opL v A Ψ) := by
  have hSB : ∀ φ, A φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) := fun φ => soLoc_sub G.M' B.ψ τ (hA φ)
  obtain ⟨hΨ, m, m', g, f, s, g', f', s', hc, hc', rfl, rfl, hk⟩ := h
  have hg : ∀ j, opF v A (g' j) ∈ SB _ := fun j => opF_mem v A (fun φ _ => hSB φ) (hc' j).1
  have he : ∀ u : Fin m' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
      opL v A (∑ j, pureA F (u j) (g' j)) = ∑ j, pureA F (u j) (opF v A (g' j)) := fun u => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => opL_pureA v A _ _
  have hso := opL_so G.M' B.ψ hM' B.τ₁ τ hne A hA hΨ
  have hk' := fun k => opL_so G.M' B.ψ hM' B.τ₁ τ hne A hA (hk k).1
  have hpm := fun k => polMatch_move (G := G) (X := X) (R := R) (Rf := Rf) hM' hsph A hSB hp (hk k).2
  refine ⟨⟨hso.1, m, m', g, f, s, fun j => opF v A (g' j), f', s', hc, fun j => ⟨hg j, (hc' j).2⟩, rfl, he f', fun k => ?_⟩,
    ⟨hso.2, m, m', g, f, s, fun j => opF v A (g' j), f', s', hc, fun j => ⟨hg j, (hc' j).2⟩, rfl, he f', fun k => ?_⟩⟩
  · rw [← he]
    exact ⟨(hk' k).1, hpm k⟩
  · rw [← he]
    exact ⟨(hk' k).2, hpm k⟩

theorem const_eq (hM : IsMatched B G X om om' R Rf) (one : OneConst B G X om om' R Rf) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F}
    (τ : E →ₐ[F] Fv F v) (hne : v ≠ B.v₁) (hvT : v ∉ X.T) (hs : ∀ ξ, ∃ φ ∈ G.M'.SoLoc B.ψ τ, Rf.p' v φ = ξ) {c c' : ℂ}
    (hc : IsConst B G X om om' R Rf c) (hc' : IsConst (mv B v τ) G X om om' R Rf c') : c = c' := by
  obtain ⟨A, hp, hA⟩ := exists_section (Rf.p' v) _ hs
  have hnz : ∃ Φ Ψ h, Match B G X R Rf Φ Ψ ∧ G.M'.I om' Ψ h ≠ 0 := by
    by_contra hcon
    have hz : ∀ Φ Ψ h, Match B G X R Rf Φ Ψ → G.M'.I om' Ψ h = 0 :=
      fun Φ Ψ h hm => by_contra fun hn => hcon ⟨Φ, Ψ, h, hm, hn⟩
    obtain ⟨c₀, _, hu⟩ := one.2.1
    have hc1 : IsConst B G X om om' R Rf (c + 1) := fun Φ Ψ hm h => by
      rw [hc Φ Ψ hm h, hz Φ Ψ h hm, mul_zero, mul_zero]
    have := (hu _ hc1).trans (hu _ hc).symm
    simp at this
  obtain ⟨Φ, Ψ, h, hm, hI⟩ := hnz
  obtain ⟨m1, m2⟩ := match_move hM.triple.geo.hM' τ hne (hM.fin.sph v hvT).1 A hA hp hm
  have e1 := hc Φ Ψ hm h
  have e2 := hc _ _ m1 h
  have e3 := hc' _ _ m2 h
  have hI' : G.M'.I om' (opL v A Ψ) h ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at e2
    rw [e2] at e1
    exact mul_ne_zero (one.2.2 c hc) hI e1.symm
  exact mul_right_cancel₀ hI' (e2.symm.trans e3)

theorem matched_move (hM : IsMatched B G X om om' R Rf) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (hv : X.Good v) :
    IsMatched (mv B v τ) G X om om' R Rf := by
  obtain ⟨⟨hb, hg, hc, hw, hw'⟩, hr, hf⟩ := hM
  have hV := hg.hV
  have hV' := hg.hV'
  have hW := hg.hW
  have q := hr.quot
  have q' := hr.quot'
  exact ⟨⟨⟨hb.cm, hb.galois, hb.unram, hb.std, hb.inert, hb.psiP⟩,
    ⟨hg.lt, hg.even, hg.kappa, hg.eBig, hg.aBig,
      ⟨hV.herm, hV.sig, hV.lat, hV.dual, hV.cartan, hV.bas⟩,
      ⟨hV'.herm, hV'.sig, hV'.lat, hV'.dual, hV'.cartan, hV'.bas⟩,
      ⟨hW.skew, hW.sig, hW.lat, hW.dual, hW.cartan, hW.bas⟩, hg.hM, hg.hM'⟩,
    ⟨hc.heckeα, hc.heckeβ, hc.resα, hc.resβ, hc.expα, hc.expβ, hc.disj, hc.sub, hc.ram, hc.unrα, hc.unrβ, hv⟩, hw, hw'⟩,
    ⟨⟨q.onto, q.lie, q.cpt⟩, ⟨q'.onto, q'.lie, q'.cpt⟩, hr.lie, hr.cpt, hr.nontriv, hr.irred⟩,
    ⟨hf.onto, hf.onto', hf.inv, hf.inv', hf.equiv, hf.nontriv, hf.irred, hf.sph, hf.zeta⟩⟩

theorem const_step (hT : ThetaIntegralsAgree) (hM : IsMatched B G X om om' R Rf) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F}
    (τ : E →ₐ[F] Fv F v) (hv : X.Good v) (hne : v ≠ B.v₁) {c : ℂ} (hc : IsConst B G X om om' R Rf c) :
    IsConst (mv B v τ) G X om om' R Rf c := by
  have hM₂ := matched_move hM τ hv
  obtain ⟨one, -⟩ := (hT.1 F E σ B a a' G X om om' hM.triple).2 R Rf hM
  obtain ⟨one₂, co₂⟩ := (hT.1 F E σ (mv B v τ) a a' G X om om' hM₂.triple).2 R Rf hM₂
  obtain ⟨c₂, hc₂, -⟩ := one₂.2.1
  have := const_eq hM one τ hne hv.1 ((co₂.1 v hv).2.2.1 τ) hc hc₂
  rwa [this]

end Main

theorem const_good_place : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B Γ X om om' R Rf → ∀ v (τ : E →ₐ[F] Fv F v), X.Good v → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched { B with v₁ := v, τ₁ := τ } Γ X om om' R Rf ∧ ∀ c, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst B Γ X om om' R Rf c → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst { B with v₁ := v, τ₁ := τ } Γ X om om' R Rf c := by
  intro hT F E _ _ _ _ _ σ B a a' Γ X om om' R Rf hM v τ hv
  refine ⟨matched_move hM τ hv, fun c hc => ?_⟩
  haveI : IsGalois ℚ E := hM.triple.base.galois
  classical
  obtain ⟨v₂, hS, hsp, ⟨τ₂⟩⟩ := GlobalTheory.T.exists_split_place_outside F E (insert v (insert B.v₁ X.T))
  have hv₂v : v₂ ≠ v := fun h => hS (h ▸ Finset.mem_insert_self _ _)
  have hv₂₁ : v₂ ≠ B.v₁ := fun h => hS (h ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hg₂ : X.Good v₂ := ⟨fun h => hS (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)), hsp⟩
  have hM₂ := matched_move hM τ₂ hg₂
  have hc₂ := const_step hT hM τ₂ hg₂ hv₂₁ hc
  exact const_step hT hM₂ τ hv hv₂v.symm hc₂

end GlobalTheory.CompanionTheory.Ar.RT.Move

end
