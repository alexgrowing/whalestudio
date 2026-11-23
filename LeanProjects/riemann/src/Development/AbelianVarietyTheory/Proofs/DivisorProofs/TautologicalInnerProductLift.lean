import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self toMod coord ofSec mkSec sec_ext)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.VB GlobalTheory.ProjSpace GlobalTheory.QCoh
open GlobalTheory.CxPts GlobalTheory.HermFrame
open scoped ZeroObject ComplexOrder

namespace GlobalTheory.TautFlag

def flagOfShortExact {X : Scheme.{0}} (S : ShortComplex X.Modules) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1)
    (h₂ : IsVB S.X₂ 2) (h₃ : IsVB S.X₃ 1) : Vert.Flag S.X₂ 2 :=
  have := hS.mono_f
  { F := ![0, S.X₁, S.X₂]
    ι := Fin.cons 0 (Fin.cons S.f (Fin.cons (𝟙 _) finZeroElim))
    isSubbundle := Fin.cons ⟨(isZero_zero _).mono _, 2, h₂.of_iso cokernelZeroIsoTarget.symm⟩
      (Fin.cons (isSubbundle_of_shortExact hS h₃) (Fin.cons (isSubbundle_of_isIso (𝟙 _)) finZeroElim))
    isVB := Fin.cons (isVB_zero_iff.2 (isZero_zero _)) (Fin.cons h₁ (Fin.cons h₂ finZeroElim))
    step := Fin.cons 0 (Fin.cons S.f finZeroElim)
    step_ι := Fin.cons zero_comp (Fin.cons (Category.comp_id _) finZeroElim)
    isIso_last := IsIso.id _ }

abbrev Q : (PSpace ℤ 1).Modules := toMod (O1 ℤ 1)

abbrev E : (PSpace ℤ 1).Modules := freeModule (PSpace ℤ 1) (Fin 2)

def X' (j : Fin 2) : Γ(Q, ⊤) := ofSec (ProjSpace.coord ℤ 1 j) ⊤

def sec : Fin 2 → Γ(Q, ⊤) := ![-X' 1, X' 0]

def quotMap : E ⟶ Q := sectionsHom sec

theorem resM_X' (j : Fin 2) : resM Q (le_top : chart ℤ 1 j ≤ ⊤) (X' j) = LB.chartSec (O1_isLB ℤ 1) j :=
  sec_ext fun i => by
    rfl

theorem chartSec_mem_span (j : Fin 2) : resM Q (le_refl (chart ℤ 1 j)) (LB.chartSec (O1_isLB ℤ 1) j) ∈
    Submodule.span Γ(PSpace ℤ 1, chart ℤ 1 j)
      (Set.range fun i => resM Q (le_top : chart ℤ 1 j ≤ ⊤) (sec i)) := by
  have e : resM Q (le_refl (chart ℤ 1 j)) (LB.chartSec (O1_isLB ℤ 1) j) =
      resM Q (le_top : chart ℤ 1 j ≤ ⊤) (X' j) := (resM_self _ _).trans (resM_X' j).symm
  rw [e]
  fin_cases j
  · exact Submodule.subset_span ⟨1, rfl⟩
  · have h : resM Q (le_top : chart ℤ 1 1 ≤ ⊤) (sec 0) ∈ Submodule.span Γ(PSpace ℤ 1, chart ℤ 1 1)
      (Set.range fun i => resM Q (le_top : chart ℤ 1 1 ≤ ⊤) (sec i)) := Submodule.subset_span ⟨0, rfl⟩
    have e : resM Q (le_top : chart ℤ 1 1 ≤ ⊤) (X' 1) = -resM Q (le_top : chart ℤ 1 1 ≤ ⊤) (sec 0) := by
      rw [← map_neg]
      exact congrArg _ (neg_neg _).symm
    change resM Q (le_top : chart ℤ 1 1 ≤ ⊤) (X' 1) ∈ Submodule.span Γ(PSpace ℤ 1, chart ℤ 1 1)
      (Set.range fun i => resM Q (le_top : chart ℤ 1 1 ≤ ⊤) (sec i))
    rw [e]
    exact Submodule.neg_mem _ h

instance epi_quotMap : Epi quotMap := by
  have := LB.isQuasicoherent_toMod (O1_isLB ℤ 1)
  refine (epi_sectionsHom_iff sec).2 (spanStalks_of_forall_exists_affine sec fun x => ?_)
  obtain ⟨j, hj⟩ := exists_mem_chart ℤ 1 x
  refine ⟨_, isAffineOpen_chart ℤ 1 j, hj, top_le_iff.1 fun q _ => ?_⟩
  have e := (LB.chartEquiv (O1_isLB ℤ 1) j (le_refl (chart ℤ 1 j))).symm_apply_apply q
  have e₂ : q = _ • resM Q (le_refl (chart ℤ 1 j)) (LB.chartSec (O1_isLB ℤ 1) j) :=
    e.symm.trans (LB.chartEquiv_symm_apply (O1_isLB ℤ 1) j (le_refl (chart ℤ 1 j)) _)
  refine e₂ ▸ Submodule.smul_mem _ _ ?_
  exact chartSec_mem_span j

abbrev K : (PSpace ℤ 1).Modules := kernel quotMap

abbrev seq : ShortComplex (PSpace ℤ 1).Modules := .mk (kernel.ι quotMap) quotMap (kernel.condition _)

theorem seq_shortExact : seq.ShortExact :=
  have : Mono seq.f := equalizer.ι_mono
  have : Epi seq.g := inferInstanceAs (Epi quotMap)
  { exact := ShortComplex.exact_kernel _ }

theorem isVB_seq₁ : IsVB seq.X₁ 1 :=
  isVB_X₁_of_shortExact _ seq 1 1 seq_shortExact (isVB_freeModule_fin _ 2) (isVB_toMod (O1_isLB ℤ 1))

def flag : Vert.Flag (HermVB.std (PSpace.str ℤ 1) 2).E 2 :=
  flagOfShortExact seq seq_shortExact isVB_seq₁ (isVB_freeModule_fin _ 2) (isVB_toMod (O1_isLB ℤ 1))

abbrev e (a : Fin 2) : Γ(E, ⊤) := freeFrame _ (Fin 2) a

abbrev eV (V : (PSpace ℤ 1).Opens) (a : Fin 2) : Γ(E, V) := resM E le_top (e a)

theorem quotMap_eV (V : (PSpace ℤ 1).Opens) (a : Fin 2) :
    quotMap.app V (eV V a) = resM Q le_top (sec a) := by
  rw [app_resM]
  exact congrArg _ (sectionsHom_app_freeBasis sec a)

theorem resM_X'_eq (j a : Fin 2) {V : (PSpace ℤ 1).Opens} (h : V ≤ chart ℤ 1 j) :
    resM Q le_top (X' a) = ratioOn V j h a • resM Q h (LB.chartSec (O1_isLB ℤ 1) j) :=
  ((LB.chartEquiv (O1_isLB ℤ 1) j h).symm_apply_apply _).symm

theorem eq_zero_of_smul_chartSec (j : Fin 2) {V : (PSpace ℤ 1).Opens} (h : V ≤ chart ℤ 1 j) (c : Γ(PSpace ℤ 1, V))
    (hc : c • resM Q h (LB.chartSec (O1_isLB ℤ 1) j) = 0) : c = 0 := by
  have := (LB.chartEquiv (O1_isLB ℤ 1) j h).symm.injective (a₁ := c) (a₂ := 0) (hc.trans (map_zero _).symm)
  exact this

def v (j : Fin 2) : Γ(E, chart ℤ 1 j) := ratio ℤ 1 j 0 • eV _ 0 + ratio ℤ 1 j 1 • eV _ 1

theorem exists_comb {V : (PSpace ℤ 1).Opens} (t : Γ(E, V)) : ∃ c₀ c₁ : Γ(PSpace ℤ 1, V), t = c₀ • eV V 0 + c₁ • eV V 1 := by
  have h := ((isFrame_freeFrame (PSpace ℤ 1) (Fin 2)).basis (le_top : V ≤ ⊤)).sum_repr t
  rw [Fin.sum_univ_two, IsFrame.basis_apply, IsFrame.basis_apply] at h
  exact ⟨_, _, h.symm⟩

theorem comb_injective {V : (PSpace ℤ 1).Opens} {c₀ c₁ d₀ d₁ : Γ(PSpace ℤ 1, V)}
    (h : c₀ • eV V 0 + c₁ • eV V 1 = d₀ • eV V 0 + d₁ • eV V 1) : c₀ = d₀ ∧ c₁ = d₁ := by
  have hi := ((isFrame_freeFrame (PSpace ℤ 1) (Fin 2)) V le_top).1
  have := @hi ![c₀, c₁] ![d₀, d₁] (by
    simpa [Fintype.linearCombination_apply, Fin.sum_univ_two] using h)
  exact ⟨congrFun this 0, congrFun this 1⟩

theorem quotMap_comb (j : Fin 2) {V : (PSpace ℤ 1).Opens} (h : V ≤ chart ℤ 1 j) (c₀ c₁ : Γ(PSpace ℤ 1, V)) :
    quotMap.app V (c₀ • eV V 0 + c₁ • eV V 1) =
      (c₁ * ratioOn V j h 0 - c₀ * ratioOn V j h 1) • resM Q h (LB.chartSec (O1_isLB ℤ 1) j) := by
  have e₀ : quotMap.app V (eV V 0) = -(ratioOn V j h 1 • resM Q h (LB.chartSec (O1_isLB ℤ 1) j)) := by
    rw [quotMap_eV, ← resM_X'_eq j 1 h, ← map_neg]
    rfl
  have e₁ : quotMap.app V (eV V 1) = ratioOn V j h 0 • resM Q h (LB.chartSec (O1_isLB ℤ 1) j) := by
    rw [quotMap_eV, ← resM_X'_eq j 0 h]
    rfl
  rw [map_add, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, e₀, e₁, sub_smul, mul_smul, mul_smul,
    smul_neg, sub_eq_add_neg, add_comm]

theorem quotMap_v (j : Fin 2) : quotMap.app _ (v j) = 0 := by
  rw [v, quotMap_comb j le_rfl]
  rw [mul_comm, sub_self, zero_smul]

def s (j : Fin 2) : Γ(K, chart ℤ 1 j) := ((exact_kernel_ι_app quotMap _ (v j)).1 (quotMap_v j)).choose

theorem map_s (j : Fin 2) : (kernel.ι quotMap).app _ (s j) = v j :=
  ((exact_kernel_ι_app quotMap _ (v j)).1 (quotMap_v j)).choose_spec

theorem resM_v (j : Fin 2) {V : (PSpace ℤ 1).Opens} (h : V ≤ chart ℤ 1 j) :
    resM E h (v j) = ratioOn V j h 0 • eV V 0 + ratioOn V j h 1 • eV V 1 := by
  rw [v, map_add, resM_smul, resM_smul, resM_resM, resM_resM]
  rfl

theorem kernel_ι_app_smul_resM_s (j : Fin 2) {V : (PSpace ℤ 1).Opens} (h : V ≤ chart ℤ 1 j) (c : Γ(PSpace ℤ 1, V)) :
    (kernel.ι quotMap).app V (c • resM K h (s j)) = (c * ratioOn V j h 0) • eV V 0 + (c * ratioOn V j h 1) • eV V 1 := by
  refine (Scheme.Modules.Hom.app_smul _ _ _).trans ((congrArg (c • ·) ((app_resM _ _ _).trans
    ((congrArg (resM E h) (map_s j)).trans (resM_v j h)))).trans ?_)
  rw [smul_add, mul_smul, mul_smul]

theorem isFrame_const_s (j : Fin 2) : IsFrame fun _ : Fin 1 => s j := fun V h => by
  have hm : Mono (kernel.ι quotMap) := equalizer.ι_mono
  refine ⟨(injective_iff_map_eq_zero _).2 fun c hc => ?_, fun t => ?_⟩
  · have h₁ : c 0 • resM K h (s j) = 0 := by
      simpa [Fintype.linearCombination_apply] using hc
    have h₂ := kernel_ι_app_smul_resM_s j h (c 0)
    rw [h₁, map_zero] at h₂
    have h₃ := comb_injective (V := V) (c₀ := 0) (c₁ := 0) (by simpa using h₂)
    have h₄ : c 0 = 0 := by
      rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1) with rfl | rfl
      · simpa using h₃.1.symm
      · simpa using h₃.2.symm
    exact funext fun i => Subsingleton.elim i 0 ▸ h₄
  · obtain ⟨c₀, c₁, e⟩ := exists_comb ((kernel.ι quotMap).app V t)
    have h₀ := (exact_kernel_ι_app quotMap V ((kernel.ι quotMap).app V t)).2 ⟨t, rfl⟩
    rw [e, quotMap_comb j h] at h₀
    have h₁ := sub_eq_zero.1 (eq_zero_of_smul_chartSec j h _ h₀)
    refine ⟨fun _ => ![c₀, c₁] j, injective_app_of_mono (kernel.ι quotMap) V ?_⟩
    have e₁ : Fintype.linearCombination Γ(PSpace ℤ 1, V) (fun _ : Fin 1 => resM K h (s j)) (fun _ => ![c₀, c₁] j) =
        ![c₀, c₁] j • resM K h (s j) := by
      simp [Fintype.linearCombination_apply]
    rw [e₁, kernel_ι_app_smul_resM_s, e]
    rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1) with rfl | rfl
    · have r₀ : ratioOn V 0 h 0 = 1 := ratioOn_self
      rw [r₀, mul_one] at h₁ ⊢
      simp [h₁]
    · have r₁ : ratioOn V 1 h 1 = 1 := ratioOn_self
      rw [r₁, mul_one] at h₁ ⊢
      simp [h₁]

def t : ∀ j : Fin 2, Γ(E, chart ℤ 1 j) := Fin.cons (eV _ 1) (Fin.cons (-eV _ 0) finZeroElim)

theorem quotMap_app_t_eq_chartSec (j : Fin 2) : quotMap.app _ (t j) = LB.chartSec (O1_isLB ℤ 1) j := by
  rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1) with rfl | rfl
  · exact (quotMap_eV _ 1).trans (resM_X' 0)
  · refine (map_neg _ _).trans ((congrArg (- ·) (quotMap_eV _ 0)).trans ?_)
    refine Eq.trans ?_ (resM_X' 1)
    rw [← map_neg]
    exact congrArg _ (neg_neg _)

def grIso₀ {X : Scheme.{0}} (S : ShortComplex X.Modules) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1)
    (h₂ : IsVB S.X₂ 2) (h₃ : IsVB S.X₃ 1) : (flagOfShortExact S hS h₁ h₂ h₃).gr 0 ≅ S.X₁ :=
  cokernelZeroIsoTarget

def grIso₁ {X : Scheme.{0}} (S : ShortComplex X.Modules) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1)
    (h₂ : IsVB S.X₂ 2) (h₃ : IsVB S.X₃ 1) : (flagOfShortExact S hS h₁ h₂ h₃).gr 1 ≅ S.X₃ :=
  (colimit.isColimit _).coconePointUniqueUpToIso hS.gIsCokernel

theorem π_grIso₁ : flag.π 1 ≫ (grIso₁ seq seq_shortExact isVB_seq₁ (isVB_freeModule_fin _ 2)
    (isVB_toMod (O1_isLB ℤ 1))).hom = quotMap :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom seq_shortExact.gIsCokernel WalkingParallelPair.one

theorem π_grIso₀ : flag.π 0 ≫ (grIso₀ seq seq_shortExact isVB_seq₁ (isVB_freeModule_fin _ 2)
    (isVB_toMod (O1_isLB ℤ 1))).hom = 𝟙 K :=
  by
  change cokernel.π (0 : (0 : (PSpace ℤ 1).Modules) ⟶ K) ≫ cokernelZeroIsoTarget.hom = 𝟙 K
  simp [cokernelZeroIsoTarget]

def adapt₁ (j : Fin 2) : VBExt.AdaptedChart (VMetric.stepSeq flag 1) 1 1 where
  U := chart ℤ 1 j
  e := fun _ => s j
  t := fun _ => t j
  he := isFrame_const_s j
  ht := by
    have := (isFrame_chartSec (O1_isLB ℤ 1) j).map_iso (grIso₁ seq seq_shortExact isVB_seq₁ (isVB_freeModule_fin _ 2)
      (isVB_toMod (O1_isLB ℤ 1))).inv
    have e : (VMetric.stepSeq flag 1).g = quotMap ≫ (grIso₁ seq seq_shortExact isVB_seq₁ (isVB_freeModule_fin _ 2)
      (isVB_toMod (O1_isLB ℤ 1))).inv := (Iso.eq_comp_inv _).2 π_grIso₁
    have e₂ : (VMetric.stepSeq flag 1).g.app (chart ℤ 1 j) (t j) = (grIso₁ seq seq_shortExact isVB_seq₁
        (isVB_freeModule_fin _ 2) (isVB_toMod (O1_isLB ℤ 1))).inv.app _ (LB.chartSec (O1_isLB ℤ 1) j) :=
      (congrArg (fun φ => φ.app _ (t j)) e).trans ((app_app _ _ _ _).symm.trans (congrArg _ (quotMap_app_t_eq_chartSec j)))
    simp only [e₂]
    exact this

theorem isFrame_zero {X : Scheme.{0}} {F : X.Modules} (hF : IsZero F) {U : X.Opens} (e : Fin 0 → Γ(F, U)) : IsFrame e := fun V _ => by
  have : Subsingleton Γ(F, V) := ⟨fun a b => by
    have : Mono (0 : F ⟶ F) := hF.mono _
    refine injective_app_of_mono (0 : F ⟶ F) V ?_
    simp⟩
  exact ⟨Function.injective_of_subsingleton _, fun b => ⟨0, Subsingleton.elim _ _⟩⟩

def adapt₀ (j : Fin 2) : VBExt.AdaptedChart (VMetric.stepSeq flag 0) 0 1 where
  U := chart ℤ 1 j
  e := Fin.elim0
  t := fun _ => s j
  he := isFrame_zero (isZero_zero _) _
  ht := by
    have := (isFrame_const_s j).map_iso (grIso₀ seq seq_shortExact isVB_seq₁ (isVB_freeModule_fin _ 2)
      (isVB_toMod (O1_isLB ℤ 1))).inv
    have e : (VMetric.stepSeq flag 0).g = 𝟙 K ≫ (grIso₀ seq seq_shortExact isVB_seq₁ (isVB_freeModule_fin _ 2)
      (isVB_toMod (O1_isLB ℤ 1))).inv := (Iso.eq_comp_inv _).2 π_grIso₀
    have e₂ : (VMetric.stepSeq flag 0).g.app (chart ℤ 1 j) (s j) = (grIso₀ seq seq_shortExact isVB_seq₁
        (isVB_freeModule_fin _ 2) (isVB_toMod (O1_isLB ℤ 1))).inv.app _ (s j) :=
      (congrArg (fun φ => φ.app _ (s j)) e).trans ((app_app _ _ _ _).symm.trans rfl)
    simp only [e₂]
    exact this

abbrev stdH : HermVB (PSpace.str ℤ 1) 2 := HermVB.std (PSpace.str ℤ 1) 2

variable {σ : ℤ →+* ℂ}

abbrev metE (σ : ℤ →+* ℂ) : Met (PSpace.str ℤ 1) σ E 2 := stdH.h.met σ

abbrev cE : Chart E 2 := ⟨⊤, _, isFrame_freeFrame (PSpace ℤ 1) (Fin 2)⟩

theorem metE_G (y : CxPts (PSpace.str ℤ 1) σ) : (metE σ).G cE y = 1 :=
  Met.ofFrame_G _ _ (fun _ => Matrix.PosDef.one) y

theorem form_comb {V : (PSpace ℤ 1).Opens} (c₀ c₁ d₀ d₁ : Γ(PSpace ℤ 1, V)) {y : CxPts (PSpace.str ℤ 1) σ}
    (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ V) :
    (metE σ).form (c₀ • eV V 0 + c₁ • eV V 1) (d₀ • eV V 0 + d₁ • eV V 1) y =
      ev _ σ V c₀ y * starRingEnd ℂ (ev _ σ V d₀ y) + ev _ σ V c₁ y * starRingEnd ℂ (ev _ σ V d₁ y) := by
  have hc : y ∈ ptsIn (PSpace.str ℤ 1) σ cE.U := mem_ptsIn_top
  have he (a b : Fin 2) : cE.crd _ σ (eV V b) y a = (Pi.single b 1 : Fin 2 → ℂ) a :=
    congrFun ((cE.crd_resM _ le_top hy).trans (cE.crd_frame hc b)) a
  rw [(metE σ).form_eq _ hc _ _ hy, metE_G]
  have e₀ := funext fun a => he a 0
  have e₁ := funext fun a => he a 1
  simp only [Chart.crd_add, Chart.crd_smul, e₀, e₁]
  simp [form_eq_sum, Fin.sum_univ_two, Matrix.one_apply]

theorem form_stepMet₁ {V : (PSpace ℤ 1).Opens} (a b : Γ(E, V)) {y : CxPts (PSpace.str ℤ 1) σ}
    (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ V) :
    ((stdH.h.stepMet flag 1).met σ).form a b y = (metE σ).form a b y :=
  Met.form_restrict (metE σ) (flag.isSubbundle (Fin.succ 1)) (flag.isVB (Fin.succ 1)) a b hy

theorem form_stepMet₀ {V : (PSpace ℤ 1).Opens} (a b : Γ(K, V)) {y : CxPts (PSpace.str ℤ 1) σ}
    (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ V) :
    ((stdH.h.stepMet flag 0).met σ).form a b y = (metE σ).form ((kernel.ι quotMap).app V a) ((kernel.ι quotMap).app V b) y :=
  Met.form_restrict (metE σ) (flag.isSubbundle (Fin.succ 0)) (flag.isVB (Fin.succ 0)) a b hy

def nsqV (j : Fin 2) (y : CxPts (PSpace.str ℤ 1) σ) : ℂ :=
  ev _ σ _ (ratio ℤ 1 j 0) y * starRingEnd ℂ (ev _ σ _ (ratio ℤ 1 j 0) y) +
    ev _ σ _ (ratio ℤ 1 j 1) y * starRingEnd ℂ (ev _ σ _ (ratio ℤ 1 j 1) y)

def ipVT (j : Fin 2) (y : CxPts (PSpace.str ℤ 1) σ) : ℂ :=
  (![ev _ σ _ (ratio ℤ 1 0 1) y, -ev _ σ _ (ratio ℤ 1 1 0) y] : Fin 2 → ℂ) j

theorem t_zero : t 0 = (0 : Γ(PSpace ℤ 1, chart ℤ 1 0)) • eV _ 0 + (1 : Γ(PSpace ℤ 1, chart ℤ 1 0)) • eV _ 1 := by
  rw [zero_smul, one_smul, zero_add]
  rfl

theorem t_one : t 1 = (-1 : Γ(PSpace ℤ 1, chart ℤ 1 1)) • eV _ 0 + (0 : Γ(PSpace ℤ 1, chart ℤ 1 1)) • eV _ 1 := by
  rw [zero_smul, neg_one_smul, add_zero]
  rfl

theorem form_v_v (j : Fin 2) {y : CxPts (PSpace.str ℤ 1) σ} (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ (chart ℤ 1 j)) :
    (metE σ).form (v j) (v j) y = nsqV j y :=
  form_comb _ _ _ _ hy

theorem tautological_lift_norm_one (j : Fin 2) {y : CxPts (PSpace.str ℤ 1) σ} (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ (chart ℤ 1 j)) :
    (metE σ).form (t j) (t j) y = 1 := by
  rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1) with rfl | rfl
  · rw [t_zero, form_comb _ _ _ _ hy]
    simp [ev_eq hy]
  · rw [t_one, form_comb _ _ _ _ hy]
    simp [ev_eq hy]

theorem tautological_inner_product_lift (j : Fin 2) {y : CxPts (PSpace.str ℤ 1) σ} (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ (chart ℤ 1 j)) :
    (metE σ).form (v j) (t j) y = ipVT j y := by
  rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1) with rfl | rfl
  · rw [t_zero, v, form_comb _ _ _ _ hy]
    simp [ev_eq hy, ipVT]
  · rw [t_one, v, form_comb _ _ _ _ hy]
    have r₁ : ratio ℤ 1 1 1 = 1 := ratioOn_self
    simp [ev_eq hy, ipVT, r₁]

theorem gram_adapt₁ (j : Fin 2) {y : CxPts (PSpace.str ℤ 1) σ} (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ (chart ℤ 1 j)) :
    ((stdH.h.stepMet flag 1).met σ).gram (adapt₁ j).frame y =
      Matrix.fromBlocks (Matrix.of fun _ _ => nsqV j y) (Matrix.of fun _ _ => ipVT j y)
        (Matrix.of fun _ _ => starRingEnd ℂ (ipVT j y)) 1 := by
  have e : (kernel.ι quotMap).app _ (s j) = v j := map_s j
  ext (a | a) (b | b)
  · exact (form_stepMet₁ ((kernel.ι quotMap).app _ (s j)) ((kernel.ι quotMap).app _ (s j)) hy).trans
      (e ▸ form_v_v j hy)
  · exact (form_stepMet₁ ((kernel.ι quotMap).app _ (s j)) (t j) hy).trans (e ▸ tautological_inner_product_lift j hy)
  · refine (form_stepMet₁ (t j) ((kernel.ι quotMap).app _ (s j)) hy).trans ?_
    rw [e, ← Met.conj_form, tautological_inner_product_lift j hy]
    rfl
  · refine (form_stepMet₁ (t j) (t j) hy).trans ((tautological_lift_norm_one j hy).trans ?_)
    rw [Subsingleton.elim a b]
    simp

theorem gram_adapt₀ (j : Fin 2) {y : CxPts (PSpace.str ℤ 1) σ} (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ (chart ℤ 1 j))
    (a b : Fin 1) : ((stdH.h.stepMet flag 0).met σ).gram (adapt₀ j).frame y (.inr a) (.inr b) = nsqV j y :=
  (form_stepMet₀ (s j) (s j) hy).trans (map_s j ▸ form_v_v j hy)

end GlobalTheory.TautFlag
