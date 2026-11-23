import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsCuspFunOnePlane
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Doubling GlobalTheory.OpTrace
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp IsIsotropic extSub coordR act unipRad parab)
open GlobalTheory.AutFunCompare (vecOf colSpan repr_vecOf)
open scoped TensorProduct ComplexConjugate InnerProductSpace

namespace GlobalTheory.Cusp

section Span

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {V : HSpace E} {R : Type} [CommRing R] [Algebra F R]

omit [NumberField F] in

theorem mem_extSub_span_lt {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) E} (i : ℕ) (y : Fin V.rank → R ⊗[F] E) :
    y ∈ extSub (F := F) V R (Submodule.span E ((fun k => vecOf V (Cᵀ k)) '' {j | j.val < i})) ↔
      ∃ a : Fin r → R ⊗[F] E, (∀ j, i ≤ j.val → a j = 0) ∧ y = (C.map (inclR (F := F) R)).mulVec a := by
  let C' : Matrix (Fin V.rank) (Fin r) E := fun a j => if j.val < i then C a j else 0
  have e : Submodule.span E ((fun k => vecOf V (Cᵀ k)) '' {j | j.val < i}) = colSpan V C' := by
    refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨j, hj, rfl⟩
      exact ⟨j, congrArg (vecOf V) (funext fun a => if_pos hj)⟩
    · rintro _ ⟨j, rfl⟩
      by_cases hj : j.val < i
      · exact Submodule.subset_span ⟨j, hj, congrArg (vecOf V) (funext fun a => (if_pos hj).symm)⟩
      · have : C'ᵀ j = 0 := funext fun a => if_neg hj
        simp [this, vecOf]
  rw [e, AutFunCompare.mem_extSub_colSpan]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨fun j => if j.val < i then a j else 0, fun j hj => if_neg (not_lt.2 hj), funext fun b => ?_⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j.val < i <;> simp [C', hj]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, funext fun b => ?_⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j.val < i
    · simp [C', hj]
    · rw [ha j (not_lt.1 hj), mul_zero, mul_zero]

theorem act_sub_mem_of_mem_span {S : Set V.V} {A : Submodule E V.V} {g : HA R hc.sig V.gram}
    (h : ∀ x ∈ S, act hc V g (coordR V R x) - coordR V R x ∈ extSub (F := F) V R A) {x : V.V}
    (hx : x ∈ Submodule.span E S) : act hc V g (coordR V R x) - coordR V R x ∈ extSub (F := F) V R A := by
  let f : (Fin V.rank → R ⊗[F] E) →ₗ[R ⊗[F] E] Fin V.rank → R ⊗[F] E :=
    (HA.mat R hc.sig V.gram g).1.mulVecLin - LinearMap.id
  change f (coordR V R x) ∈ _
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [show coordR V R 0 = 0 from funext fun _ => by simp [coordR], map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 =>
    rw [show coordR V R (x + y) = coordR V R x + coordR V R y from funext fun _ => by simp [coordR], map_add]
    exact add_mem h1 h2
  | smul a x _ h1 =>
    rw [show coordR V R (a • x) = inclR (F := F) R a • coordR V R x from funext fun _ => by simp [coordR], map_smul]
    exact Submodule.smul_mem _ _ h1

end Span

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

section Groups

variable (𝔉 : IsoFlag V)

abbrev PA : Subgroup (GA D V) := 𝔉.par D.sp.cm (AF D.host.F)

abbrev NA : Subgroup (GA D V) := 𝔉.unip D.sp.cm (AF D.host.F)

abbrev PQ : Subgroup (PA 𝔉) := (GQ V).subgroupOf (PA 𝔉)

abbrev NQ : Subgroup (NA 𝔉) := (GQ V).subgroupOf (NA 𝔉)

abbrev PLoc (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (AdelicU.GLoc D.sp.cm.sig V.gram v) :=
  𝔉.par D.sp.cm (Fv D.host.F v)

abbrev NLoc (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (AdelicU.GLoc D.sp.cm.sig V.gram v) :=
  𝔉.unip D.sp.cm (Fv D.host.F v)

abbrev PArch (w : InfinitePlace D.host.F) : Subgroup (AdelicU.GArch D.sp.cm.sig V.gram w) := 𝔉.par D.sp.cm w.Completion

abbrev NArch (w : InfinitePlace D.host.F) : Subgroup (AdelicU.GArch D.sp.cm.sig V.gram w) := 𝔉.unip D.sp.cm w.Completion

theorem map_unipRat : (𝔉.unipRat D.sp.cm).map (AdelicU.ratEmb D.sp.cm.sig V.gram) = GQ V ⊓ NA 𝔉 := by
  have : Nontrivial (AF D.host.F) := inferInstanceAs (Nontrivial (Ainf D.host.F × Af D.host.F))
  rw [show 𝔉.unipRat D.sp.cm = (NA 𝔉).comap (AdelicU.ratEmb D.sp.cm.sig V.gram) from
    Subgroup.ext fun _ => IsoFlag.diagH_mem_unip.symm, Subgroup.map_comap_eq, AdelicU.range_ratEmb, AdelicU.GQ_eq]

variable {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}

theorem colSpan_le_perp_iff : colSpan V C ≤ perp V (colSpan V C) ↔
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram * C = 0 := by
  rw [colSpan, Submodule.span_le, Set.range_subset_iff]
  change (∀ k, _ ∈ perp V (colSpan V C)) ↔ _
  simp only [AutFunCompare.mem_perp_colSpan D.sp.cm, repr_vecOf]
  exact ⟨fun h => Matrix.ext fun a k => congrFun (h k) a, fun h k => funext fun a => congrFun (congrFun h a) k⟩

theorem linearIndependent_vecOf (h : LinearIndependent D.host.E Cᵀ) :
    LinearIndependent D.host.E fun k => vecOf V (Cᵀ k) := h.map' V.frame.equivFun.symm.toLinearMap (LinearEquiv.ker _)

def frameFlag (hC : IsIsoFrame V C) : IsoFlag V := .single ((AutFunCompare.isIsoFrame_iff V C).1 hC).2

theorem NA_frameFlag (hC : IsIsoFrame V C) : NA (frameFlag hC) = NI V C :=
  (IsoFlag.unip_single _ _ _).trans (AutFunCompare.NI_eq V C).symm

def columnFlag (hC : IsIsoSub V C) : IsoFlag V :=
  .ofVectors (fun k => vecOf V (Cᵀ k)) (linearIndependent_vecOf hC.1) fun a b =>
    mem_perp.1 (colSpan_le_perp_iff.2 hC.2 (Submodule.subset_span ⟨a, rfl⟩)) _ (Submodule.subset_span ⟨b, rfl⟩)

end Groups

section Const

def constTerm (𝔉 : IsoFlag V) (φ : GA D V → ℂ) : GA D V → ℂ := constTermOn (GQ V) (NA 𝔉) φ

variable {𝔉 : IsoFlag V} {φ : GA D V → ℂ}

theorem cocompact_single {W : Submodule D.host.E V.V} (hW : IsIsotropic V W) : Cocompact (GQ V) (NA (.single hW)) := by
  rw [NA, IsoFlag.unip_single, AutFunCompare.GQ_eq]
  exact AutFunCompare.unipRad_cocompact D.sp.cm V W hW

theorem constTerm_eq {ν : Measure (NA 𝔉)} [ν.IsHaarMeasure] {𝓕 : Set (NA 𝔉)} (h : IsFundamentalDomain (NQ 𝔉) 𝓕 ν)
    (hφ : LeftInv (GQ V) φ) (x : GA D V) : constTerm 𝔉 φ x = (ν.real 𝓕)⁻¹ • ∫ n in 𝓕, φ (n * x) ∂ν :=
  constTermOn_eq h hφ x

theorem isCuspFun_iff (hφ : LeftInv (GQ V) φ) :
    IsCuspFun V φ ↔ ∀ (W : Submodule D.host.E V.V) (hW : IsIsotropic V W), constTerm (.single hW) φ = 0 := by
  let Z : Subgroup (GA D V) → Prop := fun N => ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure →
    IsFundamentalDomain ((GQ V).subgroupOf N) 𝓕 μ → ∀ g, ∫ n in 𝓕, φ ((n : GA D V) * g) ∂μ = 0
  have key : ∀ {W} (hW : IsIsotropic V W), constTerm (.single hW) φ = 0 ↔ Z (NA (.single hW)) := fun hW =>
    ⟨fun h μ 𝓕 _ h𝓕 g => ((cocompact_single hW).constTermOn_eq_zero_iff h𝓕 hφ g).1 (congrFun h g),
      fun h => funext fun g => ((cocompact_single hW).constTermOn_eq_zero_iff
        (isFundamentalDomain_stdDom _ Measure.haar) hφ g).2 (h _ _ inferInstance (isFundamentalDomain_stdDom _ _) g)⟩
  refine ⟨fun h W hW => ?_, fun h r C hC => ?_⟩
  · obtain ⟨r, C, hC, rfl⟩ := (AutFunCompare.isIsotropic_iff V W).1 hW
    exact (key hW).2 ((congrArg Z (NA_frameFlag hC)).mpr (h r C hC))
  · exact (congrArg Z (NA_frameFlag hC)).mp ((key _).1 (h _ _))

theorem isCuspFun_of_forall_flag (hφ : LeftInv (GQ V) φ) (h : ∀ 𝔉 : IsoFlag V, 𝔉.Proper → constTerm 𝔉 φ = 0) :
    IsCuspFun V φ := (isCuspFun_iff hφ).2 fun _ hW => h _ (IsoFlag.proper_single hW)

theorem isCuspFun_rTr (h : IsCuspFun V φ) (k : GA D V) : IsCuspFun V (rTr V k φ) :=
  fun r C hC μ 𝓕 hμ h𝓕 g => by simpa only [rTr, mul_assoc] using h r C hC μ 𝓕 hμ h𝓕 (g * k)

variable (V) in

def cuspCont : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | Continuous φ ∧ LeftInv (GQ V) φ ∧ IsCuspFun V φ}
  zero_mem' := ⟨continuous_zero, fun _ _ _ => rfl, CuspDecay.Model.isCuspFun_zero V⟩
  add_mem' := fun {φ ψ} h h' =>
    have hl : LeftInv (GQ V) (φ + ψ) := fun γ hγ g => congrArg₂ (· + ·) (h.2.1 γ hγ g) (h'.2.1 γ hγ g)
    ⟨h.1.add h'.1, hl, (isCuspFun_iff hl).2 fun W hW => funext fun x =>
      ((cocompact_single hW).constTermOn_add h.2.1 h.1 h'.2.1 h'.1 x).trans <| by
        rw [show constTermOn _ _ φ x = 0 from congrFun ((isCuspFun_iff h.2.1).1 h.2.2 W hW) x,
          show constTermOn _ _ ψ x = 0 from congrFun ((isCuspFun_iff h'.2.1).1 h'.2.2 W hW) x]
        simp⟩
  smul_mem' := fun c φ h => ⟨h.1.const_smul c, fun γ hγ g => congrArg (c • ·) (h.2.1 γ hγ g),
    fun r C hC μ 𝓕 hμ h𝓕 g => (integral_const_mul c _).trans (by rw [h.2.2 r C hC μ 𝓕 hμ h𝓕 g, mul_zero])⟩

theorem mem_cuspCont : φ ∈ cuspCont V ↔ Continuous φ ∧ LeftInv (GQ V) φ ∧ IsCuspFun V φ := Iff.rfl

theorem rTr_mem_cuspCont (h : φ ∈ cuspCont V) (k : GA D V) : rTr V k φ ∈ cuspCont V :=
  ⟨h.1.comp (continuous_mul_const k), h.2.1.mul_right k, isCuspFun_rTr h.2.2 k⟩

theorem conj_mem_cuspCont (h : φ ∈ cuspCont V) : (fun g => conj (φ g)) ∈ cuspCont V :=
  ⟨Complex.continuous_conj.comp h.1, fun γ hγ g => congrArg conj (h.2.1 γ hγ g),
    fun r C hC μ 𝓕 hμ h𝓕 g => integral_conj.trans (by rw [h.2.2 r C hC μ 𝓕 hμ h𝓕 g, map_zero])⟩

end Const

section L2

variable (V) (μ : Measure (GA D V))

def cuspContinuousL2 [μ.IsMulLeftInvariant] : Submodule ℂ (DividedPowerChartLift V μ) where
  carrier := {F | ∃ φ ∈ cuspCont V, lift (GQ V) F =ᵐ[μ] φ}
  zero_mem' := ⟨0, zero_mem _, ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)⟩
  add_mem' := fun {F F'} ⟨_, h, e⟩ ⟨_, h', e'⟩ =>
    ⟨_, add_mem h h', Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_add F F')) (e.add e')⟩
  smul_mem' := fun c F ⟨_, h, e⟩ =>
    ⟨_, Submodule.smul_mem _ c h, Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_smul c F)) (e.const_smul c)⟩

def L2cusp [μ.IsMulLeftInvariant] : Submodule ℂ (DividedPowerChartLift V μ) := (cuspContinuousL2 V μ).topologicalClosure

def IsCuspAE (F : DividedPowerChartLift V μ) : Prop := ∀ 𝔉 : IsoFlag V, 𝔉.Proper → constTerm 𝔉 (lift (GQ V) F) =ᵐ[μ] 0

variable {V μ} {φ ψ : GA D V → ℂ}

theorem toL2_mem_cuspidal [μ.IsMulLeftInvariant] (h : MemL2Quotient (GQ V) μ φ) (hφ : φ ∈ cuspCont V) : h.toL2 ∈ L2cusp V μ :=
  Submodule.le_topologicalClosure _ ⟨φ, hφ, h.lift_toL2_ae_eq⟩

theorem mem_L2cusp_of_ae_eq [μ.IsMulLeftInvariant] {F : DividedPowerChartLift V μ} (hφ : φ ∈ cuspCont V) (e : lift (GQ V) F =ᵐ[μ] φ) :
    F ∈ L2cusp V μ := Submodule.le_topologicalClosure _ ⟨φ, hφ, e⟩

theorem L2cusp_le [μ.IsMulLeftInvariant] {U : Submodule ℂ (DividedPowerChartLift V μ)} (hU : IsClosed (U : Set (DividedPowerChartLift V μ)))
    (h : ∀ φ ∈ cuspCont V, ∀ h : MemL2Quotient (GQ V) μ φ, h.toL2 ∈ U) : L2cusp V μ ≤ U := by
  refine Submodule.topologicalClosure_minimal _ ?_ hU
  rintro F ⟨φ, hφ, e⟩
  have hd := isFundamentalDomain_stdDom (GQ V) μ
  have h2 : MemL2Quotient (GQ V) μ φ :=
    (memL2_iff_fundamental_domain hd).2 ⟨hφ.2.1, ((memL2_iff_fundamental_domain hd).1 (memL2_lift F)).2.ae_eq (ae_restrict_of_ae e)⟩
  exact l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (h2.lift_toL2_ae_eq.trans e.symm) ▸ h φ hφ h2

variable (V μ) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem isSubrep_L2cusp : IsSubrep (RG V μ) (L2cusp V μ) :=
  isSubrep_topologicalClosure fun g F ⟨_, h, e⟩ => ⟨_, rTr_mem_cuspCont h g,
    (lift_R g F).trans ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae e)⟩

omit [μ.IsMulRightInvariant] in

instance : CompleteSpace (L2cusp V μ) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe

abbrev Rcusp : GA D V →* (L2cusp V μ →L[ℂ] L2cusp V μ) := (isSubrep_L2cusp V μ).rep

abbrev RcuspOp (f : GA D V → ℂ) : L2cusp V μ →L[ℂ] L2cusp V μ := repOp (Rcusp V μ) μ f

theorem isUnitaryRep_Rcusp : IsUnitaryRep (Rcusp V μ) := (isSubrep_L2cusp V μ).isUnitaryRep (isUnitaryRep_RG V μ)

theorem coe_RcuspOp {f : GA D V → ℂ} (hf : Integrable f μ) (F : L2cusp V μ) :
    (RcuspOp V μ f F : DividedPowerChartLift V μ) = RopG V μ f F := ((isSubrep_L2cusp V μ).coe_repOp_rep (isRepOp_Rop hf)).2 F

end L2

section Forms

variable (θ : InfF D) (V : HSp D)

def IsCartanFrame (A : CptF V) : Prop :=
  ∀ τ, (A τ)ᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * A τ = gramAt D V τ

theorem exists_isCartanFrame (hV : V.SigOK) : ∃ A, IsCartanFrame V A := by
  choose e P h using fun τ => hV (tauE D τ)
  refine ⟨fun τ => ((P τ)⁻¹).1.submatrix id (e τ), fun τ => ?_⟩
  have h1 : ((P τ)⁻¹).1ᴴ * (P τ).1ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  have h2 : ((P τ)⁻¹).1ᴴ * Formalism.UG.Jpq _ _ * ((P τ)⁻¹).1 = (gramAt D V τ).reindex (e τ) (e τ) := by
    rw [← h τ, show Formalism.UG.cT (starRingEnd ℂ) (P τ).1 = (P τ).1ᴴ from rfl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1,
      Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]; rfl
  ext i j
  simpa [Matrix.mul_apply] using congrFun (congrFun h2 (e τ i)) (e τ j)

theorem isKC_mul {p q : ℕ} {a b : Mat p q} (ha : IsKC a) (hb : IsKC b) : IsKC (a * b) := fun i j h =>
  Matrix.mul_apply.trans <| Finset.sum_eq_zero fun k _ => by
    by_cases e : sameBlock i k
    · rw [hb k j fun e' => h (by cases i <;> cases j <;> cases k <;> simp_all [sameBlock]), mul_zero]
    · rw [ha i k e, zero_mul]

def blockAlg {p q n : ℕ} (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) : Subalgebra ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {g | ∃ b : Mat p q, IsKC b ∧ b * A = A * g}
  mul_mem' := fun ⟨a, ha, e⟩ ⟨b, hb, e'⟩ =>
    ⟨a * b, isKC_mul ha hb, by rw [Matrix.mul_assoc, e', ← Matrix.mul_assoc, e, Matrix.mul_assoc]⟩
  add_mem' := fun ⟨a, ha, e⟩ ⟨b, hb, e'⟩ => ⟨a + b, fun i j h => by rw [Matrix.add_apply, ha i j h, hb i j h, add_zero],
    by rw [Matrix.add_mul, e, e', Matrix.mul_add]⟩
  algebraMap_mem' c := ⟨c • 1, fun i j h => by
    rw [Matrix.smul_apply, Matrix.one_apply_ne (by rintro rfl; cases i <;> exact h trivial), smul_zero],
    by simp [Algebra.algebraMap_eq_smul_one]⟩

def Kinf (A : CptF V) : Subgroup (GA D V) where
  carrier := {g | IsKinf θ V A g}
  one_mem' := ⟨one_mem _, fun τ => by
    rw [SmoothForms.HeightCoset.infMat_one']; exact (blockAlg (A τ)).one_mem⟩
  mul_mem' := fun h h' => ⟨mul_mem h.1 h'.1, fun τ => by
    rw [SmoothForms.HeightCoset.infMat_mul']; exact (blockAlg (A τ)).mul_mem (h.2 τ) (h'.2 τ)⟩
  inv_mem' := fun {g} h => ⟨inv_mem h.1, fun τ => by
    have e : infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) g = 1 := by
      rw [← SmoothForms.HeightCoset.infMat_mul', inv_mul_cancel, SmoothForms.HeightCoset.infMat_one']
    obtain ⟨s, hs⟩ := (LinearMap.injective_iff_surjective (f := LinearMap.mulLeft ℂ (⟨_, h.2 τ⟩ : blockAlg (A τ)))).1
      (fun a b hab => Subtype.ext (by
        simpa only [← Matrix.mul_assoc, e, Matrix.one_mul, LinearMap.mulLeft_apply, MulMemClass.coe_mul] using
          congrArg (fun z : blockAlg (A τ) => infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ * z.1) hab)) 1
    have h1 : infMat D.sp.cm.sig V.gram (θ τ) g * s.1 = 1 := congrArg Subtype.val hs
    have h2 : infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ = s.1 := by
      rw [← Matrix.mul_one (infMat _ _ _ g⁻¹), ← h1, ← Matrix.mul_assoc, e, Matrix.one_mul]
    exact h2 ▸ s.2⟩

variable (K : Subgroup (GA D V))

def autForms : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | IsAutFunSm θ V φ ∧ IsKFinite K φ}
  zero_mem' := ⟨isAutFunSm_const θ V 0, .of_invariant fun _ _ _ => rfl⟩
  add_mem' := fun h h' => ⟨Mem.AutSpace.isAutFunSm_add h.1 h'.1, h.2.add h'.2⟩
  smul_mem' := fun c _ h => ⟨Mem.AutSpace.isAutFunSm_smul c h.1,
    let ⟨W, hW, e⟩ := isKFinite_iff.1 h.2
    isKFinite_iff.2 ⟨W, hW, fun k hk => W.smul_mem c (e k hk)⟩⟩

def cuspForms : Submodule ℂ (GA D V → ℂ) := autForms θ V K ⊓ cuspCont V

abbrev A0 (A : CptF V) : Submodule ℂ (GA D V → ℂ) := cuspForms θ V (Kinf θ V A)

abbrev petersson (μ : Measure (GA D V)) (φ ψ : GA D V → ℂ) : ℂ := pet (GQ V) μ φ ψ

variable {θ V K} {A : CptF V} {φ ψ : GA D V → ℂ} {μ : Measure (GA D V)}

theorem mem_Kinf {g : GA D V} : g ∈ Kinf θ V A ↔ IsKinf θ V A g := Iff.rfl

theorem Kinf_le : Kinf θ V A ≤ GinfC V := fun _ h => h.1

theorem mem_autForms : φ ∈ autForms θ V K ↔ IsAutFunSm θ V φ ∧ IsKFinite K φ := Iff.rfl

theorem mem_cuspForms : φ ∈ cuspForms θ V K ↔ IsCuspForm θ V φ ∧ IsKFinite K φ :=
  ⟨fun h => ⟨⟨h.1.1, h.2.2.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.1.cont, h.1.1.left, h.1.2⟩⟩

theorem rTr_fin_mem_autForms (hθ : IsInfFam θ) (hK : K ≤ GinfC V) (h : φ ∈ autForms θ V K) {g : GA D V}
    (hg : g ∈ GfC V) : rTr V g φ ∈ autForms θ V K := by
  refine ⟨Mem.FinTranslate.isAutFunSm_rTr_fin D θ hθ V φ h.1 g hg, ?_⟩
  obtain ⟨W, hW, e⟩ := isKFinite_iff.1 h.2
  refine isKFinite_iff.2 ⟨W.map (LinearMap.funLeft ℂ ℂ (· * g)), inferInstance, fun k hk => ⟨_, e k hk, funext fun x => ?_⟩⟩
  have hc : k * g = g * k := AdelicU.ext_inf_fin _ _ (by simp [AdelicU.mem_finPts.1 hg])
    (by simp [AdelicU.mem_infPts.1 (hK hk)])
  exact congrArg φ (by rw [mul_assoc, mul_assoc, hc])

theorem rTr_fin_mem_cuspForms (hθ : IsInfFam θ) (hK : K ≤ GinfC V) (h : φ ∈ cuspForms θ V K) {g : GA D V}
    (hg : g ∈ GfC V) : rTr V g φ ∈ cuspForms θ V K := ⟨rTr_fin_mem_autForms hθ hK h.1 hg, rTr_mem_cuspCont h.2 g⟩

instance isFiniteMeasure_autMeasure [μ.IsHaarMeasure] : IsFiniteMeasure (autMeasure V μ) :=
  ⟨(quotMeasure_univ (isFundamentalDomain_stdDom _ μ)).trans_lt
    (CuspDecay.measure_lt_top Mem.VolFin.finVol V μ _ inferInstance (isFundamentalDomain_stdDom _ μ))⟩

theorem memL2_of_bounded_continuous_invariant [μ.IsHaarMeasure] (hl : LeftInv (GQ V) φ) (hc : Continuous φ) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) :
    MemL2Quotient (GQ V) μ φ :=
  ⟨hl, .of_bound (aestronglyMeasurable_quotMeasure_iff_lift.2 (hl.lift_descend.symm ▸ hc.aestronglyMeasurable)) C
    (.of_forall fun _ => hC _)⟩

theorem memL2_of_cusp_form (hP : Published.CuspRapidDecay) (hθ : IsInfFam θ) [μ.IsHaarMeasure] (h : IsCuspForm θ V φ) :
    MemL2Quotient (GQ V) μ φ :=
  let ⟨_, hC⟩ := CuspDecay.bounded_of_cuspForm hP hθ h.1 h.2
  memL2_of_bounded_continuous_invariant h.1.left h.1.cont hC

variable (K μ) in

def cuspToL2 (hP : Published.CuspRapidDecay) (hθ : IsInfFam θ) [μ.IsHaarMeasure] : cuspForms θ V K →ₗ[ℂ] L2cusp V μ where
  toFun φ := ⟨_, toL2_mem_cuspidal (memL2_of_cusp_form hP hθ (mem_cuspForms.1 φ.2).1) φ.2.2⟩
  map_add' φ ψ := Subtype.ext (MemLp.toLp_add (memL2_of_cusp_form hP hθ (mem_cuspForms.1 φ.2).1).2
    (memL2_of_cusp_form hP hθ (mem_cuspForms.1 ψ.2).1).2)
  map_smul' c φ := Subtype.ext (MemLp.toLp_const_smul c (memL2_of_cusp_form hP hθ (mem_cuspForms.1 φ.2).1).2)

theorem lift_cusp_form_toL2 (hP : Published.CuspRapidDecay) (hθ : IsInfFam θ) [μ.IsHaarMeasure] (φ : cuspForms θ V K) :
    lift (GQ V) (cuspToL2 K μ hP hθ φ : DividedPowerChartLift V μ) =ᵐ[μ] φ :=
  (memL2_of_cusp_form hP hθ (mem_cuspForms.1 φ.2).1).lift_toL2_ae_eq

theorem cusp_form_toL2_injective (hP : Published.CuspRapidDecay) (hθ : IsInfFam θ) [μ.IsHaarMeasure] :
    Function.Injective (cuspToL2 (V := V) K μ hP hθ) := fun φ ψ h =>
  Subtype.ext ((Continuous.ae_eq_iff_eq μ φ.2.2.1 ψ.2.2.1).1
    ((lift_cusp_form_toL2 hP hθ φ).symm.trans (h ▸ lift_cusp_form_toL2 hP hθ ψ)))

theorem petersson_inner_eq_integral_quotient (hP : Published.CuspRapidDecay) (hθ : IsInfFam θ) [μ.IsHaarMeasure] (φ ψ : cuspForms θ V K) :
    ⟪cuspToL2 K μ hP hθ ψ, cuspToL2 K μ hP hθ φ⟫_ℂ = petersson V μ φ ψ :=
  (Submodule.coe_inner _ _ _).trans ((memL2_of_cusp_form hP hθ (mem_cuspForms.1 φ.2).1).inner_toL2_eq_theta_pairing
    (memL2_of_cusp_form hP hθ (mem_cuspForms.1 ψ.2).1))

theorem petersson_eq [μ.IsMulLeftInvariant] {𝓕 : Set (GA D V)} (h : IsFundamentalDomain (GQ V) 𝓕 μ)
    (hφ : LeftInv (GQ V) φ) (hψ : LeftInv (GQ V) ψ) : petersson V μ φ ψ = ∫ g in 𝓕, φ g * conj (ψ g) ∂μ := pet_eq h hφ hψ

theorem petersson_conj_symm (φ ψ : GA D V → ℂ) : conj (petersson V μ ψ φ) = petersson V μ φ ψ :=
  integral_conj.symm.trans (integral_congr_ae (.of_forall fun _ => by simp [mul_comm]))

theorem petersson_smul_left (c : ℂ) (φ ψ : GA D V → ℂ) : petersson V μ (c • φ) ψ = c * petersson V μ φ ψ :=
  (integral_congr_ae (.of_forall fun _ => mul_assoc _ _ _)).trans (integral_const_mul c _)

theorem petersson_add_left {φ' : GA D V → ℂ} (h : MemL2Quotient (GQ V) μ φ) (h' : MemL2Quotient (GQ V) μ φ') (hψ : MemL2Quotient (GQ V) μ ψ) :
    petersson V μ (φ + φ') ψ = petersson V μ φ ψ + petersson V μ φ' ψ :=
  (integral_congr_ae (.of_forall fun _ => add_mul _ _ _)).trans
    (integral_add (h.integrable_mul_conj hψ) (h'.integrable_mul_conj hψ))

theorem petersson_rTr [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (h : MemL2Quotient (GQ V) μ φ) (h' : MemL2Quotient (GQ V) μ ψ)
    (g : GA D V) : petersson V μ (rTr V g φ) (rTr V g ψ) = petersson V μ φ ψ := by
  refine ((h.mul_right g).inner_toL2_eq_theta_pairing (h'.mul_right g)).symm.trans (Eq.trans ?_ (h.inner_toL2_eq_theta_pairing h'))
  rw [← right_translate_toL2, ← right_translate_toL2, (isUnitaryRep_RG V μ).inner_apply_left, ← mul_apply_eq_comp, ← map_mul,
    inv_mul_cancel, map_one, one_apply_eq_self]

theorem petersson_self_pos [μ.IsHaarMeasure] (h : MemL2Quotient (GQ V) μ φ) (hc : Continuous φ) (h0 : φ ≠ 0) :
    0 < (petersson V μ φ φ).re := by
  rw [petersson, ← h.inner_toL2_eq_theta_pairing h]
  refine (re_inner_self_pos (𝕜 := ℂ)).2 fun e => h0 ((Continuous.ae_eq_iff_eq μ hc continuous_zero).1 ?_)
  exact h.lift_toL2_ae_eq.symm.trans (e ▸ ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _))

end Forms

section Witt

theorem le_wittIndex_iff_isIsoSub {i : ℕ} :
    i ≤ wittIndex V ↔ ∃ C : Matrix (Fin V.rank) (Fin i) D.host.E, IsIsoSub V C := by
  refine ⟨fun h => ?_, fun ⟨_, hC⟩ => (columnFlag hC).k_le_wittIndex⟩
  obtain ⟨W, hW, e⟩ := le_wittIndex_iff.1 h
  obtain ⟨r, C, hC, rfl⟩ := AutFunCompare.exists_colSpan V W
  obtain rfl : r = i := ((finrank_span_eq_card (linearIndependent_vecOf hC)).trans (Fintype.card_fin r)).symm.trans e
  exact ⟨C, hC, colSpan_le_perp_iff.1 hW⟩

theorem wittIndex_eq_zero_iff_isAniso : wittIndex V = 0 ↔ IsAniso V := by
  rw [← not_iff_not, ← Ne, ← Nat.pos_iff_ne_zero, wittIndex_pos_iff, IsAniso]
  push Not
  exact ⟨fun ⟨W, hW⟩ => let ⟨r, C, hC, _⟩ := (AutFunCompare.isIsotropic_iff V W).1 hW; ⟨r, C, hC⟩,
    fun ⟨_, C, hC⟩ => ⟨_, ((AutFunCompare.isIsoFrame_iff V C).1 hC).2⟩⟩

theorem exists_isWittLower_iff {i : ℕ} : (∃ V' : HSp D, IsWittLower V V' i ∧ V'.SigOK) ↔ i ≤ wittIndex V :=
  ⟨fun ⟨_, ⟨_, _, _, C, hC, _⟩, _⟩ => le_wittIndex_iff_isIsoSub.2 ⟨C, hC⟩,
    fun h => WittLow.wittLowEx D V i (le_wittIndex_iff_isIsoSub.1 h)⟩

variable (V) in

def minusHyp (i : ℕ) (h : i ≤ wittIndex V) : HSp D := (exists_isWittLower_iff.2 h).choose

theorem isWittLower_minusHyp {i : ℕ} (h : i ≤ wittIndex V) : IsWittLower V (minusHyp V i h) i :=
  (exists_isWittLower_iff.2 h).choose_spec.1

theorem rank_minusHyp {i : ℕ} (h : i ≤ wittIndex V) : (minusHyp V i h).rank + 2 * i = V.rank :=
  (isWittLower_minusHyp h).1

variable (V) in

theorem two_mul_wittIndex_le : 2 * wittIndex V ≤ V.rank := Nat.le_add_left _ _ |>.trans (rank_minusHyp le_rfl).le

end Witt

section Examples

open CuspDecay.Model

def planeFlag (D : D7) : IsoFlag (plane D) := frameFlag (isIsoFrame_plane D)

theorem wittIndex_plane (D : D7) : wittIndex (plane D) = 1 := by
  have h1 : 2 * wittIndex (plane D) ≤ 2 := two_mul_wittIndex_le (plane D)
  have h2 : 1 ≤ wittIndex (plane D) := (planeFlag D).k_le_wittIndex
  omega

example (D : D7) (c : ℂ) (x : GA D (plane D)) : constTerm (planeFlag D) (fun _ => c) x = c :=
  (cocompact_single ((AutFunCompare.isIsoFrame_iff _ _).1 (isIsoFrame_plane D)).2).constTermOn_const c x

example (θ : InfF D) (K : Subgroup (GA D V)) : (fun _ => (1 : ℂ)) ∈ cuspForms θ V K ↔ wittIndex V = 0 := by
  rw [wittIndex_eq_zero_iff_isAniso, mem_cuspForms]
  exact ⟨fun h r C hC => not_isCuspFun_const V hC one_ne_zero h.1.2,
    fun h => ⟨⟨isAutFunSm_const θ V 1, fun r C hC => absurd hC (h r C)⟩, .of_invariant fun _ _ _ => rfl⟩⟩

example (μ : Measure (GA D V)) (φ ψ : GA D V → ℂ) :
    petersson V μ φ (Complex.I • ψ) = -Complex.I * petersson V μ φ ψ := by
  rw [← petersson_conj_symm, petersson_smul_left, map_mul, Complex.conj_I, petersson_conj_symm]

end Examples

end GlobalTheory.Cusp

end
