import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactLatticeGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteTopologyRatN

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.OpTrace GlobalTheory.IdeleCovolume GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele

namespace GlobalTheory.CuspRep.CuspidalL2GL

section Top

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

scoped instance t2Space_GA : T2Space (GA E a) :=
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  Units.isEmbedding_embedProduct.t2Space

scoped instance locallyCompactSpace_GA : LocallyCompactSpace (GA E a) :=
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Ad E))
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance secondCountableTopology_GA : SecondCountableTopology (GA E a) :=
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance measurableSpace_GA : MeasurableSpace (GA E a) := borel _

scoped instance borelSpace_GA : BorelSpace (GA E a) := ⟨rfl⟩

variable {E a} in

theorem continuous_unip {r : ℕ} : Continuous (unip : (BlockIx a r → Ad E) → GA E a) := by
  have h : Continuous (nilM : (BlockIx a r → Ad E) → Matrix (Fin a) (Fin a) (Ad E)) :=
    continuous_matrix fun i j => by
      simp only [nilM, Matrix.of_apply]
      split_ifs
      · exact continuous_apply _
      · exact continuous_const
  exact Units.continuous_iff.2 ⟨continuous_const.add h, continuous_const.sub h⟩

end Top

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

section Lattice

theorem splitCentre_eq_scalar (t : ℝ) : splitCentre E a t =
    GeneralLinearGroup.scalar (Fin a) (infId E (expU fun _ : InfinitePlace E => (t : ℂ))) := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
    sInf E (Matrix.scalar (Fin a) (_ : Cinf E) i j) = Matrix.scalar (Fin a) (1 - sInf E 1 + sInf E _) i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem splitCentre_comm (t : ℝ) (g : GA E a) : splitCentre E a t * g = g * splitCentre E a t := by
  rw [splitCentre_eq_scalar]
  exact Units.ext (Matrix.scalar_commute _ (fun _ => Commute.all _ _) g.val).eq

theorem splitCentre_add (s t : ℝ) : splitCentre E a (s + t) = splitCentre E a s * splitCentre E a t := by
  rw [splitCentre, splitCentre, splitCentre, ← map_mul, ← map_mul, ← expU_add]
  congr 3
  funext w
  simp

theorem splitCentre_zero : splitCentre E a 0 = 1 := by
  simpa using splitCentre_add (E := E) (a := a) 0 0

theorem splitCentre_intCast (n : ℤ) : splitCentre E a n = splitCentre E a 1 ^ n := by
  let f : Multiplicative ℝ →* GA E a :=
    ⟨⟨fun t => splitCentre E a t.toAdd, splitCentre_zero⟩, fun s t => splitCentre_add _ _⟩
  have := map_zpow f (Multiplicative.ofAdd 1) n
  simpa [f] using this

theorem det_splitCentre_one : GeneralLinearGroup.det (splitCentre E a 1) = eIdele E ^ a := by
  rw [splitCentre_eq_scalar]
  refine Units.ext ?_
  change (Matrix.scalar (Fin a) (eIdele E : Ad E)).det = _
  simp

theorem ratGL_mem_latticeGL (γ : GL (Fin a) E) : ratGL E a γ ∈ latticeGL E a := Subgroup.mem_sup_left ⟨γ, rfl⟩

theorem zpow_mem_latticeGL (n : ℤ) : splitCentre E a 1 ^ n ∈ latticeGL E a := Subgroup.mem_sup_right ⟨n, rfl⟩

theorem mem_latticeGL_iff {g : GA E a} :
    g ∈ latticeGL E a ↔ ∃ (γ : GL (Fin a) E) (n : ℤ), ratGL E a γ * splitCentre E a 1 ^ n = g := by
  refine ⟨fun h => ?_, by rintro ⟨γ, n, rfl⟩; exact mul_mem (ratGL_mem_latticeGL γ) (zpow_mem_latticeGL n)⟩
  have : (Subgroup.zpowers (splitCentre E a 1)).Normal := ⟨by
    rintro _ ⟨n, rfl⟩ x
    refine ⟨n, ?_⟩
    beta_reduce
    rw [← splitCentre_intCast, ← splitCentre_comm, mul_inv_cancel_right]⟩
  obtain ⟨_, ⟨γ, rfl⟩, _, ⟨n, rfl⟩, e⟩ := Subgroup.mem_sup_of_normal_right.1 h
  exact ⟨γ, n, e⟩

scoped instance discreteTopology_latticeGL : DiscreteTopology (latticeGL E a) := by
  obtain ⟨W, hW, h⟩ := exists_nhds_idele E
  obtain ⟨U, hU, h0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero E
  refine discreteTopology_of_isOpen_singleton_one (isOpen_iff_mem_nhds.2 ?_)
  rintro _ rfl
  have h1 : ∀ᶠ γ : latticeGL E a in 𝓝 1, GeneralLinearGroup.det (γ : GA E a) ∈ W :=
    (GeneralLinearGroup.continuous_det.comp continuous_subtype_val).continuousAt.preimage_mem_nhds (by simpa using hW)
  have h2 : ∀ᶠ γ : latticeGL E a in 𝓝 1, ∀ i j, ((γ : GA E a).val - 1) i j ∈ U := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    have hc : Continuous fun γ : latticeGL E a => ((γ : GA E a).val - 1) i j :=
      ((Units.continuous_val.comp continuous_subtype_val).sub continuous_const).matrix_elem i j
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  filter_upwards [h1, h2] with ⟨g, hg⟩ e1 e2
  obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
  have hd : GeneralLinearGroup.det (ratGL E a γ) = diag E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  rw [map_mul, map_zpow, hd, det_splitCentre_one, ← zpow_natCast, ← _root_.zpow_mul] at e1
  have h3 := congrArg (ideleNorm (E := E)) (h _ _ e1)
  rw [map_mul, map_zpow, map_one, show ideleNorm (E := E) (diag E _) = 1 from ideleNorm_principalIdele _, one_mul,
    zpow_eq_one_iff_right₀ (zero_lt_one.trans (one_lt_ideleNorm_eIdele E)).le (one_lt_ideleNorm_eIdele E).ne',
    mul_eq_zero] at h3
  refine Subtype.ext ?_
  rcases h3 with h3 | rfl
  · obtain rfl : a = 0 := by exact_mod_cast h3
    exact Subsingleton.elim _ _
  · simp only [zpow_zero, mul_one] at e2 ⊢
    have : γ = 1 := Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => h0 _ (by
      convert e2 i j using 1
      simp [ratGL, Matrix.one_apply, apply_ite (algebraMap E (Ad E))])))
    rw [this, map_one]
    rfl

theorem leftInv_latticeGL_iff {X : Type*} {φ : GA E a → X} : LeftInv (latticeGL E a) φ ↔
    (∀ γ g, φ (ratGL E a γ * g) = φ g) ∧ ∀ (n : ℤ) g, φ (splitCentre E a n * g) = φ g :=
  ⟨fun h => ⟨fun γ => h _ (ratGL_mem_latticeGL γ), fun n => h _ (splitCentre_intCast (E := E) (a := a) n ▸ zpow_mem_latticeGL n)⟩,
    fun h γ hγ g => by
      obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hγ
      rw [mul_assoc, h.1, ← splitCentre_intCast, h.2]⟩

theorem leftInv_latticeGL {X : Type*} {φ : GA E a → X} (h : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (h' : ∀ t g, φ (splitCentre E a t * g) = φ g) : LeftInv (latticeGL E a) φ :=
  leftInv_latticeGL_iff.2 ⟨h, fun _ => h' _⟩

end Lattice

section Cusp

variable {φ ψ : GA E a → ℂ}

omit [IsTotallyComplex E] in

theorem integrableOn_unip (hc : Continuous φ) (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g) {r : ℕ}
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (ν : Measure (BlockIx a r → Ad E))
    [ν.IsAddHaarMeasure] {𝓕 : Set (BlockIx a r → Ad E)} (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 ν) (g : GA E a) :
    IntegrableOn (fun x => φ (unip x * g)) 𝓕 ν := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.ConstNotCusp.discreteTopology_ratN E a r
  haveI : Countable (ratN E a r) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  have hf : Continuous fun x : BlockIx a r → Ad E => φ (unip x * g) := hc.comp (continuous_unip.mul continuous_const)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine Measure.integrableOn_of_bounded (M := C)
    (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact _ hK hcov ν h𝓕).ne hf.aestronglyMeasurable
    (.of_forall fun x => ?_)
  obtain ⟨_, ⟨y, rfl⟩, hk⟩ := hcov x
  have := hC _ hk
  rw [unip_add, mul_assoc] at this
  exact (congrArg norm ((congrArg (fun u => φ (u * _)) (unip_algebraMap y)).trans (hl _ _))).symm.trans_le this

variable (E a) in

def cuspCont : Submodule ℂ (GA E a → ℂ) where
  carrier := {φ | Continuous φ ∧ (∀ γ g, φ (ratGL E a γ * g) = φ g) ∧ (∀ t g, φ (splitCentre E a t * g) = φ g) ∧
    IsCuspidal φ}
  zero_mem' := ⟨continuous_zero, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ => integral_zero _ _⟩
  add_mem' := fun {φ ψ} h h' =>
    ⟨h.1.add h'.1, fun γ g => congrArg₂ (· + ·) (h.2.1 γ g) (h'.2.1 γ g),
      fun t g => congrArg₂ (· + ·) (h.2.2.1 t g) (h'.2.2.1 t g), fun r h0 h1 _ _ ν 𝓕 hν h𝓕 g =>
        (integral_add (integrableOn_unip h.1 h.2.1 ν h𝓕 g) (integrableOn_unip h'.1 h'.2.1 ν h𝓕 g)).trans <| by
          rw [h.2.2.2 r h0 h1 ν 𝓕 hν h𝓕 g, h'.2.2.2 r h0 h1 ν 𝓕 hν h𝓕 g, add_zero]⟩
  smul_mem' := fun c φ h =>
    ⟨h.1.const_smul c, fun γ g => congrArg (c • ·) (h.2.1 γ g), fun t g => congrArg (c • ·) (h.2.2.1 t g),
      fun r h0 h1 _ _ ν 𝓕 hν h𝓕 g =>
        (integral_const_mul c _).trans (by rw [h.2.2.2 r h0 h1 ν 𝓕 hν h𝓕 g, mul_zero])⟩

theorem mem_cuspCont : φ ∈ cuspCont E a ↔ Continuous φ ∧ (∀ γ g, φ (ratGL E a γ * g) = φ g) ∧
    (∀ t g, φ (splitCentre E a t * g) = φ g) ∧ IsCuspidal φ := Iff.rfl

theorem leftInv_of_mem_cuspCont (h : φ ∈ cuspCont E a) : LeftInv (latticeGL E a) φ := leftInv_latticeGL h.2.1 h.2.2.1

theorem mul_right_mem_cuspCont (h : φ ∈ cuspCont E a) (k : GA E a) : (fun g => φ (g * k)) ∈ cuspCont E a :=
  ⟨h.1.comp (continuous_mul_const k), fun γ g => by simp only [mul_assoc, h.2.1],
    fun t g => by simp only [mul_assoc, h.2.2.1], fun r h0 h1 _ _ ν 𝓕 hν h𝓕 g => by
      simpa only [mul_assoc] using h.2.2.2 r h0 h1 ν 𝓕 hν h𝓕 (g * k)⟩

theorem mem_cuspCont_of_isCuspForm {φ : Sm E a} (h : IsCuspForm φ) (h' : ∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) :
    φ.1 ∈ cuspCont E a :=
  ⟨ContAut.continuous_of_isOpen_stab E a φ h.1.level, h.1.left, h', h.2⟩

theorem mem_cuspCont_of_le_one (ha : a ≤ 1) : φ ∈ cuspCont E a ↔ Continuous φ ∧ (∀ γ g, φ (ratGL E a γ * g) = φ g) ∧
    ∀ t g, φ (splitCentre E a t * g) = φ g :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.1⟩, fun h => ⟨h.1, h.2.1, h.2.2, fun r h0 h1 => by omega⟩⟩

theorem one_mem_cuspCont_iff : (fun _ => (1 : ℂ)) ∈ cuspCont E a ↔ a ≤ 1 :=
  ⟨fun h => not_lt.1 fun ha => GlobalTheory.ConstNotCusp.not_isCuspidal_oneFn E a ha h.2.2.2,
    fun ha => (mem_cuspCont_of_le_one ha).2 ⟨continuous_const, fun _ _ => rfl, fun _ _ => rfl⟩⟩

end Cusp

section L2

variable (μ : Measure (GA E a))

def fnClasses [μ.IsMulLeftInvariant] (S : Submodule ℂ (GA E a → ℂ)) : Submodule ℂ (L2 (latticeGL E a) μ) where
  carrier := {F | ∃ φ ∈ S, lift (latticeGL E a) F =ᵐ[μ] φ}
  zero_mem' := ⟨0, zero_mem _, ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)⟩
  add_mem' := fun {F F'} ⟨_, h, e⟩ ⟨_, h', e'⟩ =>
    ⟨_, add_mem h h', Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_add F F')) (e.add e')⟩
  smul_mem' := fun c F ⟨_, h, e⟩ =>
    ⟨_, Submodule.smul_mem _ c h, Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_smul c F)) (e.const_smul c)⟩

def cuspContinuousL2 [μ.IsMulLeftInvariant] : Submodule ℂ (L2 (latticeGL E a) μ) := fnClasses μ (cuspCont E a)

def L2cusp [μ.IsMulLeftInvariant] : Submodule ℂ (L2 (latticeGL E a) μ) := (cuspContinuousL2 μ).topologicalClosure

def classes (V : Submodule ℂ (Sm E a)) (μ : Measure (GA E a)) [μ.IsMulLeftInvariant] :
    Submodule ℂ (L2 (latticeGL E a) μ) where
  carrier := {F | ∃ φ ∈ V, lift (latticeGL E a) F =ᵐ[μ] φ.1}
  zero_mem' := ⟨0, zero_mem _, ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)⟩
  add_mem' := fun {F F'} ⟨_, h, e⟩ ⟨_, h', e'⟩ =>
    ⟨_, add_mem h h', Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_add F F')) (e.add e')⟩
  smul_mem' := fun c F ⟨_, h, e⟩ =>
    ⟨_, Submodule.smul_mem _ c h, Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_smul c F)) (e.const_smul c)⟩

variable {μ} {φ : GA E a → ℂ} {V : Submodule ℂ (Sm E a)} {F : L2 (latticeGL E a) μ}

section Left

variable [μ.IsMulLeftInvariant]

theorem mem_classes : F ∈ classes V μ ↔ ∃ φ ∈ V, lift (latticeGL E a) F =ᵐ[μ] φ.1 := Iff.rfl

theorem toL2_mem_classes {φ : Sm E a} (hφ : φ ∈ V) (h : MemL2Quotient (latticeGL E a) μ φ.1) : h.toL2 ∈ classes V μ :=
  ⟨φ, hφ, h.lift_toL2_ae_eq⟩

theorem memL2_of_ae_eq (hφ : LeftInv (latticeGL E a) φ) (e : lift (latticeGL E a) F =ᵐ[μ] φ) :
    MemL2Quotient (latticeGL E a) μ φ :=
  have hd := isFundamentalDomain_stdDom (latticeGL E a) μ
  (memL2_iff_fundamental_domain hd).2 ⟨hφ, ((memL2_iff_fundamental_domain hd).1 (memL2_lift F)).2.ae_eq (ae_restrict_of_ae e)⟩

theorem mem_L2cusp_of_ae_eq (hφ : φ ∈ cuspCont E a) (e : lift (latticeGL E a) F =ᵐ[μ] φ) : F ∈ L2cusp μ :=
  Submodule.le_topologicalClosure _ ⟨φ, hφ, e⟩

theorem toL2_mem_cuspidal (h : MemL2Quotient (latticeGL E a) μ φ) (hφ : φ ∈ cuspCont E a) : h.toL2 ∈ L2cusp μ :=
  mem_L2cusp_of_ae_eq hφ h.lift_toL2_ae_eq

theorem L2cusp_le {U : Submodule ℂ (L2 (latticeGL E a) μ)} (hU : IsClosed (U : Set (L2 (latticeGL E a) μ)))
    (h : ∀ φ ∈ cuspCont E a, ∀ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ U) : L2cusp μ ≤ U := by
  refine Submodule.topologicalClosure_minimal _ ?_ hU
  rintro F ⟨φ, hφ, e⟩
  have h2 := memL2_of_ae_eq (leftInv_of_mem_cuspCont hφ) e
  exact l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (h2.lift_toL2_ae_eq.trans e.symm) ▸ h φ hφ h2

theorem closure_classes_le_L2cusp (h : ∀ φ ∈ V, IsCuspForm φ)
    (h' : ∀ φ ∈ V, ∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) : (classes V μ).topologicalClosure ≤ L2cusp μ :=
  Submodule.topologicalClosure_mono fun _ ⟨φ, hφ, e⟩ => ⟨_, mem_cuspCont_of_isCuspForm (h φ hφ) (h' φ hφ), e⟩

theorem classes_le_L2cusp (h : ∀ φ ∈ V, IsCuspForm φ)
    (h' : ∀ φ ∈ V, ∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) : classes V μ ≤ L2cusp μ :=
  (Submodule.le_topologicalClosure _).trans (closure_classes_le_L2cusp h h')

variable (μ) in

theorem isClosed_L2cusp : IsClosed (L2cusp μ : Set (L2 (latticeGL E a) μ)) := Submodule.isClosed_topologicalClosure _

variable (μ) in

instance completeSpace_L2cusp : CompleteSpace (L2cusp μ) := (isClosed_L2cusp μ).completeSpace_coe

end Left

section Haar

variable [μ.IsHaarMeasure]

theorem memL2_iff_isSqInt (hc : Continuous φ) (h : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (h' : ∀ t g, φ (splitCentre E a t * g) = φ g) : MemL2Quotient (latticeGL E a) μ φ ↔ IsSqInt φ := by
  have hl := leftInv_latticeGL h h'
  have key : ∀ (ν : Measure (GA E a)) (𝓕 : Set (GA E a)),
      MemLp φ 2 (ν.restrict 𝓕) ↔ ∫⁻ g in 𝓕, ‖φ g‖ₑ ^ 2 ∂ν < ⊤ := fun ν 𝓕 => by
    rw [MemLp, and_iff_right hc.aestronglyMeasurable,
      eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    simp
  have hd := isFundamentalDomain_stdDom (latticeGL E a) μ
  refine ⟨fun hm => ⟨h', μ, _, inferInstance, hd, (key _ _).1 ((memL2_iff_fundamental_domain hd).1 hm).2⟩, ?_⟩
  rintro ⟨-, ν, 𝓕, hν, h𝓕, hi⟩
  refine (memL2_iff_fundamental_domain (h𝓕.mono (Measure.absolutelyContinuous_isHaarMeasure μ ν))).2 ⟨hl, (key _ _).2 ?_⟩
  rw [Measure.isMulLeftInvariant_eq_smul μ ν, Measure.restrict_smul, lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hi

theorem memL2_of_isAutForm {φ : Sm E a} (h : IsAutForm φ) (h' : IsSqInt φ.1) : MemL2Quotient (latticeGL E a) μ φ.1 :=
  (memL2_iff_isSqInt (ContAut.continuous_of_isOpen_stab E a φ h.level) h.left h'.1).2 h'

theorem toL2_ne_zero (h : MemL2Quotient (latticeGL E a) μ φ) (hc : Continuous φ) (h0 : φ ≠ 0) : h.toL2 ≠ 0 := fun e =>
  h0 ((Continuous.ae_eq_iff_eq μ hc continuous_zero).1
    (h.lift_toL2_ae_eq.symm.trans (e ▸ ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _))))

variable (μ V) in

def toL2ₗ (h : ∀ φ ∈ V, MemL2Quotient (latticeGL E a) μ φ.1) : V →ₗ[ℂ] L2 (latticeGL E a) μ where
  toFun φ := (h φ φ.2).toL2
  map_add' φ ψ := MemLp.toLp_add (h φ φ.2).2 (h ψ ψ.2).2
  map_smul' c φ := MemLp.toLp_const_smul c (h φ φ.2).2

theorem lift_toL2ₗ (h : ∀ φ ∈ V, MemL2Quotient (latticeGL E a) μ φ.1) (φ : V) :
    lift (latticeGL E a) (toL2ₗ μ V h φ) =ᵐ[μ] φ.1.1 := (h φ φ.2).lift_toL2_ae_eq

theorem range_toL2ₗ (h : ∀ φ ∈ V, MemL2Quotient (latticeGL E a) μ φ.1) : LinearMap.range (toL2ₗ μ V h) = classes V μ :=
  Submodule.ext fun _ => ⟨fun ⟨φ, e⟩ => e ▸ toL2_mem_classes φ.2 (h φ φ.2),
    fun ⟨φ, hφ, e⟩ => ⟨⟨φ, hφ⟩, l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ((h φ hφ).lift_toL2_ae_eq.trans e.symm)⟩⟩

theorem toL2ₗ_injective (h : ∀ φ ∈ V, MemL2Quotient (latticeGL E a) μ φ.1) (hc : ∀ φ ∈ V, Continuous φ.1) :
    Function.Injective (toL2ₗ μ V h) :=
  (injective_iff_map_eq_zero _).2 fun φ e => Subtype.ext <| Subtype.ext <| by
    by_contra h0
    exact toL2_ne_zero (h φ φ.2) (hc φ φ.2) h0 e

variable [μ.IsMulRightInvariant]

variable (μ) in

theorem isSubrep_L2cusp : IsSubrep (R (latticeGL E a) μ) (L2cusp μ) :=
  isSubrep_topologicalClosure fun g F ⟨_, h, e⟩ => ⟨_, mul_right_mem_cuspCont h g,
    (lift_R g F).trans ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae e)⟩

variable (μ) in

abbrev Rcusp : GA E a →* (L2cusp μ →L[ℂ] L2cusp μ) := (isSubrep_L2cusp μ).rep

variable (μ) in

theorem isUnitaryRep_Rcusp : IsUnitaryRep (Rcusp μ) :=
  (isSubrep_L2cusp μ).isUnitaryRep (isUnitaryRep_R (latticeGL E a) μ)

theorem R_splitCentre (t : ℝ) (hF : F ∈ L2cusp μ) : R (latticeGL E a) μ (splitCentre E a t) F = F := by
  have := L2cusp_le (μ := μ) (ContinuousLinearMap.isClosed_ker (R (latticeGL E a) μ (splitCentre E a t) - 1))
    (fun φ hφ h => by
      refine sub_eq_zero.2 ((right_translate_toL2 h _).trans ?_)
      exact ((h.mul_right _).toL2_eq_iff_ae_eq h).2 (.of_forall fun g => by
        beta_reduce; rw [← splitCentre_comm, hφ.2.2.1])) hF
  exact sub_eq_zero.1 this

theorem Rcusp_splitCentre (t : ℝ) : Rcusp μ (splitCentre E a t) = 1 :=
  ContinuousLinearMap.ext fun F => Subtype.ext (R_splitCentre t F.2)

theorem R_mem_classes {g : GA E a} (hg : ∀ φ ∈ V, rt E a g φ ∈ V) (hF : F ∈ classes V μ) :
    R (latticeGL E a) μ g F ∈ classes V μ :=
  let ⟨φ, h, e⟩ := hF
  ⟨_, hg φ h, (lift_R g F).trans ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae e)⟩

theorem R_toL2ₗ (h : ∀ φ ∈ V, MemL2Quotient (latticeGL E a) μ φ.1) {g : GA E a} (φ : V) (hg : rt E a g φ.1 ∈ V) :
    R (latticeGL E a) μ g (toL2ₗ μ V h φ) = toL2ₗ μ V h ⟨_, hg⟩ := right_translate_toL2 (h φ φ.2) g

end Haar

end L2

section RankOne

omit [IsTotallyComplex E] in

theorem mul_comm_one (g h : GA E 1) : g * h = h * g := by
  rw [← toGL_det E (g * h), ← toGL_det E (h * g), map_mul GeneralLinearGroup.det, map_mul GeneralLinearGroup.det, mul_comm (GeneralLinearGroup.det g)]

variable {μ : Measure (GA E 1)} [μ.IsHaarMeasure]

theorem memL2_of_rank_one {φ : GA E 1 → ℂ} (hc : Continuous φ) (h : LeftInv (latticeGL E 1) φ) : MemL2Quotient (latticeGL E 1) μ φ := by
  have hd := isFundamentalDomain_stdDom (latticeGL E 1) μ
  obtain ⟨K, hK, hcov⟩ := exists_compact_latticeGL E
  refine (memL2_iff_fundamental_domain hd).2 ⟨h, (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 ?_⟩
  simpa only [← _root_.norm_pow] using (GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ _ K hK hcov μ inferInstance _ hd
    (fun g => φ g ^ 2) (hc.pow 2) fun γ hγ g => by rw [h γ hγ]).norm

variable (μ) in

theorem exists_one_mem_L2cusp : ∃ F ∈ L2cusp μ, F ≠ 0 ∧ lift (latticeGL E 1) F =ᵐ[μ] fun _ => 1 :=
  have h : MemL2Quotient (latticeGL E 1) μ fun _ => 1 := memL2_of_rank_one continuous_const fun _ _ _ => rfl
  ⟨h.toL2, toL2_mem_cuspidal h (one_mem_cuspCont_iff.2 le_rfl),
    toL2_ne_zero h continuous_const fun e => one_ne_zero (congrFun e 1), h.lift_toL2_ae_eq⟩

end RankOne

example (μ : Measure (GA E 1)) [μ.IsHaarMeasure] :
    classes (CuspSub.triv E le_rfl).V μ ≠ ⊥ ∧ classes (CuspSub.triv E le_rfl).V μ ≤ L2cusp μ := by
  obtain ⟨F, -, h0, e⟩ := exists_one_mem_L2cusp μ
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨F, ⟨oneFn E 1, Submodule.mem_span_singleton_self _, e⟩, h0⟩,
    classes_le_L2cusp (CuspSub.triv E le_rfl).cusp fun φ hφ t g => ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
  rfl

example : (fun _ => (1 : ℂ)) ∉ cuspCont E 2 := fun h => absurd (one_mem_cuspCont_iff.1 h) (by norm_num)

example (γ : GL (Fin 1) E) : ratGL E 1 γ ≠ splitCentre E 1 1 := fun e => by
  have h := congrArg (fun g => ideleNorm (E := E) (GeneralLinearGroup.det g)) e
  simp only [det_ratGL, det_splitCentre] at h
  exact (one_lt_ideleNorm_eIdele E).ne ((ideleNorm_principalIdele _).symm.trans h)

end GlobalTheory.CuspRep.CuspidalL2GL

end
