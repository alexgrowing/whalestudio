import Mathlib
import GroundTheory.AutomorphicForms.DixmierMalliavinBasic

namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set Filter

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

noncomputable def prodExpVal {d : ℕ} (X : Fin d → 𝔸) (t : Fin d → ℝ) : 𝔸 :=
  (List.ofFn fun i => exp (t i • X i)).prod

theorem prodExpVal_succ {d : ℕ} (X : Fin (d + 1) → 𝔸) (t : Fin (d + 1) → ℝ) :
    prodExpVal X t = exp (t 0 • X 0) * prodExpVal (fun i => X i.succ) (fun i => t i.succ) := by
  simp [prodExpVal, List.ofFn_succ]

theorem prodExpVal_zero {d : ℕ} (X : Fin d → 𝔸) : prodExpVal X 0 = 1 := by
  simp [prodExpVal]

theorem prodExpVal_zero' {d : ℕ} (X : Fin d → 𝔸) : prodExpVal X (fun _ => 0) = 1 :=
  prodExpVal_zero X

theorem contDiff_prodExpVal {d : ℕ} (X : Fin d → 𝔸) : ContDiff ℝ ∞ (prodExpVal X) := by
  induction d with
  | zero =>
    have e : prodExpVal X = fun _ => 1 := funext fun t => by simp [prodExpVal]
    rw [e]; exact contDiff_const
  | succ d ih =>
    have e : prodExpVal X = fun t => exp (t 0 • X 0) *
        prodExpVal (fun i => X i.succ) (fun i => t i.succ) := funext (prodExpVal_succ X)
    rw [e]
    exact ((contDiff_exp ℝ 𝔸).comp ((contDiff_apply ℝ ℝ 0).smul contDiff_const)).mul
      ((ih _).comp (contDiff_pi.2 fun i => contDiff_apply ℝ ℝ i.succ))

theorem hasFDerivAt_prodExpVal_zero {d : ℕ} (X : Fin d → 𝔸) :
    HasFDerivAt (prodExpVal X)
      (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (X i)) 0 := by
  induction d with
  | zero =>
    have e : prodExpVal X = fun _ => 1 := funext fun t => by simp [prodExpVal]
    rw [e]
    refine (hasFDerivAt_const (1 : 𝔸) (0 : Fin 0 → ℝ)).congr_fderiv ?_
    ext t; simp
  | succ d ih =>
    have e : prodExpVal X = fun t => exp (t 0 • X 0) *
        prodExpVal (fun i => X i.succ) (fun i => t i.succ) := funext (prodExpVal_succ X)
    rw [e]
    have hA : HasFDerivAt (fun t : Fin (d + 1) → ℝ => exp (t 0 • X 0))
        ((ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (X 0)) 0 := by
      have hL : HasFDerivAt (fun t : Fin (d + 1) → ℝ => t 0 • X 0)
          ((ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (X 0)) 0 :=
        ((ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (X 0)).hasFDerivAt
      have hE : HasFDerivAt (exp : 𝔸 → 𝔸) (1 : 𝔸 →L[ℝ] 𝔸) ((0 : Fin (d + 1) → ℝ) 0 • X 0) := by
        have : (0 : Fin (d + 1) → ℝ) 0 • X 0 = 0 := by simp
        rw [this]; exact hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)
      exact (hE.comp (0 : Fin (d + 1) → ℝ) hL).congr_fderiv (by ext t; simp)
    let T : (Fin (d + 1) → ℝ) →L[ℝ] (Fin d → ℝ) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ
    have hB : HasFDerivAt (fun t : Fin (d + 1) → ℝ =>
        prodExpVal (fun i => X i.succ) (fun i => t i.succ))
        ((∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (X i.succ)).comp T)
        0 := by
      have h0 : T 0 = 0 := map_zero T
      have := (ih (fun i => X i.succ))
      rw [← h0] at this
      exact this.comp (0 : Fin (d + 1) → ℝ) (T.hasFDerivAt)
    refine (hA.mul' hB).congr_fderiv ?_
    ext t
    simp [T, Fin.sum_univ_succ, prodExpVal_zero']
    rw [add_comm]

theorem hasFDerivAt_expSymm_one :
    HasFDerivAt (expPartialHomeomorph ℝ 𝔸).symm (1 : 𝔸 →L[ℝ] 𝔸) 1 := by
  have hd : HasFDerivAt (expPartialHomeomorph ℝ 𝔸)
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸)
      ((expPartialHomeomorph ℝ 𝔸).symm 1) := by
    rw [expPartialHomeomorph_symm_one, coe_expPartialHomeomorph]
    exact (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)).congr_fderiv (by ext; simp)
  exact ((expPartialHomeomorph ℝ 𝔸).hasFDerivAt_symm
    (one_mem_expPartialHomeomorph_target ℝ 𝔸) hd).congr_fderiv (by ext; simp)

variable {𝔤 : Submodule ℝ 𝔸}

noncomputable def logCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (w : 𝔸) : Fin d → ℝ :=
  b.equivFun.toContinuousLinearEquiv (subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm w))

theorem contDiffOn_logCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ContDiffOn ℝ ∞ (logCoord b) (expPartialHomeomorph ℝ 𝔸).target :=
  (b.equivFun.toContinuousLinearEquiv.contDiff.comp (subspaceProj 𝔤).contDiff).comp_contDiffOn
    (contDiffOn_expPartialHomeomorph_symm ℝ 𝔸)

theorem logCoord_one {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) : logCoord b (1 : 𝔸) = 0 := by
  simp [logCoord, expPartialHomeomorph_symm_one]

theorem logCoord_coe_sum {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (t : Fin d → ℝ) :
    b.equivFun.toContinuousLinearEquiv (subspaceProj 𝔤 (∑ i, t i • (b i : 𝔸))) = t := by
  have : (∑ i, t i • (b i : 𝔸)) = ((b.equivFun.symm t : 𝔤) : 𝔸) := by
    rw [Module.Basis.equivFun_symm_apply]; simp
  rw [this, subspaceProj_coe]
  exact b.equivFun.apply_symm_apply t

noncomputable def prodExpCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (t : Fin d → ℝ) :
    Fin d → ℝ :=
  logCoord b (prodExpVal (fun i => (b i : 𝔸)) t)

theorem prodExpCoord_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) : prodExpCoord b 0 = 0 := by
  simp [prodExpCoord, prodExpVal_zero, logCoord_one]

theorem contDiffOn_prodExpCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ContDiffOn ℝ ∞ (prodExpCoord b)
      {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph ℝ 𝔸).target} :=
  (contDiffOn_logCoord b).comp (contDiff_prodExpVal _).contDiffOn (fun _ ht => ht)

theorem isOpen_prodExpCoord_domain {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    IsOpen {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph ℝ 𝔸).target} :=
  (expPartialHomeomorph ℝ 𝔸).open_target.preimage (contDiff_prodExpVal _).continuous

theorem hasFDerivAt_prodExpCoord_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    HasFDerivAt (prodExpCoord b)
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) :
        (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) 0 := by
  have hL : HasFDerivAt (fun w : 𝔸 => b.equivFun.toContinuousLinearEquiv
      (subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm w)))
      (((b.equivFun.toContinuousLinearEquiv : 𝔤 →L[ℝ] (Fin d → ℝ)).comp (subspaceProj 𝔤)).comp
        (1 : 𝔸 →L[ℝ] 𝔸)) (prodExpVal (fun i => (b i : 𝔸)) 0) := by
    rw [prodExpVal_zero]
    exact (((b.equivFun.toContinuousLinearEquiv : 𝔤 →L[ℝ] (Fin d → ℝ)).comp
      (subspaceProj 𝔤)).hasFDerivAt).comp (1 : 𝔸) hasFDerivAt_expSymm_one
  refine (hL.comp (0 : Fin d → ℝ) (hasFDerivAt_prodExpVal_zero _)).congr_fderiv ?_
  ext t : 1
  simpa using logCoord_coe_sum b t

theorem contDiffAt_prodExpCoord_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ContDiffAt ℝ ∞ (prodExpCoord b) 0 :=
  (contDiffOn_prodExpCoord b).contDiffAt ((isOpen_prodExpCoord_domain b).mem_nhds
    (by simp [prodExpVal_zero, one_mem_expPartialHomeomorph_target]))

namespace IsExpLieAlgebra

variable {G : Subgroup 𝔸ˣ} (h : IsExpLieAlgebra G 𝔤)

theorem exists_prodExp_coord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ (S T : Set (Fin d → ℝ)) (ψ : (Fin d → ℝ) → (Fin d → ℝ)), IsOpen S ∧ IsOpen T ∧
      (0 : Fin d → ℝ) ∈ S ∧ MapsTo (prodExpCoord b) S T ∧ MapsTo ψ T S ∧
      (∀ z ∈ S, ψ (prodExpCoord b z) = z) ∧ (∀ w ∈ T, prodExpCoord b (ψ w) = w) ∧
      ContDiffOn ℝ ∞ ψ T ∧ (∀ z ∈ S, prodExpVal (fun i => (b i : 𝔸)) z ∈ h.nhdOne) := by
  set Φ := prodExpCoord b with hΦdef
  set U := {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph ℝ 𝔸).target} with hUdef
  have hU : IsOpen U := isOpen_prodExpCoord_domain b
  have hΦU : ContDiffOn ℝ ∞ Φ U := contDiffOn_prodExpCoord b
  let F₀ := (contDiffAt_prodExpCoord_zero b).toOpenPartialHomeomorph Φ
    (hasFDerivAt_prodExpCoord_zero b) (by simp)
  have hcont : ContinuousOn (fderiv ℝ Φ) U := hΦU.continuousOn_fderiv_of_isOpen hU (by simp)
  have hS₁ : IsOpen (U ∩ fderiv ℝ Φ ⁻¹' {u | IsUnit u}) :=
    hcont.isOpen_inter_preimage hU Units.isOpen
  have hN : IsOpen {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ h.nhdOne} :=
    h.isOpen_nhdOne.preimage (contDiff_prodExpVal _).continuous
  set S₂ := (U ∩ fderiv ℝ Φ ⁻¹' {u | IsUnit u}) ∩
    {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ h.nhdOne} with hS₂def
  have hS₂ : IsOpen S₂ := hS₁.inter hN
  let F := F₀.restrOpen S₂ hS₂
  have hF : (F : (Fin d → ℝ) → (Fin d → ℝ)) = Φ := rfl
  refine ⟨F.source, F.target, F.symm, F.open_source, F.open_target, ?_, ?_, F.mapsTo_symm,
    fun z hz => F.left_inv hz, fun w hw => F.right_inv hw, ?_, ?_⟩
  · refine ⟨(contDiffAt_prodExpCoord_zero b).mem_toOpenPartialHomeomorph_source _ _, ?_⟩
    have h0 : prodExpVal (fun i => (b i : 𝔸)) 0 = 1 := prodExpVal_zero _
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show prodExpVal (fun i => (b i : 𝔸)) 0 ∈ (expPartialHomeomorph ℝ 𝔸).target
      rw [h0]; exact one_mem_expPartialHomeomorph_target ℝ 𝔸
    · show IsUnit (fderiv ℝ Φ 0)
      rw [(hasFDerivAt_prodExpCoord_zero b).fderiv]
      exact isUnit_one
    · show prodExpVal (fun i => (b i : 𝔸)) 0 ∈ h.nhdOne
      rw [h0]; exact h.one_mem_nhdOne
  · intro z hz; rw [← hF]; exact F.map_source hz
  · intro w hw
    apply ContDiffAt.contDiffWithinAt
    have hz : F.symm w ∈ F.source := F.map_target hw
    have hzS : F.symm w ∈ S₂ := hz.2
    have hu : IsUnit (fderiv ℝ Φ (F.symm w)) := hzS.1.2
    have hΦz : ContDiffAt ℝ ∞ Φ (F.symm w) := hΦU.contDiffAt (hU.mem_nhds hzS.1.1)
    have hdiff : HasFDerivAt Φ (fderiv ℝ Φ (F.symm w)) (F.symm w) :=
      (hΦz.differentiableAt (by simp)).hasFDerivAt
    have key : ((ContinuousLinearEquiv.unitsEquiv ℝ (Fin d → ℝ) hu.unit :
        (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) =
        fderiv ℝ Φ (F.symm w) := by
      ext x; simp
    exact F.contDiffAt_symm hw (key ▸ hdiff) hΦz
  · intro z hz; exact hz.2.2

theorem isEmbedding_coe_coe :
    Topology.IsEmbedding (fun x : G => ((x : 𝔸ˣ) : 𝔸)) :=
  Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal

include h in

theorem secondCountableTopology : SecondCountableTopology G :=
  isEmbedding_coe_coe.secondCountableTopology

theorem val_prodExp {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) :
    (((h.prodExp X t : G) : 𝔸ˣ) : 𝔸) = prodExpVal (fun i => (X i : 𝔸)) t := by
  let f : G →* 𝔸 := (Units.coeHom 𝔸).comp G.subtype
  show f (List.ofFn fun i => h.expG (t i • X i)).prod = _
  rw [map_list_prod, List.map_ofFn]
  simp [prodExpVal, f, Function.comp_def]

theorem continuous_prodExp {d : ℕ} (X : Fin d → 𝔤) : Continuous (h.prodExp X) := by
  rw [isEmbedding_coe_coe.continuous_iff]
  have : (fun x : G => ((x : 𝔸ˣ) : 𝔸)) ∘ h.prodExp X = prodExpVal (fun i => (X i : 𝔸)) :=
    funext fun t => h.val_prodExp X t
  rw [this]; exact (contDiff_prodExpVal _).continuous

theorem prodExp_coord_eq {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) {T : Set (Fin d → ℝ)}
    {ψ : (Fin d → ℝ) → (Fin d → ℝ)} (hψT : ∀ w ∈ T, prodExpCoord b (ψ w) = w)
    (hN : ∀ w ∈ T, prodExpVal (fun i => (b i : 𝔸)) (ψ w) ∈ h.nhdOne) {y : G}
    (hy : ((y : 𝔸ˣ) : 𝔸) ∈ h.nhdOne) (hyT : logCoord b ((y : 𝔸ˣ) : 𝔸) ∈ T) :
    h.prodExp (⇑b) (ψ (logCoord b ((y : 𝔸ˣ) : 𝔸))) = y := by
  set w := logCoord b ((y : 𝔸ˣ) : 𝔸)
  set z := ψ w
  have hz : logCoord b (prodExpVal (fun i => (b i : 𝔸)) z) = w := hψT w hyT
  have hPz : (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸) = prodExpVal (fun i => (b i : 𝔸)) z :=
    h.val_prodExp _ z
  have hzN : (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸) ∈ h.nhdOne := hPz ▸ hN w hyT
  have h1 := h.symm_mem_lie hzN
  have h2 := h.symm_mem_lie hy
  have e1 : subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm
      (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸)) =
      subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm ((y : 𝔸ˣ) : 𝔸)) := by
    apply b.equivFun.toContinuousLinearEquiv.injective
    rw [hPz]; exact hz
  have e2 := congrArg Subtype.val e1
  rw [subspaceProj_of_mem h1, subspaceProj_of_mem h2] at e2
  have e3 := congrArg exp e2
  rw [h.exp_symm hzN, h.exp_symm hy] at e3
  exact Subtype.ext (Units.ext e3)

end IsExpLieAlgebra

theorem contDiff_det_pi {d : ℕ} :
    ContDiff ℝ ∞ (fun f : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => f.det) := by
  have e : (fun f : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => f.det) = fun f =>
      ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, f (Pi.single i 1) (σ i) := by
    funext f
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    congr 1
  rw [e]
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  refine contDiff_prod fun i _ => ?_
  exact ((ContinuousLinearMap.proj (σ i) : (Fin d → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.apply ℝ (Fin d → ℝ) (Pi.single i (1 : ℝ) : Fin d → ℝ) :
      ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) →L[ℝ] (Fin d → ℝ))).contDiff

theorem contDiff_smul_of_tsupport {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {O : Set V} (hO : IsOpen O) {f : V → F}
    {g : V → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiff ℝ ∞ g) (hgO : tsupport g ⊆ O) :
    ContDiff ℝ ∞ (fun x => g x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ O
  · exact hg.contDiffAt.smul (hf.contDiffAt (hO.mem_nhds hx))
  · have hx' : x ∉ tsupport g := fun h' => hx (hgO h')
    have : (fun x => g x • f x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq this

open MeasureTheory in

theorem contDiff_integral_comp_of_hasCompactSupport {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X] (ν : Measure X)
    [IsFiniteMeasure ν] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {u : X → V}
    (hu : Continuous u) (n : ℕ) :
    ∀ {W F : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup F]
      [NormedSpace ℝ F] [CompleteSpace F] (Ξ : V × W → F), ContDiff ℝ ∞ Ξ → HasCompactSupport Ξ →
      ContDiff ℝ n (fun z => ∫ x, Ξ (u x, z) ∂ν) := by
  induction n with
  | zero =>
    intro W F _ _ _ _ _ Ξ hΞ hc
    obtain ⟨C, hC⟩ := hΞ.continuous.bounded_above_of_compact_support hc
    rw [Nat.cast_zero, contDiff_zero]
    refine continuous_of_dominated (bound := fun _ => C) (fun z => ?_) (fun z => ?_)
      (integrable_const C) (Eventually.of_forall fun a => ?_)
    · exact (hΞ.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable
    · exact Eventually.of_forall fun a => hC _
    · exact hΞ.continuous.comp (continuous_const.prodMk continuous_id)
  | succ n ih =>
    intro W F _ _ _ _ _ Ξ hΞ hc
    set Ξ' : V × W → (W →L[ℝ] F) := fun q => (fderiv ℝ Ξ q).comp (ContinuousLinearMap.inr ℝ V W)
      with hΞ'def
    have hΞ'c : ContDiff ℝ ∞ Ξ' :=
      ContDiff.clm_comp (𝕜 := ℝ) (g := fun q => fderiv ℝ Ξ q)
        (f := fun _ => ContinuousLinearMap.inr ℝ V W)
        (hΞ.fderiv_right (m := ∞) (by simp)) contDiff_const
    have hΞ's : HasCompactSupport Ξ' :=
      (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : V × W →L[ℝ] F => L.comp (ContinuousLinearMap.inr ℝ V W))
        (ContinuousLinearMap.zero_comp _)
    obtain ⟨C, hC⟩ := hΞ'c.continuous.bounded_above_of_compact_support hΞ's
    obtain ⟨C₀, hC₀⟩ := hΞ.continuous.bounded_above_of_compact_support hc
    have hdiff : ∀ (v : V) (z : W), HasFDerivAt (fun z => Ξ (v, z)) (Ξ' (v, z)) z := by
      intro v z
      have h1 : HasFDerivAt Ξ (fderiv ℝ Ξ (v, z)) (v, z) :=
        ((hΞ.differentiable (by simp)) (v, z)).hasFDerivAt
      exact h1.comp z ((hasFDerivAt_const v z).prodMk (hasFDerivAt_id z))
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun z => ∫ x, Ξ' (u x, z) ∂ν, ih Ξ' hΞ'c hΞ's, fun z₀ => ?_⟩
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := fun _ => C)
      (F := fun z a => Ξ (u a, z)) (F' := fun z a => Ξ' (u a, z))
      univ_mem (Eventually.of_forall fun z => ?_) ?_ ?_ ?_ (integrable_const C) ?_
    · exact (hΞ.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable
    · exact Integrable.of_bound
        (hΞ.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable C₀
        (Eventually.of_forall fun a => hC₀ _)
    · exact (hΞ'c.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable
    · exact Eventually.of_forall fun a z _ => hC _
    · exact Eventually.of_forall fun a z _ => hdiff (u a) z

end GroundTheory.Automorphic
