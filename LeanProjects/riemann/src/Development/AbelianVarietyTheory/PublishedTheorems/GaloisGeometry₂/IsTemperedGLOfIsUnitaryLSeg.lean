import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

noncomputable section

open NumberField IsDedekindDomain Topology Matrix GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.GKCoh

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

variable (E a) in

def regFun : Subalgebra ℂ (GL (Fin a) (Cinf E) → ℂ) :=
  Algebra.adjoin ℂ ({f | ∃ τ i j, f = fun y => coord τ (y.val i j)} ∪ {f | ∃ τ, f = fun y => (coord τ y.val.det)⁻¹})

variable (E a) in

structure AlgRep where

  d : ℕ

  mat : GL (Fin a) (Cinf E) →* Matrix (Fin d) (Fin d) ℂ
  reg : ∀ i j, (fun y => mat y i j) ∈ regFun E a
  pos : 0 < d
  irred : ∀ W : Submodule ℂ (Fin d → ℂ), (∀ y, ∀ v ∈ W, mat y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

open Classical in

def extGL (f : GL (Fin a) (Cinf E) → ℂ) (x : Lie E a) : ℂ := if h : IsUnit (Matrix.of x) then f h.unit else 0

omit [NumberField E] in

theorem extGL_val (f : GL (Fin a) (Cinf E) → ℂ) (y : GL (Fin a) (Cinf E)) : extGL f (toL y.val) = f y := by
  have h : IsUnit (Matrix.of (toL y.val)) := y.isUnit
  have e : h.unit = y := Units.ext h.unit_spec
  rw [extGL, dif_pos h, e]

theorem extGL_eventuallyEq {f : GL (Fin a) (Cinf E) → ℂ} {F : Lie E a → ℂ} (h : ∀ y, f y = F (toL y.val))
    {x : Lie E a} (hx : x ∈ invSet E a) : extGL f =ᶠ[𝓝 x] F :=
  Filter.eventually_of_mem (isOpen_invSet.mem_nhds hx) fun z hz => by
    obtain ⟨u, hu⟩ := hz
    have e : z = toL u.val := hu.symm
    rw [e, extGL_val, h]

def coordL (τ : E →+* ℂ) : Cinf E →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := coord τ
      map_add' := map_add _
      map_smul' := fun c z => by unfold coord; split_ifs <;> simp }

@[simp] theorem coordL_apply (τ : E →+* ℂ) (z : Cinf E) : coordL τ z = coord τ z := rfl

theorem differentiableAt_extGL {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    DifferentiableAt ℝ (extGL f) x := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    rcases hf with ⟨τ, i, j, rfl⟩ | ⟨τ, rfl⟩
    · refine DifferentiableAt.congr_of_eventuallyEq (f := fun x => coordL τ (x i j)) (by fun_prop)
        (extGL_eventuallyEq (by exact fun _ => rfl) hx)
    · refine DifferentiableAt.congr_of_eventuallyEq (f := fun x => (coordL τ (Matrix.of x).det)⁻¹) ?_
        (extGL_eventuallyEq (by exact fun _ => rfl) hx)
      exact ((coordL τ).differentiableAt.comp x (contDiff_det.differentiable (by simp) x)).inv
        (((Matrix.isUnit_iff_isUnit_det _).1 hx).map (coord τ)).ne_zero
  | algebraMap c =>
    exact (differentiableAt_const c).congr_of_eventuallyEq (extGL_eventuallyEq (by exact fun _ => rfl) hx)
  | add f g _ _ h1 h2 =>
    exact (h1.add h2).congr_of_eventuallyEq (extGL_eventuallyEq (fun y => by simp [extGL_val]) hx)
  | mul f g _ _ h1 h2 =>
    exact (h1.mul h2).congr_of_eventuallyEq (extGL_eventuallyEq (fun y => by simp [extGL_val]) hx)

namespace AlgRep

def dmat (Ξ : AlgRep E a) : Lie E a →ₗ[ℝ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ where
  toFun X := Matrix.of fun i j => fderiv ℝ (extGL fun y => Ξ.mat y i j) (oneL E a) X
  map_add' X Y := by ext i j; simp
  map_smul' c X := by ext i j; simp

theorem hasDerivAt_curve (Ξ : AlgRep E a) (c : ℝ → GL (Fin a) (Cinf E)) (X : Lie E a) (h0 : c 0 = 1)
    (hc : HasDerivAt (fun t => toL (c t).val) X 0) (i j : Fin Ξ.d) :
    HasDerivAt (fun t => Ξ.mat (c t) i j) (Ξ.dmat X i j) 0 := by
  have h : HasFDerivAt (extGL fun y => Ξ.mat y i j) (fderiv ℝ (extGL fun y => Ξ.mat y i j) (oneL E a)) (toL (c 0).val) := by
    rw [h0]; exact (differentiableAt_extGL (Ξ.reg i j) isUnit_one).hasFDerivAt
  have h2 := h.comp_hasDerivAt (0 : ℝ) hc
  simp only [Function.comp_def, extGL_val] at h2
  exact h2

theorem mat_mul_dmat (Ξ : AlgRep E a) (y : GL (Fin a) (Cinf E)) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    Ξ.mat y * Ξ.dmat (toL X) = Ξ.dmat (toL (y.val * X * (y⁻¹).val)) * Ξ.mat y := by
  classical
  let T : Lie E a →L[ℝ] Lie E a := (rmul (toL (y⁻¹).val)).comp (lmul (toL y.val))
  have hT : T (oneL E a) = oneL E a := (congrArg (· * (y⁻¹).val) (mul_one y.val)).trans y.mul_inv
  have hd := fun i j => (differentiableAt_extGL (Ξ.reg i j) (x := oneL E a) isUnit_one).hasFDerivAt
  ext i j
  have h1 := HasFDerivAt.fun_sum (u := Finset.univ) fun l _ => (hd l j).const_mul (Ξ.mat y i l)
  have h2 := HasFDerivAt.fun_sum (u := Finset.univ) fun l _ =>
    (HasFDerivAt.comp (oneL E a) (hT.symm ▸ hd i l) T.hasFDerivAt).mul_const (Ξ.mat y l j)
  have h3 := h1.unique (h2.congr_of_eventuallyEq (Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one)
    fun z hz => by
      obtain ⟨u, hu⟩ := hz
      have e : z = toL u.val := hu.symm
      have e2 : T (toL u.val) = toL (y * u * y⁻¹).val := rfl
      simp only [e, Function.comp_apply, e2, extGL_val]
      rw [← Matrix.mul_apply, ← Matrix.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]))
  have h4 := congrArg (fun D : Lie E a →L[ℝ] ℂ => D (toL X)) h3
  simp only [_root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    hT] at h4
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact h4.trans (Finset.sum_congr rfl fun l _ => mul_comm _ _)

variable (E a) in

def triv : AlgRep E a where
  d := 1
  mat := 1
  reg i j := Subalgebra.algebraMap_mem _ ((1 : Matrix (Fin 1) (Fin 1) ℂ) i j)
  pos := one_pos
  irred W _ := by
    have : IsSimpleModule ℂ (Fin 1 → ℂ) := isSimpleModule_iff_finrank_eq_one.2 (by simp)
    exact eq_bot_or_eq_top W

theorem dmat_triv (X : Lie E a) : (triv E a).dmat X = 0 := by
  ext i j
  have h := extGL_eventuallyEq (f := fun y => (triv E a).mat y i j) (F := fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ) i j)
    (fun _ => rfl) (x := oneL E a) isUnit_one
  change fderiv ℝ _ _ X = 0
  rw [h.fderiv_eq]
  simp

omit [NumberField E] in

theorem exists_section (τ : E →+* ℂ) : ∃ s : ℂ →+* Cinf E, ∀ z, coord τ (s z) = z := by
  unfold coord
  split_ifs
  · exact ⟨Pi.constRingHom _ _, fun _ => rfl⟩
  · exact ⟨(Pi.constRingHom _ _).comp (starRingEnd ℂ), fun z => by simp⟩

def std (τ : E →+* ℂ) (ha : 0 < a) : AlgRep E a where
  d := a
  mat := ((coord τ).mapMatrix.toMonoidHom).comp (Units.coeHom _)
  reg i j := Algebra.subset_adjoin (Or.inl ⟨τ, i, j, rfl⟩)
  pos := ha
  irred W hW := by
    obtain ⟨s, hs⟩ := exists_section τ
    have h1 : ∀ M : Matrix (Fin a) (Fin a) ℂ, IsUnit M → ∀ v ∈ W, M *ᵥ v ∈ W := by
      rintro _ ⟨g, rfl⟩ v hv
      convert hW (GeneralLinearGroup.map s g) v hv using 2
      ext i j
      exact (hs _).symm
    have h2 : ∀ M : Matrix (Fin a) (Fin a) ℂ, ∀ v ∈ W, M *ᵥ v ∈ W := by
      intro M v hv
      obtain ⟨c, hc⟩ := (Matrix.finite_spectrum M).infinite_compl.nonempty
      have h3 := h1 _ (spectrum.notMem_iff.1 hc) v hv
      rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec] at h3
      simpa using W.sub_mem (W.smul_mem c hv) h3
    refine or_iff_not_imp_left.2 fun h => eq_top_iff.2 fun w _ => ?_
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 h
    obtain ⟨j, hj⟩ := Function.ne_iff.1 h0
    have hj' : v j ≠ 0 := hj
    convert h2 (Matrix.of fun i k => if k = j then w i / v j else 0) v hv
    ext i
    simp [Matrix.mulVec, dotProduct, hj']

theorem dmat_std (τ : E →+* ℂ) (ha : 0 < a) (X : Lie E a) : (std τ ha).dmat X = (Matrix.of X).map (coord τ) := by
  ext i j
  have h := extGL_eventuallyEq (f := fun y => (std τ ha).mat y i j) (F := fun x => coordL τ (x i j))
    (fun _ => rfl) (x := oneL E a) isUnit_one
  change fderiv ℝ _ _ X = _
  rw [h.fderiv_eq]
  exact congrArg (fun L : Lie E a →L[ℝ] ℂ => L X) (((coordL τ).comp ((ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin a → Cinf E) i))).fderiv)

end AlgRep

variable (E a) in

abbrev Herm : Submodule ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := selfAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) (Cinf E))

def adHerm (k : Kinf E a) (X : Herm E a) : Herm E a := ⟨k.1 * X.1 * star k.1, IsSelfAdjoint.conjugate X.2 k.1⟩

section Complex

omit [NumberField E]

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M)

def IsCochain {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : Prop :=
  ∀ (k : Kinf E a) (X : Fin q → Herm E a), ω (fun i => adHerm k (X i)) = κ k (ω X)

def dCo {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M :=
  AlternatingMap.alternatizeUncurryFin
    { toFun := fun X => ((L (toL X.1)).restrictScalars ℝ).compAlternatingMap ω
      map_add' := fun X Y => AlternatingMap.ext fun v => LinearMap.congr_fun (map_add L (toL X.1) (toL Y.1)) (ω v)
      map_smul' := fun c X => AlternatingMap.ext fun v => LinearMap.congr_fun (map_smul L c (toL X.1)) (ω v) }

theorem dCo_apply {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) (X : Fin (q + 1) → Herm E a) :
    dCo L ω X = ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • L (toL (X i).1) (ω (i.removeNth X)) :=
  AlternatingMap.alternatizeUncurryFin_apply _ _

def HasCohomology : Prop :=
  (∃ ω : Herm E a [⋀^Fin 0]→ₗ[ℝ] M, IsCochain κ ω ∧ dCo L ω = 0 ∧ ω ≠ 0) ∨
    ∃ (q : ℕ) (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M), IsCochain κ ω ∧ dCo L ω = 0 ∧
      ∀ η : Herm E a [⋀^Fin q]→ₗ[ℝ] M, IsCochain κ η → dCo L η ≠ ω

variable {κ L}

theorem IsCochain.dCo (h : ∀ (k : Kinf E a) (X : Herm E a), κ k * L (toL X.1) = L (toL (adHerm k X).1) * κ k)
    {q : ℕ} {ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M} (hω : IsCochain κ ω) : IsCochain κ (dCo L ω) := fun k X => by
  rw [dCo_apply, dCo_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, ← Module.End.mul_apply, h, Module.End.mul_apply, ← hω]
  rfl

theorem hasCohomology_of_invariant {m : M} (h0 : m ≠ 0) (hκ : ∀ k, κ k m = m) (hL : ∀ X, L X m = 0) :
    HasCohomology κ L :=
  Or.inl ⟨AlternatingMap.constOfIsEmpty ℝ _ _ m, fun k _ => (hκ k).symm,
    AlternatingMap.ext fun X => by simp [dCo_apply, hL], fun h => h0 (DFunLike.congr_fun h 0)⟩

theorem dCo_cons {q : ℕ} (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M) (Z : Herm E a) (X : Fin (q + 1) → Herm E a) :
    dCo L ω (Matrix.vecCons Z X) = L (toL Z.1) (ω X) - dCo L (ω.curryLeft Z) X := by
  rw [dCo_apply, dCo_apply, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · simp [Matrix.vecCons]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have e : i.succ.removeNth (Matrix.vecCons Z X) = Matrix.vecCons Z (i.removeNth X) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [Fin.removeNth]
    simp [e, pow_succ]

theorem not_hasCohomology_of_central {c : ℂ} (hc : c ≠ 0) (h : ∀ m, L (oneL E a) m = c • m) :
    ¬ HasCohomology κ L := by
  let Z : Herm E a := ⟨1, IsSelfAdjoint.one _⟩
  have hZ : ∀ k, adHerm k Z = Z := fun k => Subtype.ext (by
    change k.1 * 1 * star k.1 = 1
    rw [mul_one]; exact k.2.2)
  rintro (⟨ω, -, h1, h2⟩ | ⟨q, ω, h0, h1, h2⟩)
  · refine h2 (AlternatingMap.ext fun X => ?_)
    have h3 := DFunLike.congr_fun h1 fun _ => Z
    rw [dCo_apply, Fin.sum_univ_one, h, Subsingleton.elim (Fin.removeNth _ _) X] at h3
    simpa [hc] using h3
  · let s : M →ₗ[ℝ] M := (c⁻¹ • LinearMap.id : M →ₗ[ℂ] M).restrictScalars ℝ
    refine h2 (s.compAlternatingMap (ω.curryLeft Z)) (fun k X => ?_) (AlternatingMap.ext fun X => ?_)
    · change c⁻¹ • ω (Matrix.vecCons Z _) = κ k (c⁻¹ • ω (Matrix.vecCons Z X))
      rw [map_smul, ← h0]
      congr 2
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [hZ]
    · have h3 := dCo_cons (L := L) ω Z X
      rw [h1, h, AlternatingMap.zero_apply, eq_comm, sub_eq_zero, dCo_apply] at h3
      rw [dCo_apply, ← inv_smul_smul₀ hc (ω X), h3, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm c⁻¹, ← map_smul (L _) c⁻¹]
      rfl

end Complex

variable [IsTotallyComplex E]

def lieOp (π : CuspSub E a) : Lie E a →ₗ[ℝ] Module.End ℂ π.V where
  toFun X := π.op (.lie X)
  map_add' X Y := LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun (map_add (lie E a) X Y) φ.1)
  map_smul' c X := LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun (map_smul (lie E a) c X) φ.1)

def tensorK (π : CuspSub E a) (Ξ : AlgRep E a) (k : Kinf E a) : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
  TensorProduct.map (π.op (.cpt k)) (Matrix.toLin' (Ξ.mat (Unitary.toUnits k)))

def tensorLie (π : CuspSub E a) (Ξ : AlgRep E a) : Lie E a →ₗ[ℝ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) where
  toFun X := (lieOp π X).rTensor _ + (Matrix.toLin' (Ξ.dmat X)).lTensor _
  map_add' X Y := by simp only [map_add, LinearMap.rTensor_add, LinearMap.lTensor_add]; abel
  map_smul' c X := by
    rw [map_smul, map_smul, RingHom.id_apply, ← algebraMap_smul ℂ c (lieOp π X), ← algebraMap_smul ℂ c (Ξ.dmat X),
      ← algebraMap_smul ℂ c (_ + _ : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))), map_smul,
      LinearMap.rTensor_smul, LinearMap.lTensor_smul, smul_add]

theorem tensorLie_tmul (π : CuspSub E a) (Ξ : AlgRep E a) (X : Lie E a) (φ : π.V) (v : Fin Ξ.d → ℂ) :
    tensorLie π Ξ X (φ ⊗ₜ v) = π.op (.lie X) φ ⊗ₜ v + φ ⊗ₜ (Ξ.dmat X *ᵥ v) := rfl

theorem tensorK_mul_tensorLie (π : CuspSub E a) (Ξ : AlgRep E a) (k : Kinf E a) (X : Herm E a) :
    tensorK π Ξ k * tensorLie π Ξ (toL X.1) = tensorLie π Ξ (toL (adHerm k X).1) * tensorK π Ξ k := by
  refine TensorProduct.ext' fun φ v => ?_
  have h1 : π.op (.cpt k) (π.op (.lie (toL X.1)) φ) = π.op (.lie (toL (adHerm k X).1)) (π.op (.cpt k) φ) :=
    Subtype.ext (LinearMap.congr_fun (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) X.1) φ.1)
  have h2 : Ξ.mat (Unitary.toUnits k) * Ξ.dmat (toL X.1) = Ξ.dmat (toL (adHerm k X).1) * Ξ.mat (Unitary.toUnits k) :=
    Ξ.mat_mul_dmat (Unitary.toUnits k) X.1
  simp only [Module.End.mul_apply, tensorK, tensorLie_tmul, map_add, TensorProduct.map_tmul, Matrix.toLin'_apply,
    Matrix.mulVec_mulVec, h1, h2]

def IsCohFor (π : CuspSub E a) (Ξ : AlgRep E a) : Prop := HasCohomology (tensorK π Ξ) (tensorLie π Ξ)

def IsCohomological (π : CuspSub E a) : Prop := ∃ Ξ : AlgRep E a, IsCohFor π Ξ

theorem isCohFor_triv (ha : a ≤ 1) : IsCohFor (CuspSub.triv E ha) (AlgRep.triv E a) := by
  let φ : (CuspSub.triv E ha).V := ⟨oneFn E a, Submodule.mem_span_singleton_self _⟩
  refine hasCohomology_of_invariant (m := φ ⊗ₜ fun _ => 1) (fun h => oneFn_ne_zero (E := E) (a := a) ?_) (fun k => ?_)
    fun X => ?_
  · have key : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (v : V), v ⊗ₜ[ℂ] (fun _ : Fin 1 => (1 : ℂ)) = 0 → v = 0 :=
      fun v h => by
        have h1 := congrArg (fun x => TensorProduct.rid ℂ _ (LinearMap.lTensor _ (LinearMap.proj (0 : Fin 1)) x)) h
        simp only [LinearMap.lTensor_tmul, LinearMap.proj_apply, TensorProduct.rid_tmul, one_smul, map_zero] at h1
        exact h1
    exact congrArg Subtype.val (key φ h)
  · rw [tensorK, TensorProduct.map_tmul]
    congr 1
    exact Matrix.one_mulVec (fun _ : Fin 1 => (1 : ℂ))
  · have e : (CuspSub.triv E ha).op (.lie X) φ = 0 := Subtype.ext (lie_oneFn X)
    rw [tensorLie_tmul, e, AlgRep.dmat_triv]
    simp

theorem not_isCohFor_triv_std (τ : E →+* ℂ) : ¬ IsCohFor (CuspSub.triv E le_rfl) (AlgRep.std τ one_pos) := by
  refine not_hasCohomology_of_central one_ne_zero fun m => ?_
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | tmul φ v =>
    have e : (CuspSub.triv E le_rfl).op (.lie (oneL E 1)) φ = 0 := by
      obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 φ.2
      refine Subtype.ext ?_
      change lie E 1 _ φ.1 = 0
      rw [← e, map_smul, lie_oneFn, smul_zero]
    have e2 : (AlgRep.std τ one_pos).dmat (oneL E 1) = 1 :=
      (AlgRep.dmat_std τ one_pos _).trans (Matrix.map_one _ (map_zero _) (map_one _))
    rw [tensorLie_tmul, e, e2]
    simp

end GlobalTheory.GKCoh

namespace GlobalTheory.LocGL

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GenericUnitary

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N : ℕ}

def IsTemperedGL (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ (h : ℕ) (δ : Fin h → IrrGL k) (hd : ∑ i, (δ i).1 = N), (∀ i, IsUnitaryLSeg (δ i)) ∧ Nonempty (π.Equiv (prodIrr δ hd))

theorem IsTemperedGL.of_equiv {π : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) W}
    (H : IsTemperedGL π) (φ : π.Equiv σ) : IsTemperedGL σ := by
  obtain ⟨h, δ, hd, h1, ⟨ψ⟩⟩ := H
  exact ⟨h, δ, hd, h1, ⟨φ.symm.trans ψ⟩⟩

theorem isTemperedGL_of_isUnitaryLSeg {δ : IrrGL k} (h : IsUnitaryLSeg δ) : IsTemperedGL δ.rep :=
  ⟨1, fun _ => δ, by simp, fun _ => h, nonempty_equiv_prodIrr_one δ _⟩

theorem IsTemperedGL.isComplementaryProduct {π : Representation ℂ (GL (Fin N) k) V} (H : IsTemperedGL π) :
    IsComplementaryProduct π := by
  obtain ⟨h, δ, hd, h1, h2⟩ := H
  exact ⟨List.ofFn δ, [], fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact h1 i, by simp, h, δ, hd,
    by simp [factors], h2⟩

theorem isTemperedGL_detRep_one {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) :
    IsTemperedGL (detRep (Fin 1) χ) ↔ IsUnitarisable (detRep (Fin 1) χ) := by
  constructor
  · have key : ∀ (N : ℕ) (π : Representation ℂ (GL (Fin N) k) ℂ), N = 1 → IsTemperedGL π → IsUnitarisable π := by
      rintro N π hN ⟨h, δ, hd, h1, ⟨φ⟩⟩
      have hp : ∀ i, 1 ≤ (δ i).1 := fun i => by
        obtain ⟨Δ, hΔ⟩ := (h1 i).1
        exact hΔ.deg_eq ▸ Nat.mul_pos Δ.len_pos Δ.d_pos
      have h2 : h ≤ 1 := by simpa [hd, hN] using Finset.sum_le_sum (s := Finset.univ) fun i _ => hp i
      have h3 : h ≠ 0 := by rintro rfl; simp [hN] at hd
      obtain rfl : h = 1 := by omega
      obtain ⟨x, rfl⟩ : ∃ x, δ = fun _ => x := ⟨δ 0, funext fun i => congrArg δ (Subsingleton.elim _ _)⟩
      obtain rfl : x.1 = N := by simpa using hd
      obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one x hd
      exact isUnitarisable_of_equiv (ψ.trans φ.symm) (h1 0).2
    exact key 1 _ rfl
  · intro hu
    have hc := isCuspidal_detRep_one hs
    let φ := IrrGL.equivOf (detRep (Fin 1) χ) hc.1 (isIrreducible_ofChar _)
    exact (isTemperedGL_of_isUnitaryLSeg (isUnitaryLSeg_of_isCusp (IrrGL.isCusp_of.2 ⟨one_pos, hc⟩)
      (isUnitarisable_of_equiv φ hu))).of_equiv φ.symm

end GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def CohomologicalCsdTempered : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), 2 ≤ n →
    ∀ π : CuspSub L n, π.IsCsd → GKCoh.IsCohomological π →
      ∀ (y : HeightOneSpectrum (𝓞 L)) (σ : SmIrr (GL (Fin n) (y.adicCompletion L))), π.IsLocComp y σ →
        LocGL.IsTemperedGL σ.ρ

end GlobalTheory.Published
