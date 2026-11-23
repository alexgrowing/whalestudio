import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieSmoothAndLinear
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalEigenspaceSumSqInvariantFieldsAStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKerAevalOfEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfFiniteDimensionalTranslationStableStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticGelfandInvariantEqNegSumSqDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteHermitianEqPmGramUnitaryCompactStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntertwineAeval

noncomputable section

namespace GlobalTheory.DefiniteForms

open GlobalTheory.SmoothForms Filter Topology
open scoped ContDiff

section Abstract

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

theorem mul_anti_of_unitary {a : 𝔸} (h : σ a * a = 1) : a * σ a = 1 := by
  have : IsArtinianRing 𝔸 := IsArtinianRing.of_finite ℝ 𝔸
  exact mul_eq_one_comm.1 h

omit [FiniteDimensional ℝ 𝔸] in
theorem unitary_mul (H : IsLieData σ j s) {a b : 𝔸} (ha : σ a * a = 1) (hb : σ b * b = 1) :
    σ (a * b) * (a * b) = 1 := by
  rw [H.anti, mul_assoc, ← mul_assoc (σ a), ha, one_mul, hb]

theorem unitary_anti (H : IsLieData σ j s) {a : 𝔸} (ha : σ a * a = 1) : σ (σ a) * σ a = 1 := by
  rw [H.invol, mul_anti_of_unitary ha]

theorem continuousOn_of_sm (H : IsLieData σ j s) (hl : HasLog σ j) {φ : G → ℂ} (hφ : Sm (expMap j s) φ) (g : G) :
    ContinuousOn (fun u => φ (g * s u)) {u | σ u * u = 1} := by
  obtain ⟨Λ, h1, h2, -⟩ := hl
  intro u₀ hu₀
  have hu₀' : σ u₀ * u₀ = 1 := hu₀
  have hm : Continuous fun u : 𝔸 => σ u₀ * u := continuous_const.mul continuous_id
  have ht : Tendsto (fun u => σ u₀ * u) (𝓝 u₀) (𝓝 1) := by
    have := hm.tendsto u₀
    rwa [hu₀'] at this
  have h4 : ContinuousAt (fun u => Λ (σ u₀ * u)) u₀ :=
    ContinuousAt.comp (g := Λ) (by rw [hu₀']; exact h1.continuousAt) hm.continuousAt
  have h5 : ContinuousAt (fun u => φ (g * s u₀ * expMap j s (Λ (σ u₀ * u)))) u₀ :=
    (hφ (g * s u₀)).continuous.continuousAt.comp h4
  have key : ∀ u, (σ (σ u₀ * u) * (σ u₀ * u) = 1 → NormedSpace.exp (j (Λ (σ u₀ * u))) = σ u₀ * u) → σ u * u = 1 →
      φ (g * s u) = φ (g * s u₀ * expMap j s (Λ (σ u₀ * u))) := fun u hp hu => by
    have hu' := unitary_mul H (unitary_anti H hu₀') hu
    rw [expMap, hp hu', mul_assoc, ← H.mul _ _ hu₀' hu', ← mul_assoc, mul_anti_of_unitary hu₀', one_mul]
  refine h5.continuousWithinAt.congr_of_eventuallyEq ?_ (key u₀ (ht.eventually h2).self_of_nhds hu₀')
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ht.eventually h2), self_mem_nhdsWithin] with u a b using key u a b

def uGrp (H : IsLieData σ j s) : Subgroup 𝔸ˣ where
  carrier := {u | σ u * u = 1}
  mul_mem' := fun ha hb => unitary_mul H ha hb
  one_mem' := by simp [H.one]
  inv_mem' := fun {u} hu => by
    have h : ((u⁻¹ : 𝔸ˣ) : 𝔸) = σ u := Units.inv_eq_of_mul_eq_one_left hu
    change σ (u⁻¹ : 𝔸ˣ) * (u⁻¹ : 𝔸ˣ) = 1
    rw [h]
    exact unitary_anti H hu

open Classical in

def toU (H : IsLieData σ j s) (a : 𝔸) : uGrp H :=
  if h : σ a * a = 1 then ⟨⟨a, σ a, mul_anti_of_unitary h, h⟩, h⟩ else 1

theorem toU_val (H : IsLieData σ j s) {a : 𝔸} (h : σ a * a = 1) : ((toU H a).1 : 𝔸) = a := by
  rw [toU, dif_pos h]

theorem toU_coe (H : IsLieData σ j s) (k : uGrp H) : toU H (k.1 : 𝔸) = k :=
  Subtype.ext (Units.ext (toU_val H k.2))

theorem isLieData_toU (H : IsLieData σ j s) : IsLieData σ j (toU H) :=
  ⟨H.anti, H.one, H.invol, H.inj, H.skew, fun a b ha hb => Subtype.ext (Units.ext (by
    change ((toU H (a * b)).1 : 𝔸) = (toU H a).1 * (toU H b).1
    rw [toU_val H (unitary_mul H ha hb), toU_val H ha, toU_val H hb]))⟩

theorem continuous_val (H : IsLieData σ j s) : Continuous fun k : uGrp H => (k.1 : 𝔸) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_toU (H : IsLieData σ j s) {X : Type} [TopologicalSpace X] {c : X → 𝔸} (hc : Continuous c)
    (hu : ∀ x, σ (c x) * c x = 1) : Continuous fun x => toU H (c x) := by
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hc.congr fun x => (toU_val H (hu x)).symm, ?_⟩)
  refine (σ.continuous_of_finiteDimensional.comp hc).congr fun x => ?_
  refine (Units.inv_eq_of_mul_eq_one_left ?_).symm
  change σ (c x) * ((toU H (c x)).1 : 𝔸) = 1
  rw [toU_val H (hu x), hu]

theorem compactSpace_uGrp (H : IsLieData σ j s) (hc : IsCompact {a | σ a * a = 1}) : CompactSpace (uGrp H) := by
  have := isCompact_iff_compactSpace.1 hc
  have h := isCompact_range (continuous_toU H (c := fun a : {a | σ a * a = 1} => a.1) continuous_subtype_val fun a => a.2)
  refine ⟨by convert h; exact (Set.range_eq_univ.2 fun k => ⟨⟨k.1, k.2⟩, toU_coe H k⟩).symm⟩

theorem expMap_add (H : IsLieData σ j s) (X : L) (a b : ℝ) :
    expMap j s ((a + b) • X) = expMap j s (a • X) * expMap j s (b • X) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  let : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold expMap
  rw [← H.mul _ _ (DerLinear.exp_unitary H _) (DerLinear.exp_unitary H _), ← NormedSpace.exp_add_of_commute, add_smul,
    map_add]
  rw [map_smul, map_smul]
  exact ((Commute.refl _).smul_left _).smul_right _

theorem hasDerivAt_sm (H : IsLieData σ j s) {φ : G → ℂ} (hφ : Sm (expMap j s) φ) (X : L) (x : G) (t : ℝ) :
    HasDerivAt (fun t : ℝ => φ (x * expMap j s (t • X))) (Der (expMap j s) X φ (x * expMap j s (t • X))) t := by
  have h := (Sm.differentiableAt hφ (x * expMap j s (t • X)) X).hasDerivAt
  rw [← sub_self t] at h
  have h2 := h.comp_sub_const t t
  rw [sub_self] at h2
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
  simp only
  rw [mul_assoc, ← expMap_add H, add_sub_cancel]

theorem finite_ker (H : IsLieData σ j s) (hl : HasLog σ j) (hc : IsCompact {a | σ a * a = 1}) {ι : Type} [Fintype ι]
    (X : ι → L) (hX : Submodule.span ℝ (Set.range X) = ⊤) (p : Polynomial ℂ) (hp : p ≠ 0) :
    FiniteDimensional ℂ (LinearMap.ker (Polynomial.aeval
      (∑ i, derOp (isLieData_toU H) hl (X i) * derOp (isLieData_toU H) hl (X i)) p)) := by
  have := compactSpace_uGrp H hc
  have : FiniteDimensional ℝ L := FiniteDimensional.of_injective j H.inj
  have H' := isLieData_toU H
  refine GlobalTheory.T.finiteDimensional_ker_aeval_of_eigenspaces' _ _ (fun lam => ?_) p hp
  refine GlobalTheory.T.finiteDimensional_eigenspace_sum_sq_invariantFields_alt (uGrp H) L _ (fun f hf => ?_) (expMap j (toU H)) (fun Y => ?_) ?_ (fun r hr => ?_) _
    (derOp_add _ hl) (derOp_smul _ hl) (fun Y f x t => hasDerivAt_sm H' f.2 Y x t) ι X hX lam
  · refine ((continuousOn_of_sm H' hl hf 1).comp_continuous (continuous_val H) fun k => k.2).congr fun k => ?_
    simp only [Function.comp, one_mul, toU_coe]
  · exact continuous_toU H ((DerLinear.contDiff_exp H).continuous.comp (continuous_id.smul continuous_const))
      fun t => DerLinear.exp_unitary H _
  · rw [expMap, map_zero, NormedSpace.exp_zero]
    exact toU_coe H 1
  · obtain ⟨Λ, h1, h2, h3⟩ := hl
    have hΛ : Λ 1 = 0 := by simpa using h3.self_of_nhds
    have h4 : ∀ᶠ a in 𝓝 (1 : 𝔸), Λ a ∈ Metric.ball (0 : L) r :=
      h1.continuousAt.eventually (by rw [hΛ]; exact Metric.ball_mem_nhds _ hr)
    have ht : Tendsto (fun k : uGrp H => (k.1 : 𝔸)) (𝓝 1) (𝓝 1) := (continuous_val H).tendsto 1
    filter_upwards [ht.eventually h2, ht.eventually h4] with k a b
    exact ⟨_, b, by rw [expMap, a k.2, toU_coe]⟩

theorem map_aeval {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (r : M →ₗ[ℂ] N)
    {T : Module.End ℂ M} {T' : Module.End ℂ N} (h : ∀ v, r (T v) = T' (r v)) (p : Polynomial ℂ) (v : M) :
    r (Polynomial.aeval T p v) = Polynomial.aeval T' p (r v) := by
  first
  | exact @_root_.GlobalTheory.IntertwineAeval.intertwine_aeval
  | exact _root_.GlobalTheory.IntertwineAeval.intertwine_aeval
  | (apply _root_.GlobalTheory.IntertwineAeval.intertwine_aeval <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntertwineAeval.intertwine_aeval <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntertwineAeval.intertwine_aeval <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntertwineAeval.intertwine_aeval ..)

theorem s_mul_exp (H : IsLieData σ j s) (k : uGrp H) (Y : L) :
    s ((k * expMap j (toU H) Y).1 : 𝔸) = s (k.1 : 𝔸) * expMap j s Y := by
  change s ((k.1 : 𝔸) * (toU H _).1) = _
  rw [toU_val H (DerLinear.exp_unitary H _), H.mul _ _ k.2 (DerLinear.exp_unitary H _), expMap]

def res (H : IsLieData σ j s) (x : G) : smSub (expMap j s) →ₗ[ℂ] smSub (expMap j (toU H)) where
  toFun φ := ⟨fun k => φ.1 (x * s (k.1 : 𝔸)), fun k => by
    simp only [s_mul_exp, ← mul_assoc]
    exact φ.2 _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem res_derOp (H : IsLieData σ j s) (hl : HasLog σ j) (x : G) (Y : L) (φ : smSub (expMap j s)) :
    res H x (derOp H hl Y φ) = derOp (isLieData_toU H) hl Y (res H x φ) := by
  refine Subtype.ext (funext fun k => ?_)
  change deriv (fun t : ℝ => φ.1 (x * s (k.1 : 𝔸) * expMap j s (t • Y))) 0 =
    deriv (fun t : ℝ => φ.1 (x * s ((k * expMap j (toU H) (t • Y)).1 : 𝔸))) 0
  simp only [s_mul_exp, ← mul_assoc]

theorem finite_translates (H : IsLieData σ j s) (hl : HasLog σ j) (hc : IsCompact {a | σ a * a = 1}) {ι : Type}
    [Fintype ι] (X : ι → L) (hX : Submodule.span ℝ (Set.range X) = ⊤) (W : Submodule ℂ (smSub (expMap j s)))
    [FiniteDimensional ℂ W] (hW : ∀ f ∈ W, (∑ i, derOp H hl (X i) * derOp H hl (X i)) f ∈ W)
    {φ : smSub (expMap j s)} (hφ : φ ∈ W) :
    ∃ M : Submodule ℂ (G → ℂ), FiniteDimensional ℂ M ∧ ∀ u, σ u * u = 1 → (fun g => φ.1 (g * s u)) ∈ M := by
  let T : Module.End ℂ W := LinearMap.restrict _ hW
  have := finite_ker H hl hc X hX T.charpoly T.charpoly_monic.ne_zero
  have hm : ∀ x, res H x φ ∈ LinearMap.ker (Polynomial.aeval
      (∑ i, derOp (isLieData_toU H) hl (X i) * derOp (isLieData_toU H) hl (X i)) T.charpoly) := fun x => by
    have := map_aeval (res H x ∘ₗ W.subtype) (T := T)
      (T' := ∑ i, derOp (isLieData_toU H) hl (X i) * derOp (isLieData_toU H) hl (X i)) (fun v => by
        change res H x ((∑ i, derOp H hl (X i) * derOp H hl (X i)) v.1) = _
        simp only [LinearMap.sum_apply, map_sum, Module.End.mul_apply, res_derOp]
        rfl) T.charpoly ⟨φ, hφ⟩
    rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply, map_zero] at this
    exact this.symm
  let b := Module.finBasis ℂ (LinearMap.ker (Polynomial.aeval
      (∑ i, derOp (isLieData_toU H) hl (X i) * derOp (isLieData_toU H) hl (X i)) T.charpoly))
  let c := fun i (x : G) => b.repr ⟨_, hm x⟩ i
  refine ⟨Submodule.span ℂ (Set.range c), FiniteDimensional.span_of_finite _ (Set.finite_range c), fun u hu => ?_⟩
  have e : (fun g => φ.1 (g * s u)) = ∑ i, (b i).1.1 (toU H u) • c i := by
    funext g
    have h1 := congrArg (fun y => y.1.1 (toU H u)) (b.sum_repr ⟨_, hm g⟩)
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    have h2 : (res H g φ).1 (toU H u) = φ.1 (g * s u) := by
      change φ.1 (g * s ((toU H u).1 : 𝔸)) = _
      rw [toU_val H hu]
    rw [← h2, ← h1]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Abstract

section Adelic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfF D} {V : HSp D}

theorem frame_at (hs : V.SigOK) (hd : V.IsDefinite) (τ : D.what₂.Tau) :
    (∃ B : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUnit B.det ∧ (gramAt D V τ = Bᴴ * B ∨ gramAt D V τ = -(Bᴴ * B))) ∧
      IsCompact (Formalism.QuantumDeterminants.UH (gramAt D V τ)) :=
  GlobalTheory.T.definite_hermitian_eq_pm_gram_unitary_compact _ _ _ _ (hs (tauE D τ)) (by rcases hd (tauE D τ) with h | h <;> simp [h])

theorem isCompact_unitary (R : RealPoints θ V) (hs : V.SigOK) (hd : V.IsDefinite) :
    IsCompact {u : AlgInf V | sigInf V u * u = 1} := by
  have h := isCompact_univ_pi fun τ => (frame_at hs hd τ).2
  have e : {u : AlgInf V | sigInf V u * u = 1} = Set.univ.pi fun τ => Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
    Set.ext fun u => (unit_iff R u).trans ⟨fun h τ _ => h τ, fun h τ => h τ trivial⟩
  rw [e]
  exact h

theorem exists_secInf (hθ : IsInfFam θ) (R : RealPoints θ V) {g : GA D V} (hg : g ∈ GinfC V) :
    ∃ u : AlgInf V, sigInf V u * u = 1 ∧ secInf θ V u = g := by
  have hu := (unit_iff R fun τ => infMat D.sp.cm.sig V.gram (θ τ) g).2
    fun τ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
  exact ⟨_, hu, R.2.2.1 _ (secInf_spec R hu).1 _ hg (secInf_spec R hu).2⟩

theorem gelf_one (R : RealPoints θ V) (hs : V.SigOK) (hd : V.IsDefinite) (τ : D.what₂.Tau) :
    ∃ X : Fin V.rank × Fin V.rank × Bool → LieAt V τ, Submodule.span ℝ (Set.range X) = ⊤ ∧ ∀ f : SmF θ V,
      ((∑ i, opInf R (atPlace V τ (X i)) * opInf R (atPlace V τ (X i))) f).1 = -gelf θ V τ 1 f.1 := by
  obtain ⟨B, hB, hJ⟩ := (frame_at hs hd τ).1
  obtain ⟨X, hX, h⟩ := GlobalTheory.T.quadraticGelfandInvariant_eq_neg_sum_sq_definite _ _ B hB hJ
  obtain ⟨P, Q, hPQ, -⟩ := GlobalTheory.UnitaryLieComplexification.glRel_and_span _ _ (R.1 τ).1 (R.1 τ).2
  have h1 := h P Q hPQ _ (fun Y => opInf R (atPlace V τ Y)) (opAt_add R τ) (opAt_smul R τ)
  refine ⟨X, hX, fun f => ?_⟩
  rw [← neg_eq_iff_eq_neg.2 h1, LinearMap.neg_apply, Submodule.coe_neg, neg_inj]
  have e : ∀ a b (x : SmF θ V), RderC θ V τ (Matrix.single a b 1) x.1 =
      ((opInf R (atPlace V τ (P a b)) + Complex.I • opInf R (atPlace V τ (Q a b))) x).1 := fun a b x => by
    rw [RderC, conjAt, ← (hPQ _ _).1, ← (hPQ _ _).2, Rder_eq R, Rder_eq R]
    rfl
  rw [gelf, ← (finTwoArrowEquiv _).symm.sum_comp, Fintype.sum_prod_type]
  simp only [LinearMap.sum_apply, Submodule.coe_sum, Module.End.mul_apply, ← e]
  rfl

theorem kfin_of_sm (hθ : IsInfFam θ) (hs : V.SigOK) (hd : V.IsDefinite) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) :
    IsAutFunDef V φ := by
  classical
  have R := RealPts.realPoints D |>.2 θ hθ V
  refine ⟨h.toIsAutFun, ?_⟩
  obtain ⟨W, hW, hφ, hst⟩ := h.zfin
  choose X hX hg using gelf_one R hs hd
  have : FiniteDimensional ℂ (W.comap (SmF θ V).subtype) :=
    FiniteDimensional.of_injective ((SmF θ V).subtype.restrict (p := W.comap (SmF θ V).subtype) (q := W) fun _ hx => hx)
      fun x y hxy => by
        have h' := congrArg Subtype.val hxy
        exact Subtype.ext (Subtype.ext h')
  have key := finite_translates (isLieData R) (hasLog R) (isCompact_unitary R hs hd)
    (fun p : D.what₂.Tau × Fin V.rank × Fin V.rank × Bool => (atPlace V p.1 (X p.1 p.2) : LieN V)) ?_
    (W.comap (SmF θ V).subtype) (fun f hf => ?_) (φ := ⟨φ, (smooth_iff R φ).1 h.smooth⟩) hφ
  · obtain ⟨M, hM, hm⟩ := key
    refine Submodule.finiteDimensional_of_le (S₂ := M) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨u, hu, rfl⟩ := exists_secInf hθ R hk
    exact hm u hu
  · rw [eq_top_iff]
    intro Y _
    have : Y = ∑ τ, (atPlace V τ (Y τ) : LieN V) := (sum_atPlace Y).symm
    rw [this]
    refine sum_mem fun τ _ => ?_
    have hY : (Y τ : LieAt V τ) ∈ Submodule.span ℝ (Set.range (X τ)) := hX τ ▸ Submodule.mem_top
    generalize (Y τ : LieAt V τ) = Z at hY
    induction hY using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨(τ, i), rfl⟩
    | zero => rw [atPlace, Pi.single_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [atPlace, Pi.single_add]; exact add_mem hx hy
    | smul c x _ hx => rw [atPlace, Pi.single_smul]; exact Submodule.smul_mem _ c hx
  · rw [Fintype.sum_prod_type, LinearMap.sum_apply]
    refine sum_mem fun τ _ => ?_
    change ((∑ i, opInf R (atPlace V τ (X τ i)) * opInf R (atPlace V τ (X τ i))) f).1 ∈ W
    rw [hg]
    exact neg_mem (hst τ 1 _ hf)

theorem foldr_mem {α M : Type} {S : Set M} (T : α → M → M) (l : List α) (hl : ∀ a ∈ l, ∀ f ∈ S, T a f ∈ S) {f : M}
    (hf : f ∈ S) : l.foldr (fun a f => T a f) f ∈ S := by
  induction l with
  | nil => exact hf
  | cons a l ih => exact hl a (by simp) _ (ih fun b hb => hl b (by simp [hb]))

theorem sm_of_kfin (hθ : IsInfFam θ) (hs : V.SigOK) (hd : V.IsDefinite) {φ : GA D V → ℂ} (h : IsAutFunDef V φ) :
    IsAutFunSm θ V φ := by
  have R := RealPts.realPoints D |>.2 θ hθ V
  have hfd := h.kfin
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  set M := Submodule.span ℂ {ψ : GA D V → ℂ | ∃ k ∈ GinfC V, ψ = rTr V k φ} with hM
  have hφ : φ ∈ M := Submodule.subset_span ⟨1, one_mem _, funext fun g => by simp [rTr]⟩
  have hcont : ∀ f ∈ M, Continuous f := fun f hf => by
    induction hf using Submodule.span_induction with
    | mem x hx => obtain ⟨k, -, rfl⟩ := hx; exact h.cont.comp (continuous_mul_const k)
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx => exact hx.const_smul c
  have hst : ∀ k ∈ GinfC V, ∀ f ∈ M, (fun g => f (g * k)) ∈ M := fun k hk f hf => by
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k', hk', rfl⟩ := hx
      exact Submodule.subset_span ⟨k * k', mul_mem hk hk', funext fun g => by simp [rTr, mul_assoc]⟩
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx => exact M.smul_mem c hx
  obtain ⟨h1, h2⟩ := GlobalTheory.T.deriv_mem_and_contDiff_of_translation_stable (GA D V) M (Σ τ, LieAt V τ) (fun i t => oneP θ V i.1 i.2.1 t)
    (fun i a b => by
      simp only [oneP_eq R]
      exact expMap_add (isLieData R) _ a b)
    (fun i t => hst _ (GlobalTheory.PointAtPlaceHom.atTau_mem V _ _))
    (fun i f hf g => by
      refine (hcont f hf).comp (continuous_const.mul ?_)
      refine (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V i.1).comp_continuous ?_
        fun t => GlobalTheory.SmoothAutCheck.exp_mem_UH (R.1 i.1).2 i.2.2 t
      have := (continuous_apply i.1).comp ((DerLinear.contDiff_exp (isLieData R)).continuous.comp
        (continuous_id.smul continuous_const : Continuous fun t : ℝ => t • (atPlace V i.1 i.2 : LieN V)))
      refine this.congr fun t => ?_
      classical
      refine (exp_algInf V _ _).trans ?_
      congr 1
      change t • (atPlace V i.1 i.2 i.1).1 = _
      rw [atPlace, Pi.single_eq_same])
  have hR : ∀ τ, ∀ X ∈ lieAt V τ, ∀ f ∈ M, Rder θ V τ X f ∈ M := fun τ X hX => h1 ⟨τ, X, hX⟩
  have hsm : ∀ f ∈ M, f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := fun f hf k τs Xs hX g =>
    h2 k (fun a => ⟨τs a, Xs a, hX a⟩) f hf g
  refine ⟨h.toIsAutFun, hsm φ hφ, ⟨M, hfd, hφ, fun τ k f hf => ?_⟩, 0, fun l hl x => ?_⟩
  · refine sum_mem fun idx _ => foldr_mem (S := (M : Set _)) (fun T : (GA D V → ℂ) → GA D V → ℂ => T) _
      (fun T hT f hf => ?_) hf
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hT
    obtain ⟨m1, m2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ (Matrix.single (idx a) (idx (a + 1)) 1)
    exact add_mem (hR τ _ m1 f hf) (M.smul_mem _ (hR τ _ m2 f hf))
  · have hf := foldr_mem (S := (M : Set _))
      (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l (fun p hp => hR p.1 p.2 (hl p hp)) hφ
    obtain ⟨C, hC⟩ := (isCompact_unitary R hs hd).exists_bound_of_continuousOn
      (continuousOn_of_sm (isLieData R) (hasLog R) ((smooth_iff R _).1 (hsm _ hf)) x)
    refine ⟨C, fun g hg => ?_⟩
    obtain ⟨u, hu, rfl⟩ := exists_secInf hθ R hg
    rw [pow_zero, mul_one]
    exact hC u hu

theorem autFunDefIffSm : ∀ D : D7, AutFunDefIffSm D :=
  fun _ _ hθ _ hs hd _ => ⟨sm_of_kfin hθ hs hd, kfin_of_sm hθ hs hd⟩

end Adelic

end GlobalTheory.DefiniteForms

end
