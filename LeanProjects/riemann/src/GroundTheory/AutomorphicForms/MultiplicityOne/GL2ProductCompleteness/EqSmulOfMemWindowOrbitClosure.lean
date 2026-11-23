import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.MultOne
import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep

open scoped InnerProductSpace ComplexConjugate ComplexStarModule
open Set Function

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2ProductCompleteness

set_option linter.unusedSectionVars false

section Schur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem eq_smul_one_of_commute_of_star [Nontrivial E] {S : Set (E →L[ℂ] E)}
    (hirr : ∀ W : Submodule ℂ E, IsClosed (W : Set E) → (∀ s ∈ S, ∀ v ∈ W, s v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    {T : E →L[ℂ] E} (hT : ∀ s ∈ S, Commute T s) (hT' : ∀ s ∈ S, Commute (star T) s) :
    ∃ c : ℂ, T = c • (1 : E →L[ℂ] E) := by
  have hre : ∀ s ∈ S, Commute (ℜ T : E →L[ℂ] E) s := by
    intro s hs
    rw [realPart_apply_coe]
    exact ((hT s hs).add_left (hT' s hs)).smul_left _
  have him : ∀ s ∈ S, Commute (ℑ T : E →L[ℂ] E) s := by
    intro s hs
    rw [imaginaryPart_apply_coe]
    exact (((hT s hs).sub_left (hT' s hs)).smul_left _).smul_left _
  obtain ⟨a, ha⟩ := ArchWhittaker.eq_algebraMap_of_commute hirr (ℜ T).2 hre
  obtain ⟨b, hb⟩ := ArchWhittaker.eq_algebraMap_of_commute hirr (ℑ T).2 him
  refine ⟨a + Complex.I * b, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T, ha, hb]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul,
    ← Complex.coe_smul, smul_smul, ← add_smul]

end Schur

variable {G G₁ G₂ : Type*} [Group G] [TopologicalSpace G] [Group G₁] [TopologicalSpace G₁]
  [Group G₂] [TopologicalSpace G₂]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable (τ : UnitaryRep G V) (ι₁ : G₁ →* G) (ι₂ : G₂ →* G)
variable (D : Submodule ℂ V) [CompleteSpace D]

def compr (a : G₁) : D →L[ℂ] D :=
  D.orthogonalProjectionOnto ∘L ((τ (ι₁ a) : V →L[ℂ] V) ∘L D.subtypeL)

theorem inner_compr (a : G₁) (x y : D) :
    ⟪(y : V), (compr τ ι₁ D a x : V)⟫_ℂ = ⟪(y : V), τ (ι₁ a) x⟫_ℂ := by
  show ⟪(y : V), ((D.orthogonalProjectionOnto (τ (ι₁ a) (x : V)) : D) : V)⟫_ℂ = _
  rw [← Submodule.coe_inner, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]

structure Splitting : Prop where
  irred : τ.IsIrreducible
  comm : ∀ a b, ι₁ a * ι₂ b = ι₂ b * ι₁ a
  gen : ∀ g, ∃ a b, ι₁ a * ι₂ b = g
  ne_bot : D ≠ ⊥
  inv : ∀ T : V →L[ℂ] V, (∀ a, Commute T (τ (ι₁ a))) → ∀ x ∈ D, T x ∈ D
  compr_comm : ∀ a a', Commute (compr τ ι₁ D a) (compr τ ι₁ D a')

variable {τ ι₁ ι₂ D}

theorem Splitting.mem₂ (hs : Splitting τ ι₁ ι₂ D) (b : G₂) {x : V} (hx : x ∈ D) :
    τ (ι₂ b) x ∈ D := by
  refine hs.inv _ (fun a => ?_) x hx
  show τ (ι₂ b) * τ (ι₁ a) = τ (ι₁ a) * τ (ι₂ b)
  rw [← UnitaryRep.map_mul, ← UnitaryRep.map_mul, hs.comm]

theorem Splitting.nontrivial (hs : Splitting τ ι₁ ι₂ D) : Nontrivial D := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff D).1 hs.ne_bot
  exact ⟨⟨⟨x, hx⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩

def onWindow (hs : Splitting τ ι₁ ι₂ D) (b : G₂) : D →L[ℂ] D :=
  ((τ (ι₂ b) : V →L[ℂ] V) ∘L D.subtypeL).codRestrict D (fun x => hs.mem₂ b x.2)

@[simp] theorem coe_onWindow (hs : Splitting τ ι₁ ι₂ D) (b : G₂) (x : D) :
    ((onWindow hs b x : D) : V) = τ (ι₂ b) x := rfl

theorem inner_map_right_mem (a : G₁) {x y : V} (hx : x ∈ D) (hy : y ∈ D) :
    ⟪y, τ (ι₁ a) x⟫_ℂ = ⟪(⟨y, hy⟩ : D), compr τ ι₁ D a ⟨x, hx⟩⟫_ℂ := by
  rw [Submodule.coe_inner, inner_compr]

theorem window_irreducible (hs : Splitting τ ι₁ ι₂ D) (U : Submodule ℂ D) (hU : IsClosed (U : Set D))
    (h1 : ∀ a, ∀ x ∈ U, compr τ ι₁ D a x ∈ U) (h2 : ∀ b, ∀ x ∈ U, onWindow hs b x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hU0 : U = ⊥
  · exact Or.inl hU0
  right
  obtain ⟨x', hx'U, hx'0⟩ := (Submodule.ne_bot_iff U).1 hU0
  have : CompleteSpace U := hU.completeSpace_coe
  rw [← Submodule.orthogonal_eq_bot_iff, eq_bot_iff]
  intro y' hy'
  rw [Submodule.mem_bot]
  apply Subtype.ext
  refine ArchWhittaker.eq_zero_of_forall_inner_map hs.irred (x := (x' : V))
    (fun h => hx'0 (Subtype.ext h)) fun g => ?_
  obtain ⟨a, b, rfl⟩ := hs.gen g
  rw [UnitaryRep.map_mul_apply]
  have hz : onWindow hs b x' ∈ U := h2 b x' hx'U
  have key := inner_compr τ ι₁ D a (onWindow hs b x') y'
  rw [coe_onWindow] at key
  rw [← key, ← Submodule.coe_inner]
  have h0 : ⟪(compr τ ι₁ D a (onWindow hs b x') : D), y'⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal U y').1 hy' _ (h1 a _ hz)
  rw [← inner_conj_symm, h0, map_zero]

theorem star_compr (a : G₁) : star (compr τ ι₁ D a) = compr τ ι₁ D a⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [Submodule.coe_inner, Submodule.coe_inner, ← inner_conj_symm, inner_compr,
    inner_conj_symm, UnitaryRep.inner_map_left, map_inv, inv_inv, ← inner_compr]

theorem commute_compr_onWindow (hs : Splitting τ ι₁ ι₂ D) (a : G₁) (b : G₂) :
    Commute (compr τ ι₁ D a) (onWindow hs b) := by
  ext1 x
  apply ext_inner_left ℂ
  intro y
  show ⟪y, compr τ ι₁ D a (onWindow hs b x)⟫_ℂ = ⟪y, onWindow hs b (compr τ ι₁ D a x)⟫_ℂ
  rw [Submodule.coe_inner, inner_compr, coe_onWindow, Submodule.coe_inner, coe_onWindow,
    τ.inner_map_right (ι₂ b) (y : V), ← map_inv]
  set y₁ : D := ⟨τ (ι₂ b⁻¹) y, hs.mem₂ b⁻¹ y.2⟩
  have e1 : ⟪τ (ι₂ b⁻¹) (y : V), (compr τ ι₁ D a x : V)⟫_ℂ = ⟪(y₁ : V), τ (ι₁ a) x⟫_ℂ :=
    inner_compr τ ι₁ D a x y₁
  rw [e1]
  show _ = ⟪τ (ι₂ b⁻¹) (y : V), τ (ι₁ a) (x : V)⟫_ℂ
  rw [τ.inner_map_left (ι₂ b⁻¹), map_inv, inv_inv, ← UnitaryRep.map_mul_apply,
    ← UnitaryRep.map_mul_apply, hs.comm]

theorem exists_compr_eq_smul (hs : Splitting τ ι₁ ι₂ D) :
    ∃ c : G₁ → ℂ, ∀ a, compr τ ι₁ D a = c a • (1 : D →L[ℂ] D) := by
  have := hs.nontrivial
  set S : Set (D →L[ℂ] D) := range (compr τ ι₁ D) ∪ range (onWindow hs)
  have hirr : ∀ U : Submodule ℂ D, IsClosed (U : Set D) → (∀ s ∈ S, ∀ v ∈ U, s v ∈ U) →
      U = ⊥ ∨ U = ⊤ := fun U hU hinv =>
    window_irreducible hs U hU (fun a x hx => hinv _ (Or.inl ⟨a, rfl⟩) x hx)
      (fun b x hx => hinv _ (Or.inr ⟨b, rfl⟩) x hx)
  have hcs : ∀ a, ∀ s ∈ S, Commute (compr τ ι₁ D a) s := by
    rintro a s (⟨a', rfl⟩ | ⟨b, rfl⟩)
    · exact hs.compr_comm a a'
    · exact commute_compr_onWindow hs a b
  choose c hc using fun a => eq_smul_one_of_commute_of_star hirr (hcs a)
    (by rw [star_compr]; exact hcs a⁻¹)
  exact ⟨c, hc⟩

def Splitting.coeff (hs : Splitting τ ι₁ ι₂ D) (a : G₁) : ℂ := (exists_compr_eq_smul hs).choose a

theorem Splitting.compr_eq (hs : Splitting τ ι₁ ι₂ D) (a : G₁) :
    compr τ ι₁ D a = hs.coeff a • (1 : D →L[ℂ] D) :=
  (exists_compr_eq_smul hs).choose_spec a

theorem Splitting.inner_map_eq (hs : Splitting τ ι₁ ι₂ D) (a : G₁) {x y : V} (hx : x ∈ D)
    (hy : y ∈ D) : ⟪y, τ (ι₁ a) x⟫_ℂ = hs.coeff a * ⟪y, x⟫_ℂ := by
  rw [inner_map_right_mem a hx hy, hs.compr_eq]
  simp [inner_smul_right]

variable (τ ι₁) in

def comb (x : V) : (G₁ →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ (fun a => τ (ι₁ a) x)

theorem comb_apply (x : V) (f : G₁ →₀ ℂ) : comb τ ι₁ x f = f.sum fun a α => α • τ (ι₁ a) x :=
  Finsupp.linearCombination_apply ℂ f

theorem comb_add (x y : V) (f : G₁ →₀ ℂ) : comb τ ι₁ (x + y) f = comb τ ι₁ x f + comb τ ι₁ y f := by
  simp only [comb_apply, map_add, smul_add, Finsupp.sum_add]

theorem comb_smul (c : ℂ) (x : V) (f : G₁ →₀ ℂ) : comb τ ι₁ (c • x) f = c • comb τ ι₁ x f := by
  simp only [comb_apply, map_smul, Finsupp.smul_sum]
  exact Finsupp.sum_congr fun a _ => smul_comm _ _ _

theorem inner_comb (hs : Splitting τ ι₁ ι₂ D) {x y : V} (hx : x ∈ D) (hy : y ∈ D)
    (f f' : G₁ →₀ ℂ) : ⟪comb τ ι₁ y f', comb τ ι₁ x f⟫_ℂ =
      (f'.sum fun b β => f.sum fun a α => conj β * α * hs.coeff (b⁻¹ * a)) * ⟪y, x⟫_ℂ := by
  rw [comb_apply, comb_apply, Finsupp.sum_inner, Finsupp.sum_mul]
  refine Finsupp.sum_congr fun b _ => ?_
  rw [Finsupp.inner_sum, Finsupp.sum_mul]
  refine Finsupp.sum_congr fun a _ => ?_
  rw [inner_smul_left, inner_smul_right, τ.inner_map_left, ← UnitaryRep.map_mul_apply,
    ← map_inv ι₁, ← map_mul ι₁, hs.inner_map_eq _ hx hy]
  ring

variable {v : V}

theorem inner_comb_eq (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D) (hvn : ‖v‖ = 1) {x y : V}
    (hx : x ∈ D) (hy : y ∈ D) (f f' : G₁ →₀ ℂ) :
    ⟪comb τ ι₁ y f', comb τ ι₁ x f⟫_ℂ = ⟪comb τ ι₁ v f', comb τ ι₁ v f⟫_ℂ * ⟪y, x⟫_ℂ := by
  rw [inner_comb hs hx hy, inner_comb hs hv hv, inner_self_eq_norm_sq_to_K, hvn]
  simp

theorem norm_comb (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D) (hvn : ‖v‖ = 1) {x : V} (hx : x ∈ D)
    (f : G₁ →₀ ℂ) : ‖comb τ ι₁ x f‖ = ‖x‖ * ‖comb τ ι₁ v f‖ := by
  have h := inner_comb_eq hs hv hvn hx hx f f
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖comb τ ι₁ x f‖ ^ 2 = ‖comb τ ι₁ v f‖ ^ 2 * ‖x‖ ^ 2 := by exact_mod_cast h
  have h'' : ‖comb τ ι₁ x f‖ ^ 2 = (‖x‖ * ‖comb τ ι₁ v f‖) ^ 2 := by rw [h', mul_pow, mul_comm]
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h''

variable (τ ι₁) in

def orbitClosure (v : V) : Submodule ℂ V :=
  (Submodule.span ℂ (range fun a => τ (ι₁ a) v)).topologicalClosure

instance (v : V) : CompleteSpace (orbitClosure τ ι₁ v) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem isClosed_orbitClosure (v : V) : IsClosed (orbitClosure τ ι₁ v : Set V) :=
  Submodule.isClosed_topologicalClosure _

theorem range_comb (x : V) :
    LinearMap.range (comb τ ι₁ x) = Submodule.span ℂ (range fun a => τ (ι₁ a) x) :=
  Finsupp.range_linearCombination ℂ

theorem comb_mem_orbitClosure (v : V) (f : G₁ →₀ ℂ) : comb τ ι₁ v f ∈ orbitClosure τ ι₁ v :=
  Submodule.le_topologicalClosure _ (range_comb (τ := τ) (ι₁ := ι₁) v ▸ LinearMap.mem_range_self _ f)

theorem mem_orbitClosure (v : V) (a : G₁) : τ (ι₁ a) v ∈ orbitClosure τ ι₁ v :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a, rfl⟩)

variable (τ ι₁) in

def combW (v : V) : (G₁ →₀ ℂ) →ₗ[ℂ] orbitClosure τ ι₁ v :=
  (comb τ ι₁ v).codRestrict _ (comb_mem_orbitClosure v)

@[simp] theorem coe_combW (v : V) (f : G₁ →₀ ℂ) : (combW τ ι₁ v f : V) = comb τ ι₁ v f := rfl

theorem denseRange_combW (v : V) : DenseRange (combW τ ι₁ v) := by
  intro w
  have h2 : (w : V) ∈ closure ((Submodule.span ℂ (range fun a => τ (ι₁ a) v) : Submodule ℂ V) :
      Set V) := by
    rw [← Submodule.topologicalClosure_coe]; exact w.2
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage]
  convert h2 using 2
  rw [← range_comb, LinearMap.coe_range, ← Set.range_comp]
  rfl

variable (τ ι₁) in

def tensorMap (v x : V) : orbitClosure τ ι₁ v →L[ℂ] V :=
  (comb τ ι₁ x).extendOfNorm (combW τ ι₁ v)

theorem tensorMap_combW (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D) (hvn : ‖v‖ = 1) {x : V}
    (hx : x ∈ D) (f : G₁ →₀ ℂ) : tensorMap τ ι₁ v x (combW τ ι₁ v f) = comb τ ι₁ x f :=
  LinearMap.extendOfNorm_eq (denseRange_combW v) ⟨‖x‖, fun f => (norm_comb hs hv hvn hx f).le⟩ f

theorem inner_tensorMap (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D) (hvn : ‖v‖ = 1) {x y : V}
    (hx : x ∈ D) (hy : y ∈ D) (w w' : orbitClosure τ ι₁ v) :
    ⟪tensorMap τ ι₁ v y w', tensorMap τ ι₁ v x w⟫_ℂ = ⟪(w' : V), (w : V)⟫_ℂ * ⟪y, x⟫_ℂ := by
  refine (denseRange_combW v).induction_on₂ (p := fun w' w =>
    ⟪tensorMap τ ι₁ v y w', tensorMap τ ι₁ v x w⟫_ℂ = ⟪(w' : V), (w : V)⟫_ℂ * ⟪y, x⟫_ℂ) ?_ ?_ w' w
  · exact isClosed_eq (((tensorMap τ ι₁ v y).continuous.comp continuous_fst).inner
      ((tensorMap τ ι₁ v x).continuous.comp continuous_snd))
      (((continuous_subtype_val.comp continuous_fst).inner
        (continuous_subtype_val.comp continuous_snd)).mul continuous_const)
  · intro f' f
    rw [tensorMap_combW hs hv hvn hy, tensorMap_combW hs hv hvn hx, inner_comb_eq hs hv hvn hx hy]
    rfl

theorem norm_tensorMap (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D) (hvn : ‖v‖ = 1) {x : V}
    (hx : x ∈ D) (w : orbitClosure τ ι₁ v) : ‖tensorMap τ ι₁ v x w‖ = ‖x‖ * ‖w‖ := by
  have h := inner_tensorMap hs hv hvn hx hx w w
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖tensorMap τ ι₁ v x w‖ ^ 2 = ‖(w : V)‖ ^ 2 * ‖x‖ ^ 2 := by exact_mod_cast h
  have h'' : ‖tensorMap τ ι₁ v x w‖ ^ 2 = (‖x‖ * ‖w‖) ^ 2 := by
    rw [h', mul_pow, mul_comm]; rfl
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h''

theorem tensorMap_add (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D) (hvn : ‖v‖ = 1) {x y : V}
    (hx : x ∈ D) (hy : y ∈ D) :
    tensorMap τ ι₁ v (x + y) = tensorMap τ ι₁ v x + tensorMap τ ι₁ v y := by
  refine LinearMap.extendOfNorm_unique (denseRange_combW v) ‖x + y‖
    (fun f => (norm_comb hs hv hvn (D.add_mem hx hy) f).le) _ ?_
  refine LinearMap.ext fun f => ?_
  show tensorMap τ ι₁ v x (combW τ ι₁ v f) + tensorMap τ ι₁ v y (combW τ ι₁ v f) = _
  rw [tensorMap_combW hs hv hvn hx, tensorMap_combW hs hv hvn hy, comb_add]

theorem tensorMap_smul (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D) (hvn : ‖v‖ = 1) {x : V}
    (hx : x ∈ D) (c : ℂ) : tensorMap τ ι₁ v (c • x) = c • tensorMap τ ι₁ v x := by
  refine LinearMap.extendOfNorm_unique (denseRange_combW v) ‖c • x‖
    (fun f => (norm_comb hs hv hvn (D.smul_mem c hx) f).le) _ ?_
  refine LinearMap.ext fun f => ?_
  show c • tensorMap τ ι₁ v x (combW τ ι₁ v f) = _
  rw [tensorMap_combW hs hv hvn hx, comb_smul]

def tensorMapLin (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D) (hvn : ‖v‖ = 1) :
    D →ₗ[ℂ] (orbitClosure τ ι₁ v →L[ℂ] V) where
  toFun x := tensorMap τ ι₁ v x
  map_add' x y := tensorMap_add hs hv hvn x.2 y.2
  map_smul' c x := tensorMap_smul hs hv hvn x.2 c

def tensorMapL (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D) (hvn : ‖v‖ = 1) :
    D →L[ℂ] (orbitClosure τ ι₁ v →L[ℂ] V) where
  toLinearMap := tensorMapLin hs hv hvn
  cont := AddMonoidHomClass.continuous_of_bound (tensorMapLin hs hv hvn) 1 fun x => by
    show ‖tensorMap τ ι₁ v (x : V)‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w =>
      (norm_tensorMap hs hv hvn x.2 w).le

@[simp] theorem tensorMapL_apply (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D) (hvn : ‖v‖ = 1) (x : D)
    (w : orbitClosure τ ι₁ v) : tensorMapL hs hv hvn x w = tensorMap τ ι₁ v x w := rfl

theorem self_mem_orbitClosure (v : V) : v ∈ orbitClosure τ ι₁ v := by
  simpa using mem_orbitClosure (τ := τ) (ι₁ := ι₁) v 1

theorem map_mem_orbitClosure (a : G₁) {w : V} (hw : w ∈ orbitClosure τ ι₁ v) :
    τ (ι₁ a) w ∈ orbitClosure τ ι₁ v := by
  have hle : Submodule.span ℂ (range fun b => τ (ι₁ b) v) ≤
      (orbitClosure τ ι₁ v).comap ((τ (ι₁ a) : V →L[ℂ] V) : V →ₗ[ℂ] V) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe]
    rw [← UnitaryRep.map_mul_apply, ← map_mul]
    exact mem_orbitClosure v (a * b)
  exact Submodule.topologicalClosure_minimal _ hle
    ((isClosed_orbitClosure v).preimage (τ (ι₁ a)).continuous) hw

variable (τ ι₁) in

def repW (hι₁ : Continuous ι₁) (v : V) : UnitaryRep G₁ (orbitClosure τ ι₁ v) :=
  (τ.compHom ι₁ hι₁).restrict (orbitClosure τ ι₁ v) (fun a _ hw => map_mem_orbitClosure a hw)

@[simp] theorem coe_repW_apply (hι₁ : Continuous ι₁) (v : V) (a : G₁) (w : orbitClosure τ ι₁ v) :
    ((repW τ ι₁ hι₁ v a w : orbitClosure τ ι₁ v) : V) = τ (ι₁ a) w := rfl

def repD (hs : Splitting τ ι₁ ι₂ D) (hι₂ : Continuous ι₂) : UnitaryRep G₂ D :=
  (τ.compHom ι₂ hι₂).restrict D (fun b _ hx => hs.mem₂ b hx)

@[simp] theorem coe_repD_apply (hs : Splitting τ ι₁ ι₂ D) (hι₂ : Continuous ι₂) (b : G₂) (x : D) :
    ((repD hs hι₂ b x : D) : V) = τ (ι₂ b) x := rfl

theorem comb_mapDomain (a : G₁) (x : V) (f : G₁ →₀ ℂ) :
    comb τ ι₁ x (f.mapDomain (a * ·)) = τ (ι₁ a) (comb τ ι₁ x f) := by
  rw [comb_apply, comb_apply, Finsupp.sum_mapDomain_index
    (h := fun b (β : ℂ) => β • τ (ι₁ b) x) (fun _ => zero_smul _ _)
    (fun _ _ _ => add_smul _ _ _), map_finsuppSum]
  refine Finsupp.sum_congr fun b _ => ?_
  rw [map_smul, map_mul, UnitaryRep.map_mul_apply]

theorem tensorMap_repW (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D) (hvn : ‖v‖ = 1)
    (hι₁ : Continuous ι₁) {x : V} (hx : x ∈ D) (a : G₁) (w : orbitClosure τ ι₁ v) :
    tensorMap τ ι₁ v x (repW τ ι₁ hι₁ v a w) = τ (ι₁ a) (tensorMap τ ι₁ v x w) := by
  refine (denseRange_combW v).induction_on w (isClosed_eq
    ((tensorMap τ ι₁ v x).continuous.comp (repW τ ι₁ hι₁ v a).continuous)
    ((τ (ι₁ a)).continuous.comp (tensorMap τ ι₁ v x).continuous)) fun f => ?_
  have e : repW τ ι₁ hι₁ v a (combW τ ι₁ v f) = combW τ ι₁ v (f.mapDomain (a * ·)) :=
    Subtype.ext (comb_mapDomain a v f).symm
  rw [e, tensorMap_combW hs hv hvn hx, tensorMap_combW hs hv hvn hx, comb_mapDomain]

theorem map_tensorMap (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D) (hvn : ‖v‖ = 1) {x : V}
    (hx : x ∈ D) (b : G₂) (w : orbitClosure τ ι₁ v) :
    τ (ι₂ b) (tensorMap τ ι₁ v x w) = tensorMap τ ι₁ v (τ (ι₂ b) x) w := by
  refine (denseRange_combW v).induction_on w (isClosed_eq
    ((τ (ι₂ b)).continuous.comp (tensorMap τ ι₁ v x).continuous)
    (tensorMap τ ι₁ v _).continuous) fun f => ?_
  rw [tensorMap_combW hs hv hvn hx, tensorMap_combW hs hv hvn (hs.mem₂ b hx), comb_apply,
    comb_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun a _ => ?_
  rw [map_smul, ← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, hs.comm]

theorem map_mul_tensorMap (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D) (hvn : ‖v‖ = 1)
    (hι₁ : Continuous ι₁) {x : V} (hx : x ∈ D) (a : G₁) (b : G₂) (w : orbitClosure τ ι₁ v) :
    τ (ι₁ a * ι₂ b) (tensorMap τ ι₁ v x w) =
      tensorMap τ ι₁ v (τ (ι₂ b) x) (repW τ ι₁ hι₁ v a w) := by
  rw [UnitaryRep.map_mul_apply, map_tensorMap hs hv hvn hx,
    tensorMap_repW hs hv hvn hι₁ (hs.mem₂ b hx)]

theorem tensorMap_self (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D) (hvn : ‖v‖ = 1)
    (w : orbitClosure τ ι₁ v) : tensorMap τ ι₁ v v w = w := by
  refine (denseRange_combW v).induction_on w
    (isClosed_eq (tensorMap τ ι₁ v v).continuous continuous_subtype_val) fun f => ?_
  rw [tensorMap_combW hs hv hvn hv]
  rfl

theorem eq_smul_of_mem_window_orbitClosure (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D)
    (hvn : ‖v‖ = 1) {y : V} (hyD : y ∈ D) (hyW : y ∈ orbitClosure τ ι₁ v) :
    y = ⟪v, y⟫_ℂ • v := by
  set y' := y - ⟪v, y⟫_ℂ • v with hy'
  have hy'D : y' ∈ D := D.sub_mem hyD (D.smul_mem _ hv)
  have hy'W : y' ∈ orbitClosure τ ι₁ v :=
    (orbitClosure τ ι₁ v).sub_mem hyW ((orbitClosure τ ι₁ v).smul_mem _ (self_mem_orbitClosure v))
  have hortho : ⟪y', v⟫_ℂ = 0 := by
    simp [y', inner_self_eq_norm_sq_to_K, hvn]
  have hle : orbitClosure τ ι₁ v ≤ (ℂ ∙ y')ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right,
      hs.inner_map_eq a hv hy'D, hortho, mul_zero]
  have h := hle hy'W
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero, hy',
    sub_eq_zero] at h
  exact h

theorem isIrreducible_repW (hs : Splitting τ ι₁ ι₂ D) (hv : v ∈ D) (hvn : ‖v‖ = 1)
    (hι₁ : Continuous ι₁) : (repW τ ι₁ hι₁ v).IsIrreducible := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hvn
  refine ⟨⟨⟨⟨v, self_mem_orbitClosure v⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩,
    fun U' hU' hinv => ?_⟩
  set U : Submodule ℂ V := U'.map (orbitClosure τ ι₁ v).subtype with hU
  have hUc : IsClosed (U : Set V) := by
    have e : (U : Set V) = Subtype.val '' (U' : Set (orbitClosure τ ι₁ v)) := by
      rw [hU, Submodule.map_coe]; rfl
    rw [e]
    exact (isClosed_orbitClosure v).isClosedEmbedding_subtypeVal.isClosedMap _ hU'
  have : CompleteSpace U := hUc.completeSpace_coe
  have hUinv : (τ.compHom ι₁ hι₁).IsInvariant U := by
    rintro a _ ⟨u, hu, rfl⟩
    exact ⟨repW τ ι₁ hι₁ v a u, hinv a u hu, rfl⟩
  have hP := ((τ.compHom ι₁ hι₁).isInvariant_iff_commute_starProjection U).1 hUinv
  have hPv : U.starProjection v ∈ D := hs.inv _ (fun a => (hP a).symm) v hv
  have hPvW : U.starProjection v ∈ orbitClosure τ ι₁ v := by
    obtain ⟨u, -, hu⟩ := U.starProjection_apply_mem v
    rw [← hu]; exact u.2
  obtain ⟨t, ht⟩ : ∃ t : ℂ, U.starProjection v = t • v :=
    ⟨_, eq_smul_of_mem_window_orbitClosure hs hv hvn hPv hPvW⟩
  have htt : t * t = t := by
    have h1 : U.starProjection (U.starProjection v) = U.starProjection v :=
      Submodule.starProjection_eq_self_iff.2 (U.starProjection_apply_mem v)
    rw [ht, map_smul, ht, smul_smul] at h1
    have h2 : (t * t - t) • v = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hv0)
  have ht01 : t = 0 ∨ t = 1 := by
    have : t * (t - 1) = 0 := by rw [mul_sub, htt, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  rcases ht01 with rfl | rfl
  ·
    left
    have hvU : v ∈ Uᗮ := (Submodule.starProjection_apply_eq_zero_iff U).1 (by rw [ht, zero_smul])
    have hinvo := hUinv.orthogonal
    have hle : orbitClosure τ ι₁ v ≤ Uᗮ := by
      refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact hinvo a v hvU
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_bot]
    have h1 : (u : V) ∈ U := ⟨u, hu, rfl⟩
    have h2 : (u : V) ∈ Uᗮ := hle u.2
    have h3 := Submodule.inner_right_of_mem_orthogonal h1 h2
    rw [inner_self_eq_zero] at h3
    exact Subtype.ext h3
  ·
    right
    have hvU : v ∈ U := Submodule.starProjection_eq_self_iff.1 (by rw [ht, one_smul])
    have hle : orbitClosure τ ι₁ v ≤ U := by
      refine Submodule.topologicalClosure_minimal _ ?_ hUc
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact hUinv a v hvU
    rw [eq_top_iff]
    intro w _
    obtain ⟨u, hu, hwu⟩ := hle w.2
    have : u = w := Subtype.ext hwu
    rwa [← this]

theorem isIrreducible_repD (hs : Splitting τ ι₁ ι₂ D) (hι₂ : Continuous ι₂) :
    (repD hs hι₂).IsIrreducible := by
  refine ⟨hs.nontrivial, fun U hU hinv => window_irreducible hs U hU (fun a x hx => ?_)
    (fun b x hx => hinv b x hx)⟩
  rw [hs.compr_eq]
  simpa using U.smul_mem (hs.coeff a) hx

end GL2ProductCompleteness

end

end GroundTheory.Automorphic
