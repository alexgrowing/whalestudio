import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJZetaDefs
import GroundTheory.AutomorphicForms.GL2.ExistsEqPowMulOfValuationLe
import GroundTheory.AutomorphicForms.GL2.GJLeviSupport
import GroundTheory.AutomorphicForms.LeviStagesProduct
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

section Orders

theorem det_mem_integer_of_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι F}
    (h : ∀ i j, A i j ∈ 𝒪[F]) : A.det ∈ 𝒪[F] := by
  rw [Matrix.det_apply]
  refine Subring.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact Subring.zsmul_mem _ (Subring.prod_mem _ fun i _ => h _ _) _

theorem ord_nonneg_of_mem {x : F} (hx : x ≠ 0) (h : x ∈ 𝒪[F]) : 0 ≤ LocalField.ord x := by
  rw [← LocalField.mem_valBall_iff_le_ord hx, LocalField.mem_valBall_zero_iff]
  exact h

theorem ord_eq_zero_of_mul_eq_one {x y : F} (hxy : x * y = 1) (hx : x ∈ 𝒪[F]) (hy : y ∈ 𝒪[F]) :
    LocalField.ord x = 0 := by
  have hx0 : x ≠ 0 := left_ne_zero_of_mul_eq_one hxy
  have hy0 : y ≠ 0 := right_ne_zero_of_mul_eq_one hxy
  have h1 := ord_nonneg_of_mem hx0 hx
  have h2 := ord_nonneg_of_mem hy0 hy
  have h3 : LocalField.ord x + LocalField.ord y = 0 := by
    rw [← LocalField.ord_mul hx0 hy0, hxy]
    simp [LocalField.ord]
  omega

theorem ord_zpow_uniformizer (k : ℤ) : LocalField.ord ((uniformizer F : F) ^ k) = k := by
  rw [LocalField.ord_zpow (Cartan.uniformizer_ne_zero F),
    LocalField.ord_uniformizer (irreducible_uniformizer F), mul_one]

theorem ord_prod {ι : Type*} (s : Finset ι) {f : ι → F} (hf : ∀ i ∈ s, f i ≠ 0) :
    LocalField.ord (∏ i ∈ s, f i) = ∑ i ∈ s, LocalField.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [LocalField.ord_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      LocalField.ord_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem det_ne_zero_of_GL {ι : Type*} [Fintype ι] [DecidableEq ι] (g : GL ι F) :
    (g : Matrix ι ι F).det ≠ 0 := by
  intro h
  have : (g : Matrix ι ι F).det * ((g⁻¹ : GL ι F) : Matrix ι ι F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem ord_det_eq_zero_of_integral {ι : Type*} [Fintype ι] [DecidableEq ι] (g : GL ι F)
    (h₁ : ∀ i j, (g : Matrix ι ι F) i j ∈ 𝒪[F])
    (h₂ : ∀ i j, ((g⁻¹ : GL ι F) : Matrix ι ι F) i j ∈ 𝒪[F]) :
    LocalField.ord (g : Matrix ι ι F).det = 0 :=
  ord_eq_zero_of_mul_eq_one
    (by rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one])
    (det_mem_integer_of_fintype h₁) (det_mem_integer_of_fintype h₂)

end Orders

section OrdDet

theorem ordDet_one : ordDet (1 : GL (Fin n) F) = 0 := by
  simp [ordDet, LocalField.ord_one]

theorem ordDet_inv (g : GL (Fin n) F) : ordDet g⁻¹ = -ordDet g := by
  have := ordDet_mul g g⁻¹
  rw [mul_inv_cancel, ordDet_one] at this
  omega

theorem ordDet_diagPow (μ : Fin n → ℤ) : ordDet (Cartan.diagPow F n μ) = ∑ i, μ i := by
  rw [ordDet, Cartan.coe_diagPow, Matrix.det_diagonal,
    ord_prod _ fun i _ => zpow_ne_zero _ (Cartan.uniformizer_ne_zero F)]
  exact Finset.sum_congr rfl fun i _ => ord_zpow_uniformizer (μ i)

end OrdDet

section Blocks

def blockIndicator (b : Set.range β) (i : Fin n) : ℤ := if blockOf β i = b then 1 else 0

theorem blockIndicator_const (b : Set.range β) {i j : Fin n} (h : β i = β j) :
    blockIndicator b i = blockIndicator b j := by
  have : blockOf β i = blockOf β j := Subtype.ext h
  simp only [blockIndicator, this]

variable (F) in

def blockUnif (b : Set.range β) : levi F n β :=
  ⟨Cartan.diagPow F n (blockIndicator b), diagPow_mem_levi _⟩

theorem blockUnif_mem_center (b : Set.range β) :
    blockUnif F b ∈ Submonoid.center (levi F n β) :=
  diagPow_mem_center (c := blockIndicator b) fun _ _ h => blockIndicator_const b h

theorem blockUnif_commute (b : Set.range β) (m : levi F n β) :
    blockUnif F b * m = m * blockUnif F b :=
  ((Submonoid.mem_center_iff.1 (blockUnif_mem_center b)) m).symm

theorem ordDet_blockUnif (b : Set.range β) :
    ordDet ((blockUnif F b : levi F n β) : GL (Fin n) F) = blockSize β b := by
  rw [blockUnif, ordDet_diagPow]
  simp only [blockIndicator]
  rw [Finset.sum_boole, blockSize]
  congr 1
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun i => by simp)

variable (F) in

def blockOrd (b : Set.range β) (m : levi F n β) : ℤ :=
  LocalField.ord ((leviBlock F m b : GL (Fiber β b) F) : Matrix (Fiber β b) (Fiber β b) F).det

theorem leviBlock_mul (m m' : levi F n β) (b : Set.range β) :
    leviBlock F (m * m') b = leviBlock F m b * leviBlock F m' b :=
  congrFun ((leviEquivBlocks F β).map_mul m m') b

theorem leviBlock_inv (m : levi F n β) (b : Set.range β) :
    leviBlock F m⁻¹ b = (leviBlock F m b)⁻¹ :=
  congrFun (map_inv (leviEquivBlocks F β) m) b

theorem blockOrd_mul (b : Set.range β) (m m' : levi F n β) :
    blockOrd F b (m * m') = blockOrd F b m + blockOrd F b m' := by
  rw [blockOrd, blockOrd, blockOrd, leviBlock_mul, Units.val_mul, Matrix.det_mul,
    LocalField.ord_mul (det_ne_zero_of_GL _) (det_ne_zero_of_GL _)]

theorem blockOrd_one (b : Set.range β) : blockOrd F b (1 : levi F n β) = 0 := by
  have := blockOrd_mul (F := F) b 1 1
  rw [mul_one] at this
  omega

theorem blockOrd_inv (b : Set.range β) (m : levi F n β) :
    blockOrd F b m⁻¹ = -blockOrd F b m := by
  have := blockOrd_mul (F := F) b m m⁻¹
  rw [mul_inv_cancel, blockOrd_one] at this
  omega

theorem blockOrd_pow (b : Set.range β) (m : levi F n β) (j : ℕ) :
    blockOrd F b (m ^ j) = j * blockOrd F b m := by
  induction j with
  | zero => simp [blockOrd_one]
  | succ j ih => rw [pow_succ, blockOrd_mul, ih]; push_cast; ring

theorem blockOrd_of_mem_integralGL (b : Set.range β) {k : levi F n β}
    (hk : (k : GL (Fin n) F) ∈ integralGL F n) : blockOrd F b k = 0 := by
  obtain ⟨h₁, h₂⟩ := (mem_integralGL_iff F n).1 hk
  refine ord_det_eq_zero_of_integral _ (fun i j => h₁ i.1 j.1) fun i j => ?_
  rw [← leviBlock_inv]
  exact h₂ i.1 j.1

theorem blockOrd_diagPow (b : Set.range β) (μ : Fin n → ℤ) :
    blockOrd F b (⟨Cartan.diagPow F n μ, diagPow_mem_levi μ⟩ : levi F n β) =
      ∑ i : Fiber β b, μ i.1 := by
  have hmat : ((leviBlock F (⟨Cartan.diagPow F n μ, diagPow_mem_levi μ⟩ : levi F n β) b :
      GL (Fiber β b) F) : Matrix (Fiber β b) (Fiber β b) F) =
      Matrix.diagonal fun i : Fiber β b => (uniformizer F : F) ^ μ i.1 := by
    rw [coe_leviBlock]
    ext i j
    simp only [blocks, Cartan.coe_diagPow, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (fun e => h (Subtype.ext e)), if_neg h]
  rw [blockOrd, hmat, Matrix.det_diagonal,
    ord_prod _ fun i _ => zpow_ne_zero _ (Cartan.uniformizer_ne_zero F)]
  exact Finset.sum_congr rfl fun i _ => ord_zpow_uniformizer (μ i.1)

theorem blockOrd_blockUnif (b b' : Set.range β) :
    blockOrd F b' (blockUnif F b) = if b' = b then (blockSize β b : ℤ) else 0 := by
  rw [blockUnif, blockOrd_diagPow]
  have : ∀ i : Fiber β b', blockIndicator b i.1 = if b' = b then 1 else 0 := by
    intro i
    simp only [blockIndicator, i.2]
  simp only [this, Finset.sum_ite_irrel, Finset.sum_const_zero]
  split_ifs with h
  · subst h
    simp [blockSize]
  · rfl

theorem blockOrd_cartan (b : Set.range β) {m : levi F n β} {μ : Fin n → ℤ}
    {k₁ k₂ : GL (Fin n) F} (hk₁ : k₁ ∈ levi F n β ⊓ integralGL F n)
    (hk₂ : k₂ ∈ levi F n β ⊓ integralGL F n)
    (hm : (m : GL (Fin n) F) = k₁ * Cartan.diagPow F n μ * k₂) :
    blockOrd F b m = ∑ i : Fiber β b, μ i.1 := by
  have hm' : m = ⟨k₁, hk₁.1⟩ * ⟨Cartan.diagPow F n μ, diagPow_mem_levi μ⟩ * ⟨k₂, hk₂.1⟩ :=
    Subtype.ext hm
  rw [hm', blockOrd_mul, blockOrd_mul, blockOrd_of_mem_integralGL (k := ⟨k₁, hk₁.1⟩) b hk₁.2,
    blockOrd_of_mem_integralGL (k := ⟨k₂, hk₂.1⟩) b hk₂.2, blockOrd_diagPow, zero_add, add_zero]

theorem ordDet_eq_sum_blockOrd (m : levi F n β) :
    ordDet (m : GL (Fin n) F) = ∑ b : Set.range β, blockOrd F b m := by
  obtain ⟨μ, k₁, hk₁, k₂, hk₂, hm⟩ := exists_eq_mul_diagPow_mul_levi m.2
  rw [Finset.sum_congr rfl fun b _ => blockOrd_cartan b hk₁ hk₂ hm, hm, ordDet_mul, ordDet_mul,
    ordDet_of_mem_integralGL hk₁.2, ordDet_of_mem_integralGL hk₂.2, ordDet_diagPow, zero_add,
    add_zero]
  have e1 := Fintype.sum_equiv (Equiv.sigmaFiberEquiv (blockOf β)) (fun x => μ x.2.1) μ
    (fun _ => rfl)
  rw [← e1, Fintype.sum_sigma]

def zeroBlock (b : Set.range β) (X : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  fun i j => if blockOf β i = b then 0 else X i j

end Blocks

section LocallyConstant

variable (F n β) in

def leviIntegral : Subgroup (levi F n β) := (integralGL F n).subgroupOf (levi F n β)

theorem isOpen_leviIntegral : IsOpen (leviIntegral F n β : Set (levi F n β)) :=
  isOpen_subgroupOf_levi (isOpen_integralGL F n)

theorem isCompact_leviIntegral : IsCompact (leviIntegral F n β : Set (levi F n β)) :=
  isCompact_subgroupOf_levi (isCompact_integralGL F n)

theorem isLocallyConstant_of_forall_mul {X : Type*} {f : levi F n β → X}
    (h : ∀ m, ∃ V : Subgroup (levi F n β), IsOpen (V : Set (levi F n β)) ∧ ∀ k ∈ V, f (m * k) = f m) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro m
  obtain ⟨V, hVo, hV⟩ := h m
  refine ⟨(fun x => m⁻¹ * x) ⁻¹' V, hVo.preimage (continuous_const.mul continuous_id), ?_,
    fun x hx => ?_⟩
  · show m⁻¹ * m ∈ V
    rw [inv_mul_cancel]
    exact V.one_mem
  · have := hV _ hx
    rwa [mul_inv_cancel_left] at this

theorem isLocallyConstant_blockOrd (b : Set.range β) : IsLocallyConstant (blockOrd F b) :=
  isLocallyConstant_of_forall_mul fun m => ⟨leviIntegral F n β, isOpen_leviIntegral, fun k hk => by
    rw [blockOrd_mul, blockOrd_of_mem_integralGL b (Subgroup.mem_subgroupOf.1 hk), add_zero]⟩

theorem isLocallyConstant_ordDet :
    IsLocallyConstant fun m : levi F n β => ordDet (m : GL (Fin n) F) :=
  isLocallyConstant_of_forall_mul fun m => ⟨leviIntegral F n β, isOpen_leviIntegral, fun k hk => by
    show ordDet (((m * k : levi F n β) : GL (Fin n) F)) = _
    rw [Subgroup.coe_mul, ordDet_mul, ordDet_of_mem_integralGL (Subgroup.mem_subgroupOf.1 hk), add_zero]⟩

theorem isLocallyConstant_detPow (s : ℂ) :
    IsLocallyConstant fun m : levi F n β => detPow (m : GL (Fin n) F) s := by
  have : (fun m : levi F n β => detPow (m : GL (Fin n) F) s) =
      (fun k : ℤ => qs F s ^ k) ∘ fun m : levi F n β => ordDet (m : GL (Fin n) F) := by
    funext m
    exact detPow_eq_qs_zpow _ s
  rw [this]
  exact isLocallyConstant_ordDet.comp _

theorem isLocallyConstant_coeff {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (levi F n β) W} (hσ : IsSmooth σ) (w : W) (ℓ : Module.Dual ℂ W) :
    IsLocallyConstant fun m : levi F n β => ℓ (σ m w) :=
  isLocallyConstant_of_forall_mul fun m => ⟨stabilizerOf σ w, hσ w, fun k hk => by
    show ℓ (σ (m * k) w) = ℓ (σ m w)
    rw [map_mul, Module.End.mul_apply, mem_stabilizerOf.1 hk]⟩

theorem exists_eq_pow_mul_iff {r : ℕ} {y : F} :
    (∃ a ∈ 𝒪[F], y = (uniformizer F : F) ^ r * a) ↔
      (uniformizer F : F) ^ (-(r : ℤ)) * y ∈ 𝒪[F] := by
  have hϖ := Cartan.uniformizer_ne_zero F
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [← mul_assoc, _root_.zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hϖ), one_mul]
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← mul_assoc, _root_.zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ hϖ), one_mul]

theorem isOpen_small (r : ℕ) (c : F) :
    IsOpen {x : F | (uniformizer F : F) ^ (-(r : ℤ)) * (x - c) ∈ 𝒪[F]} :=
  (show IsOpen (𝒪[F] : Set F) from Valuation.isOpen_integer).preimage ((continuous_id.sub continuous_const).const_mul _)

theorem IsLeviSchwartz.isLocallyConstant {Ψ : Matrix (Fin n) (Fin n) F → ℂ}
    (hΨ : IsLeviSchwartz β Ψ) :
    IsLocallyConstant fun m : levi F n β => Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨r, A, hinv, -⟩ := hΨ
  rw [IsLocallyConstant.iff_exists_open]
  intro m
  refine ⟨⋂ i, ⋂ j, (fun x : levi F n β => (x : GL (Fin n) F) i j) ⁻¹'
      {x : F | (uniformizer F : F) ^ (-(r : ℤ)) * (x - (m : GL (Fin n) F) i j) ∈ 𝒪[F]},
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_small r _).preimage ((continuous_entry F n i j).comp continuous_subtype_val),
    ?_, fun x hx => ?_⟩
  · simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq, sub_self, mul_zero]
    exact fun _ _ => (𝒪[F]).zero_mem
  · simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq] at hx
    have hx' : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) +
          (((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) -
            ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by abel
    rw [hx']
    refine hinv _ _ (mem_levi.1 m.2) (fun i j h => ?_) fun i j => exists_eq_pow_mul_iff.2 (hx i j)
    rw [Matrix.sub_apply, mem_levi.1 x.2 i j h, mem_levi.1 m.2 i j h, sub_zero]

theorem IsLeviSchwartz.exists_bound {Ψ : Matrix (Fin n) (Fin n) F → ℂ} (hΨ : IsLeviSchwartz β Ψ) :
    ∃ C : ℝ, ∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) → ‖Ψ X‖ ≤ C := by
  classical
  obtain ⟨r, A, hinv, hsupp⟩ := hΨ
  let bd : Matrix (Fin n) (Fin n) F → Matrix (Fin n) (Fin n) F :=
    fun x i j => if β i = β j then x i j else 0
  have hbd : ∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) → bd X = X := by
    intro X hX
    funext i j
    by_cases h : β i = β j
    · simp [bd, h]
    · simp [bd, h, hX i j h]
  let φ : Matrix (Fin n) (Fin n) F → ℂ := fun x => Ψ (bd x)
  have hφ : IsLocallyConstant φ := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨⋂ i, ⋂ j, (fun y : Matrix (Fin n) (Fin n) F => y i j) ⁻¹'
        {a : F | (uniformizer F : F) ^ (-(r : ℤ)) * (a - x i j) ∈ 𝒪[F]},
      isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (isOpen_small r _).preimage ((continuous_apply j).comp (continuous_apply i)), ?_,
      fun y hy => ?_⟩
    · simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq, sub_self, mul_zero]
      exact fun _ _ => (𝒪[F]).zero_mem
    · simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq] at hy
      have : bd y = bd x + (bd y - bd x) := by abel
      show Ψ (bd y) = Ψ (bd x)
      rw [this]
      refine hinv _ _ (fun i j h => by simp [bd, h]) (fun i j h => ?_)
        fun i j => exists_eq_pow_mul_iff.2 ?_
      · show bd y i j - bd x i j = 0
        simp [bd, h]
      · show (uniformizer F : F) ^ (-(r : ℤ)) * (bd y i j - bd x i j) ∈ 𝒪[F]
        by_cases h : β i = β j
        · simpa [bd, h] using hy i j
        · simp [bd, h]
  let S : Set F := {a | (uniformizer F : F) ^ A * a ∈ 𝒪[F]}
  have hS : IsCompact S := by
    have h𝒪 : IsCompact (𝒪[F] : Set F) :=
      isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[F]))
    have : S = (fun a => ((uniformizer F : F) ^ A)⁻¹ * a) '' (𝒪[F] : Set F) := by
      ext a
      simp only [S, Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe]
      constructor
      · intro ha
        exact ⟨_, ha, by
          rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (Cartan.uniformizer_ne_zero F)), one_mul]⟩
      · rintro ⟨b, hb, rfl⟩
        rwa [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (Cartan.uniformizer_ne_zero F)), one_mul]
    rw [this]
    exact h𝒪.image (continuous_const.mul continuous_id)
  let K : Set (Matrix (Fin n) (Fin n) F) := Set.univ.pi fun _ => Set.univ.pi fun _ => S
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hS
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφ.continuous.continuousOn
  refine ⟨max C 0, fun X hX => ?_⟩
  by_cases h0 : Ψ X = 0
  · rw [h0, norm_zero]
    exact le_max_right _ _
  · have hXK : X ∈ K :=
      Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => hsupp X hX h0 i j
    have := hC X hXK
    simp only [φ, hbd X hX] at this
    exact this.trans (le_max_left _ _)

end LocallyConstant

section Support

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

theorem exists_cartan_of_coeff_ne_zero (hσ : IsSmooth σ) (hc : IsCuspidal σ) (w : W)
    {ℓ : Module.Dual ℂ W} (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) :
    ∃ N : ℕ, ∀ m : levi F n β, ℓ (σ m w) ≠ 0 →
      ∃ (μ c : Fin n → ℤ) (k₁ k₂ : GL (Fin n) F), k₁ ∈ levi F n β ⊓ integralGL F n ∧
        k₂ ∈ levi F n β ⊓ integralGL F n ∧ (m : GL (Fin n) F) = k₁ * Cartan.diagPow F n μ * k₂ ∧
        (∀ i j, β i = β j → c i = c j) ∧ ∀ i, c i ≤ μ i ∧ μ i ≤ c i + N := by
  obtain ⟨N, hN⟩ := exists_bound_of_coeff_ne_zero hσ hc w hℓ
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨μ, k₁, hk₁, k₂, hk₂, hmk⟩ := exists_eq_mul_diagPow_mul_levi m.2
  have hm' : m = ⟨k₁, hk₁.1⟩ * ⟨Cartan.diagPow F n μ, diagPow_mem_levi μ⟩ * ⟨k₂, hk₂.1⟩ :=
    Subtype.ext hmk
  rw [hm'] at hm
  obtain ⟨c, hc1, hc2⟩ := hN μ ⟨k₁, hk₁.1⟩ ⟨k₂, hk₂.1⟩ hk₁.2 hk₂.2 hm
  exact ⟨μ, c, k₁, k₂, hk₁, hk₂, hmk, hc1, hc2⟩

theorem cartan_apply (k₁ k₂ : GL (Fin n) F) (μ : Fin n → ℤ) (i j : Fin n) :
    ((k₁ * Cartan.diagPow F n μ * k₂ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      ∑ l, (k₁ : Matrix (Fin n) (Fin n) F) i l * (uniformizer F : F) ^ μ l *
        (k₂ : Matrix (Fin n) (Fin n) F) l j := by
  rw [Units.val_mul, Units.val_mul, Cartan.coe_diagPow, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_diagonal]

theorem sum_fiber_bounds {b : Set.range β} {μ c : Fin n → ℤ} {N : ℕ}
    (hc : ∀ i j, β i = β j → c i = c j) (hμ : ∀ i, c i ≤ μ i ∧ μ i ≤ c i + N) {i : Fin n}
    (hi : blockOf β i = b) :
    (blockSize β b : ℤ) * c i ≤ ∑ l : Fiber β b, μ l.1 ∧
      ∑ l : Fiber β b, μ l.1 ≤ (blockSize β b : ℤ) * (c i + N) := by
  have hcl : ∀ l : Fiber β b, c l.1 = c i := fun l =>
    hc _ _ (congrArg Subtype.val (l.2.trans hi.symm))
  constructor
  · have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fiber β b)) (fun l => μ l.1) (c i)
      fun l _ => (hcl l) ▸ (hμ l.1).1
    simpa [blockSize, nsmul_eq_mul] using this
  · have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fiber β b)) (fun l => μ l.1)
      (c i + N) fun l _ => (hcl l) ▸ (hμ l.1).2
    simpa [blockSize, nsmul_eq_mul] using this

theorem exists_block_small (hσ : IsSmooth σ) (hc : IsCuspidal σ) (w : W)
    {ℓ : Module.Dual ℂ W} (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) :
    ∃ N : ℕ, ∀ m : levi F n β, ℓ (σ m w) ≠ 0 → ∀ (b : Set.range β) (t : ℤ),
      (blockSize β b : ℤ) * (t + N) ≤ blockOrd F b m → ∀ i j, blockOf β i = b →
        (uniformizer F : F) ^ (-t) * ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
  obtain ⟨N, hN⟩ := exists_cartan_of_coeff_ne_zero hσ hc w hℓ
  refine ⟨N, fun m hm b t ht i j hi => ?_⟩
  obtain ⟨μ, c, k₁, k₂, hk₁, hk₂, hmk, hc1, hc2⟩ := hN m hm
  have hbo := blockOrd_cartan b hk₁ hk₂ hmk
  have hb := (sum_fiber_bounds hc1 hc2 hi).2
  have hpos : (0 : ℤ) < blockSize β b := by exact_mod_cast blockSize_pos β b
  have hti : t ≤ c i := by
    have : (blockSize β b : ℤ) * (t + N) ≤ (blockSize β b : ℤ) * (c i + N) := by
      rw [← hbo] at hb; linarith
    have := le_of_mul_le_mul_left this hpos
    linarith
  obtain ⟨hk₁l, hk₁i⟩ := hk₁
  obtain ⟨-, hk₂i⟩ := hk₂
  have h1 := ((mem_integralGL_iff F n).1 hk₁i).1
  have h2 := ((mem_integralGL_iff F n).1 hk₂i).1
  rw [hmk, cartan_apply, Finset.mul_sum]
  refine Subring.sum_mem _ fun l _ => ?_
  by_cases hl : β i = β l
  · have hμl : t ≤ μ l := (hti.trans_eq (hc1 i l hl)).trans (hc2 l).1
    have : (uniformizer F : F) ^ (-t) *
        ((k₁ : Matrix (Fin n) (Fin n) F) i l * (uniformizer F : F) ^ μ l *
          (k₂ : Matrix (Fin n) (Fin n) F) l j) =
        (k₁ : Matrix (Fin n) (Fin n) F) i l * (uniformizer F : F) ^ (μ l - t) *
          (k₂ : Matrix (Fin n) (Fin n) F) l j := by
      rw [zpow_sub₀ (Cartan.uniformizer_ne_zero F), div_eq_mul_inv, ← _root_.zpow_neg]
      ring
    rw [this]
    refine Subring.mul_mem _ (Subring.mul_mem _ (h1 i l) ?_) (h2 l j)
    rw [← Int.toNat_of_nonneg (sub_nonneg.2 hμl), zpow_natCast]
    exact Subring.pow_mem _ (GLnLocal.uniformizer F).2 _
  · rw [mem_levi.1 hk₁l i l hl]
    simp

theorem exists_compact_of_coeff (hσ : IsSmooth σ) (hc : IsCuspidal σ) (w : W)
    {ℓ : Module.Dual ℂ W} (hℓ : ℓ ∈ smoothVectors (Representation.dual σ))
    (k K : Set.range β → ℤ) :
    ∃ C : Set (levi F n β), IsCompact C ∧ ∀ m : levi F n β, ℓ (σ m w) ≠ 0 →
      (∀ b, k b ≤ blockOrd F b m ∧ blockOrd F b m ≤ K b) → m ∈ C := by
  classical
  obtain ⟨N, hN⟩ := exists_cartan_of_coeff_ne_zero hσ hc w hℓ
  set L : ℤ := ∑ b, (|k b| + |K b|) + N with hL
  let S : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-L) L
  let C : Set (levi F n β) := ⋃ μ ∈ S, (fun p : levi F n β × levi F n β =>
      p.1 * ⟨Cartan.diagPow F n μ, diagPow_mem_levi μ⟩ * p.2) ''
        ((leviIntegral F n β : Set (levi F n β)) ×ˢ (leviIntegral F n β : Set (levi F n β)))
  refine ⟨C, S.finite_toSet.isCompact_biUnion fun μ _ =>
      (isCompact_leviIntegral.prod isCompact_leviIntegral).image
        ((continuous_fst.mul continuous_const).mul continuous_snd), fun m hm hbd => ?_⟩
  obtain ⟨μ, c, k₁, k₂, hk₁, hk₂, hmk, hc1, hc2⟩ := hN m hm
  have hμS : μ ∈ S := by
    simp only [S, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    set b := blockOf β i
    have hbo := blockOrd_cartan b hk₁ hk₂ hmk
    obtain ⟨hlo, hhi⟩ := sum_fiber_bounds hc1 hc2 (rfl : blockOf β i = b)
    rw [← hbo] at hlo hhi
    obtain ⟨hkb, hKb⟩ := hbd b
    have hpos : (1 : ℤ) ≤ blockSize β b := by exact_mod_cast blockSize_pos β b
    have hk : |k b| ≤ ∑ b, (|k b| + |K b|) := (le_add_of_nonneg_right (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun b => |k b| + |K b|) (fun b _ => by positivity)
        (Finset.mem_univ b))
    have hK : |K b| ≤ ∑ b, (|k b| + |K b|) := (le_add_of_nonneg_left (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun b => |k b| + |K b|) (fun b _ => by positivity)
        (Finset.mem_univ b))
    have h1 : c i ≤ |K b| := by
      rcases le_or_gt (c i) 0 with h | h
      · exact h.trans (abs_nonneg _)
      · nlinarith [le_abs_self (K b)]
    have h2 : -|k b| ≤ c i + N := by
      rcases le_or_gt 0 (c i + N) with h | h
      · exact (neg_nonpos.2 (abs_nonneg _)).trans h
      · nlinarith [neg_abs_le (k b)]
    constructor <;> linarith [(hc2 i).1, (hc2 i).2]
  refine Set.mem_biUnion hμS ⟨(⟨k₁, hk₁.1⟩, ⟨k₂, hk₂.1⟩), ⟨hk₁.2, hk₂.2⟩, Subtype.ext hmk.symm⟩

end Support

section Unipotent

theorem exists_conj_mem_leviIntegral {γ : Fin n → ℕ} {u : levi F n β}
    (hu : (u : GL (Fin n) F) ∈ unipotentRadical F n γ) :
    ∃ t : levi F n β, t * u * t⁻¹ ∈ leviIntegral F n β := by
  obtain ⟨e, he⟩ := exists_pow_mul_mem_of_isCompact F n
    (({(u : GL (Fin n) F), (u : GL (Fin n) F)⁻¹} : Set (GL (Fin n) F)).toFinite.isCompact)
  have hmem := mem_unipotentCompact_of_bound (u := (⟨(u : GL (Fin n) F), hu⟩ : unipotentRadical F n γ))
    (fun i j => he _ (by simp) i j) (fun i j => he _ (by simp) i j)
  rw [mem_unipotentCompact] at hmem
  exact ⟨⟨rankTorus F n γ e, diagGL_mem_levi _⟩, Subgroup.mem_subgroupOf.2 hmem⟩

theorem eq_one_of_mem_leviIntegral (θ : levi F n β →* NNReal) (hθ : Continuous θ)
    {k : levi F n β} (hk : k ∈ leviIntegral F n β) : θ k = 1 := by
  obtain ⟨B, hB⟩ := (isCompact_leviIntegral.image hθ).bddAbove
  have hle : ∀ x ∈ leviIntegral F n β, θ x ≤ 1 := by
    intro x hx
    by_contra h
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt B (not_le.1 h)
    exact absurd (hB ⟨x ^ j, pow_mem hx j, map_pow θ x j⟩) (not_le.2 hj)
  have h1 := hle k hk
  have h2 := hle k⁻¹ (inv_mem hk)
  have h3 : θ k * θ k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  by_contra hne
  have hlt : θ k < 1 := lt_of_le_of_ne h1 hne
  have : θ k * θ k⁻¹ < 1 := mul_lt_one_of_nonneg_of_lt_one_left zero_le hlt h2
  rw [h3] at this
  exact lt_irrefl _ this

theorem map_eq_one_of_mem_unipotentRadical (θ : levi F n β →* NNReal) (hθ : Continuous θ)
    {γ : Fin n → ℕ} {u : levi F n β} (hu : (u : GL (Fin n) F) ∈ unipotentRadical F n γ) :
    θ u = 1 := by
  obtain ⟨t, ht⟩ := exists_conj_mem_leviIntegral hu
  have h := eq_one_of_mem_leviIntegral θ hθ ht
  have ht0 : θ t ≠ 0 := by
    intro h0
    have : θ t * θ t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  rw [map_mul, map_mul, map_inv, mul_comm (θ t), mul_assoc, mul_inv_cancel₀ ht0, mul_one] at h
  exact h

theorem blockOrd_of_mem_unipotentRadical (b : Set.range β) {γ : Fin n → ℕ} {u : levi F n β}
    (hu : (u : GL (Fin n) F) ∈ unipotentRadical F n γ) : blockOrd F b u = 0 := by
  obtain ⟨t, ht⟩ := exists_conj_mem_leviIntegral hu
  have h := blockOrd_of_mem_integralGL b (Subgroup.mem_subgroupOf.1 ht)
  rw [blockOrd_mul, blockOrd_mul, blockOrd_inv] at h
  omega

theorem ordDet_of_mem_unipotentRadical {γ : Fin n → ℕ} {u : levi F n β}
    (hu : (u : GL (Fin n) F) ∈ unipotentRadical F n γ) : ordDet (u : GL (Fin n) F) = 0 := by
  rw [ordDet_eq_sum_blockOrd]
  exact Finset.sum_eq_zero fun b _ => blockOrd_of_mem_unipotentRadical b hu

theorem map_mul_right_eq_self_of_mem_unipotentRadical [MeasurableSpace (levi F n β)]
    [BorelSpace (levi F n β)] (μ : MeasureTheory.Measure (levi F n β)) [μ.IsHaarMeasure]
    {γ : Fin n → ℕ} {u : levi F n β} (hu : (u : GL (Fin n) F) ∈ unipotentRadical F n γ) :
    MeasureTheory.Measure.map (· * u) μ = μ := by
  have : LocallyCompactSpace (levi F n β) :=
    isClosed_levi.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨t, ht⟩ := exists_conj_mem_leviIntegral hu
  let V : Subgroup (levi F n β) := (leviIntegral F n β).comap (MulAut.conj t).toMonoidHom
  have hVo : IsOpen (V : Set (levi F n β)) :=
    isOpen_leviIntegral.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hVc : IsCompact (V : Set (levi F n β)) := by
    have : (V : Set (levi F n β)) = (fun x => t⁻¹ * x * t) '' (leviIntegral F n β : Set _) := by
      ext x
      simp only [V, SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, Set.mem_image]
      constructor
      · intro hx
        exact ⟨_, hx, by group⟩
      · rintro ⟨y, hy, rfl⟩
        convert hy using 1
        group
    rw [this]
    exact isCompact_leviIntegral.image ((continuous_const.mul continuous_id).mul continuous_const)
  have huV : u ∈ V := by
    simp only [V, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact ht
  have hmeas : Measurable (· * u : levi F n β → levi F n β) := measurable_mul_const u
  have hpre : (· * u) ⁻¹' (V : Set (levi F n β)) = V := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun h => by simpa using V.mul_mem h (V.inv_mem huV), fun h => V.mul_mem h huV⟩
  have key := MeasureTheory.Measure.isMulLeftInvariant_eq_smul
    (MeasureTheory.Measure.map (· * u) μ) μ
  have hV0 : μ V ≠ 0 := hVo.measure_ne_zero μ ⟨1, V.one_mem⟩
  have hVT : μ V ≠ ⊤ := hVc.measure_lt_top.ne
  have hc : MeasureTheory.Measure.haarScalarFactor (MeasureTheory.Measure.map (· * u) μ) μ = 1 := by
    have h1 := congrArg (fun ν : MeasureTheory.Measure (levi F n β) => ν V) key
    simp only [MeasureTheory.Measure.smul_apply] at h1
    rw [MeasureTheory.Measure.map_apply hmeas hVo.measurableSet, hpre] at h1
    have : ((MeasureTheory.Measure.haarScalarFactor (MeasureTheory.Measure.map (· * u) μ) μ :
        NNReal) : ENNReal) = 1 := by
      rw [ENNReal.smul_def, smul_eq_mul] at h1
      have := (ENNReal.mul_eq_right hV0 hVT).1 h1.symm
      exact this
    exact_mod_cast this
  rw [key, hc, one_smul]

theorem zeroBlock_mul_unipotent {b : Set.range β} {i₀ : Fin n} (hi₀ : blockOf β i₀ = b)
    (m : levi F n β) {u : levi F n β}
    (hu : (u : GL (Fin n) F) ∈ unipotentRadical F n (splitFun {i₀})) :
    zeroBlock b (((m * u : levi F n β) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      zeroBlock b ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨hP, h1⟩ := mem_unipotentRadical.1 hu
  ext i j
  simp only [zeroBlock]
  split_ifs with hib
  · rfl
  · rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    have hrow : ∀ l, ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i l *
        ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) l j =
        ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i l * (1 : Matrix (Fin n) (Fin n) F) l j := by
      intro l
      by_cases hl : β i = β l
      · have hli : l ≠ i₀ := by
          rintro rfl
          exact hib ((Subtype.ext hl : blockOf β i = blockOf β l).trans hi₀)
        have hγl : splitFun ({i₀} : Finset (Fin n)) l = 1 := by simp [splitFun, hli]
        congr 1
        by_cases hj : j = i₀
        · subst hj
          have hγj : splitFun ({j} : Finset (Fin n)) j = 0 := by simp [splitFun]
          rw [hP (by rw [hγj, hγl]; exact zero_lt_one), Matrix.one_apply_ne hli]
        · have hγj : splitFun ({i₀} : Finset (Fin n)) j = 1 := by simp [splitFun, hj]
          exact h1 l j (by rw [hγl, hγj])
      · rw [mem_levi.1 m.2 i l hl, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl fun l _ => hrow l, ← Matrix.mul_apply, Matrix.mul_one]

end Unipotent

end GodementJacquet

end GroundTheory.Automorphic
