import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJFELeviMulti
import GroundTheory.AutomorphicForms.InductionParabolic

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal MeasureTheory Measure Parabolic
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

section Twist

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] {W : Type*} [AddCommGroup W] [Module ℂ W]

def nnrealCharC (χ : G →* ℝ≥0) : G →* ℂ :=
  (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom.comp χ

@[simp]
theorem nnrealCharC_apply (χ : G →* ℝ≥0) (g : G) : nnrealCharC χ g = ((χ g : ℝ) : ℂ) := rfl

theorem nnrealCharC_ne_zero (χ : G →* ℝ≥0) (g : G) : nnrealCharC χ g ≠ 0 := by
  rw [nnrealCharC_apply]
  have h := map_mul_eq_one χ (mul_inv_cancel g)
  exact_mod_cast (left_ne_zero_of_mul_eq_one h)

theorem exists_compact_open_char_eq_one (χ : G →* ℝ≥0) (hχ : Continuous χ) {U : Set G}
    (hU : U ∈ nhds (1 : G)) : ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U ∧
      ∀ k ∈ (K : Set G), χ k = 1 := by
  obtain ⟨K, hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hU
  exact ⟨K, hKc, hKU, fun k hk => eq_one_of_mem_compact χ hχ hKc hk⟩

variable (χ : G →* ℝ≥0) (hχ : Continuous χ) (ρ : Representation ℂ G W)
include hχ

theorem fixedVectors_twist {K : Subgroup G} (hKc : IsCompact (K : Set G)) :
    fixedVectors (twist (nnrealCharC χ) ρ) K = fixedVectors ρ K := by
  ext v
  simp only [mem_fixedVectors, twist_apply, nnrealCharC_apply]
  refine forall₂_congr fun k hk => ?_
  rw [eq_one_of_mem_compact χ hχ hKc hk]
  simp

theorem isSmooth_twist (hρ : IsSmooth ρ) : IsSmooth (twist (nnrealCharC χ) ρ) := by
  intro v
  obtain ⟨K, hKc, hKU, hK1⟩ := exists_compact_open_char_eq_one χ hχ
    ((hρ v).mem_nhds (one_mem (stabilizerOf ρ v)))
  refine Subgroup.isOpen_mono (H₁ := (K : Subgroup G)) (fun k hk => ?_) K.isOpen
  rw [mem_stabilizerOf, twist_apply, nnrealCharC_apply, hK1 k hk, mem_stabilizerOf.1 (hKU hk)]
  simp

theorem isAdmissible_twist (hρ : IsAdmissible ρ) : IsAdmissible (twist (nnrealCharC χ) ρ) :=
  ⟨isSmooth_twist χ hχ ρ hρ.1, fun K hKc hKo => by
    rw [fixedVectors_twist χ hχ ρ hKc]
    exact hρ.2 K hKc hKo⟩

omit hχ in

def subrepresentationTwistOrderIso :
    Subrepresentation (twist (nnrealCharC χ) ρ) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    have h := S.apply_mem_toSubmodule g hv
    rw [twist_apply] at h
    have := S.toSubmodule.smul_mem (nnrealCharC χ g)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ (nnrealCharC_ne_zero χ g), one_smul] at this⟩
  invFun S := ⟨S.toSubmodule, fun g v hv => by
    rw [twist_apply]
    exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
  left_inv S := rfl
  right_inv S := rfl
  map_rel_iff' := Iff.rfl

omit hχ in
theorem isIrreducible_twist [ρ.IsIrreducible] :
    (twist (nnrealCharC χ) ρ).IsIrreducible :=
  (OrderIso.isSimpleOrder_iff (subrepresentationTwistOrderIso χ ρ)).2 inferInstance

theorem mem_smoothVectors_dual_twist_iff {ℓ : Module.Dual ℂ W} :
    ℓ ∈ smoothVectors (Representation.dual (twist (nnrealCharC χ) ρ)) ↔
      ℓ ∈ smoothVectors (Representation.dual ρ) := by
  have key : ∀ (ρ₁ ρ₂ : Representation ℂ G W), (∀ g, ∀ x, χ g = 1 → ρ₁ g x = ρ₂ g x) →
      ℓ ∈ smoothVectors (Representation.dual ρ₁) → ℓ ∈ smoothVectors (Representation.dual ρ₂) := by
    intro ρ₁ ρ₂ h12 hℓ
    obtain ⟨K, hKc, hKU, hK1⟩ := exists_compact_open_char_eq_one χ hχ
      (hℓ.mem_nhds (one_mem (stabilizerOf (Representation.dual ρ₁) ℓ)))
    refine Subgroup.isOpen_mono (H₁ := (K : Subgroup G)) (fun k hk => ?_) K.isOpen
    have h1 := mem_stabilizerOf.1 (hKU hk)
    rw [mem_stabilizerOf]
    ext x
    have := LinearMap.congr_fun h1 x
    rw [dual_apply_apply] at this ⊢
    rw [← h12 k⁻¹ x (by rw [map_inv, hK1 k hk, inv_one]), this]
  constructor
  · exact key _ _ fun g x hg => by rw [twist_apply, nnrealCharC_apply, hg]; simp
  · exact key _ _ fun g x hg => by rw [twist_apply, nnrealCharC_apply, hg]; simp

end Twist

section PUnitProd

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def prodPUnitEquiv : (G × PUnit) ≃ₜ* G where
  toFun p := p.1
  invFun g := (g, 1)
  left_inv p := by ext1 <;> rfl
  right_inv g := rfl
  map_mul' p q := rfl
  continuous_toFun := continuous_fst
  continuous_invFun := continuous_id.prodMk continuous_const

end PUnitProd

section LeviBlocks

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

theorem leviEquivPi_symm_apply_entry (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F)
    (a : Set.range β) (k l : Fin (blockSize β a)) :
    (((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) (fiberFin β a k).1
      (fiberFin β a l).1 = ((x a : GL (Fin (blockSize β a)) F) : Matrix _ _ F) k l := by
  rw [← leviEquivPi_apply, ContinuousMulEquiv.apply_symm_apply]

theorem det_leviEquivPi (m : levi F n β) (a : Set.range β) :
    Matrix.det ((leviEquivPi F β m a : GL (Fin (blockSize β a)) F) :
      Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) =
      Matrix.det ((leviBlock F m a : GL (Fiber β a) F) : Matrix (Fiber β a) (Fiber β a) F) := by
  show (Matrix.reindex _ _ ((leviBlock F m a : GL (Fiber β a) F) :
    Matrix (Fiber β a) (Fiber β a) F)).det = _
  exact Matrix.det_reindex_self _ _

theorem ordDet_leviEquivPi (m : levi F n β) (a : Set.range β) :
    ordDet (leviEquivPi F β m a) = blockOrd F a m := by
  rw [ordDet, det_leviEquivPi]
  rfl

theorem detPow_leviEquivPi_symm (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) (s : ℂ) :
    detPow (((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) s =
      ∏ a, detPow (x a) s := by
  rw [detPow_eq_qs_zpow, ordDet_eq_sum_blockOrd]
  have : ∀ a, blockOrd F a ((leviEquivPi F β).symm x) = ordDet (x a) := fun a => by
    rw [← ordDet_leviEquivPi, ContinuousMulEquiv.apply_symm_apply]
  simp_rw [this, detPow_eq_qs_zpow]
  classical
  induction (Finset.univ : Finset (Set.range β)) using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (qs_ne_zero s), ih]

theorem leviModulus_leviEquivPi_symm (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) :
    leviModulus β ((leviEquivPi F β).symm x) = ∏ a, detModulusPow (x a) := by
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [detModulusPow, ← det_leviEquivPi, ContinuousMulEquiv.apply_symm_apply]

theorem leviEquivPi_symm_mulSingle (a : Set.range β) :
    (leviEquivPi F β).symm (Pi.mulSingle a (centralUnif F (blockSize β a))) = blockUnif F a := by
  classical
  apply (leviEquivPi F β).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  funext b
  ext k l
  rw [leviEquivPi_apply]
  simp only [blockUnif, Cartan.diagPow, Matrix.diagonal_apply]
  have hk : blockOf β (fiberFin β b k).1 = b := (fiberFin β b k).2
  have hkl : (fiberFin β b k).1 = (fiberFin β b l).1 ↔ k = l := by
    rw [← Subtype.ext_iff, (fiberFin β b).injective.eq_iff]
  by_cases hb : b = a
  · subst hb
    rw [Pi.mulSingle_eq_same, coe_centralUnif]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, blockIndicator, hk, if_true,
      zpow_one, hkl]
    split_ifs <;> simp
  · rw [Pi.mulSingle_eq_of_ne hb]
    simp only [Units.val_one, Matrix.one_apply, blockIndicator, hk, if_neg hb, zpow_zero, hkl]

variable (β) in

def leviIdx (a : Set.range β) (k l : Fin (blockSize β a)) : LeviIndex n β :=
  ⟨((fiberFin β a k).1, (fiberFin β a l).1), by
    have hk := congrArg Subtype.val (fiberFin β a k).2
    have hl := congrArg Subtype.val (fiberFin β a l).2
    exact hk.trans hl.symm⟩

theorem leviIdx_bijective :
    Function.Bijective fun p : (Σ a : Set.range β, Fin (blockSize β a) × Fin (blockSize β a)) =>
      leviIdx β p.1 p.2.1 p.2.2 := by
  constructor
  · rintro ⟨a, k, l⟩ ⟨a', k', l'⟩ h
    have h1 : (fiberFin β a k).1 = (fiberFin β a' k').1 :=
      congrArg (fun ij : LeviIndex n β => ij.1.1) h
    have h2 : (fiberFin β a l).1 = (fiberFin β a' l').1 :=
      congrArg (fun ij : LeviIndex n β => ij.1.2) h
    have ha : a = a' := (fiberFin β a k).2.symm.trans (by rw [h1]; exact (fiberFin β a' k').2)
    subst ha
    have hk : k = k' := (fiberFin β a).injective (Subtype.ext h1)
    have hl : l = l' := (fiberFin β a).injective (Subtype.ext h2)
    subst hk hl
    rfl
  · rintro ⟨⟨i, j⟩, hij⟩
    have hj : blockOf β j = blockOf β i := Subtype.ext hij.symm
    refine ⟨⟨blockOf β i, ((fiberFin β (blockOf β i)).symm ⟨i, rfl⟩,
      (fiberFin β (blockOf β i)).symm ⟨j, hj⟩)⟩, ?_⟩
    simp only [leviIdx, Equiv.apply_symm_apply]

theorem prod_leviIndex {M : Type*} [CommMonoid M] (f : LeviIndex n β → M) :
    ∏ ij, f ij = ∏ a : Set.range β, ∏ p : Fin (blockSize β a) × Fin (blockSize β a),
      f (leviIdx β a p.1 p.2) := by
  rw [← Fintype.prod_equiv (Equiv.ofBijective _ leviIdx_bijective) (fun p => f (leviIdx β p.1 p.2.1 p.2.2)) f
    (fun p => rfl), Fintype.prod_sigma]

variable (β) in

def blockTensor (φ : LeviIndex n β → F → ℂ) (a : Set.range β)
    (X : Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) : ℂ :=
  ∏ p : Fin (blockSize β a) × Fin (blockSize β a), φ (leviIdx β a p.1 p.2) (X p.1 p.2)

theorem leviTensor_leviEquivPi_symm (φ : LeviIndex n β → F → ℂ)
    (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) :
    leviTensor β φ ((((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) : Matrix _ _ F) =
      ∏ a, blockTensor β φ a (x a : Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) := by
  rw [leviTensor, prod_leviIndex]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun p _ => ?_
  simp only [leviIdx]
  rw [leviEquivPi_symm_apply_entry]

theorem isSchwartzBruhat_blockTensor {φ : LeviIndex n β → F → ℂ}
    (hφ : ∀ ij, φ ij ∈ LocalField.schwartzBruhat F) (a : Set.range β) :
    IsSchwartzBruhat (blockTensor β φ a) := by
  rw [GJMatrix.isSchwartzBruhat_iff_comp_symm]
  have : blockTensor β φ a ∘ (GJMatrix.matrixCoordHomeomorph (Fin (blockSize β a)) F).symm =
      GJMatrix.localTensor fun p : Fin (blockSize β a) × Fin (blockSize β a) =>
        φ (leviIdx β a p.1 p.2) := by
    funext z
    rfl
  rw [this]
  exact GJMatrix.localTensor_mem fun p => hφ _

variable [MeasurableSpace F] [BorelSpace F]

theorem localMatrixFourier_entryTensor (ψ : AddChar F Circle) {m : ℕ}
    (g : Fin m × Fin m → F → ℂ) (Y : Matrix (Fin m) (Fin m) F) :
    GJMatrix.localMatrixFourier ψ (fun X => ∏ p : Fin m × Fin m, g p (X p.1 p.2)) Y =
      ∏ p : Fin m × Fin m,
        LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g p) (Y p.2 p.1) := by
  rw [GJMatrix.localMatrixFourier_eq]
  have : (fun X : Matrix (Fin m) (Fin m) F => ∏ p : Fin m × Fin m, g p (X p.1 p.2)) ∘
      (GJMatrix.matrixCoordHomeomorph (Fin m) F).symm = GJMatrix.localTensor g := by
    funext z
    rfl
  rw [this, GJMatrix.localFourierPi_localTensor]
  rfl

theorem leviTensorHat_leviEquivPi_symm (ψ : AddChar F Circle) (φ : LeviIndex n β → F → ℂ)
    (x : ∀ a : Set.range β, GL (Fin (blockSize β a)) F) :
    leviTensorHat β ψ φ ((((leviEquivPi F β).symm x : levi F n β) : GL (Fin n) F) : Matrix _ _ F) =
      ∏ a, GJMatrix.localMatrixFourier ψ (blockTensor β φ a)
        (x a : Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F) := by
  rw [leviTensorHat, prod_leviIndex]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [show blockTensor β φ a = fun X => ∏ p : Fin (blockSize β a) × Fin (blockSize β a),
    φ (leviIdx β a p.1 p.2) (X p.1 p.2) from rfl, localMatrixFourier_entryTensor]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp only [leviIdx]
  rw [leviEquivPi_symm_apply_entry]

end LeviBlocks

section Main

universe uF u w

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {α : Type u} [LinearOrder α] {β : Fin n → α}
  {W : Type w} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

theorem nontrivial_of_isIrreducible {G : Type*} [Group G] (ρ : Representation ℂ G W)
    [ρ.IsIrreducible] : Nontrivial W := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : Subsingleton (Subrepresentation ρ) := ⟨fun S T => by
    cases S; cases T; congr 1; exact Subsingleton.elim _ _⟩
  exact bot_ne_top (Subsingleton.elim (⊥ : Subrepresentation ρ) ⊤)

theorem detPow_add (g : GL (Fin n) F) (a b : ℂ) : detPow g (a + b) = detPow g a * detPow g b := by
  rw [detPow_eq_qs_zpow, detPow_eq_qs_zpow, detPow_eq_qs_zpow, qs_add, mul_zpow]

theorem borelSpace_GL_units (m : ℕ) : BorelSpace (GL (Fin m) F) := by
  refine ⟨?_⟩
  have hM : (GJMatrix.measurableSpace_matrix : MeasurableSpace (Matrix (Fin m) (Fin m) F)) =
      _root_.borel (Matrix (Fin m) (Fin m) F) := BorelSpace.measurable_eq
  show MeasurableSpace.comap Units.val _ = _
  rw [hM, ← borel_comap, ← (Measures.isOpenEmbedding_val F m).isEmbedding.eq_induced]

theorem exists_leviFE (hσ : IsAdmissible σ) [σ.IsIrreducible] (hc : IsCuspidal σ)
    (κ : levi F n β →* ℝ≥0) (hκ : Continuous κ) (μM : Measure (levi F n β)) [μM.IsHaarMeasure]
    {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∃ γ : RatFunc ℂ, LeviFE F σ κ μM ψ γ := by
  classical
  have _ : ∀ m : ℕ, BorelSpace (GL (Fin m) F) := fun m => borelSpace_GL_units m
  set e := leviEquivPi F β with he

  set κ' : (∀ a : Set.range β, GL (Fin (blockSize β a)) F) →* ℝ≥0 :=
    κ.comp e.symm.toMonoidHom with hκ'def
  have hκ' : Continuous κ' := hκ.comp e.symm.continuous
  set σ' : Representation ℂ (∀ a : Set.range β, GL (Fin (blockSize β a)) F) W :=
    σ.comp e.symm.toMonoidHom with hσ'def
  set ρ₀ := twist (nnrealCharC κ') σ' with hρ₀def
  set ρ : Representation ℂ ((∀ a : Set.range β, GL (Fin (blockSize β a)) F) × PUnit.{max u uF + 1}) W :=
    ρ₀.comp (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)).toMulEquiv.toMonoidHom
    with hρdef
  have hρ : ∀ x (h : PUnit.{max u uF + 1}) v, ρ (x, h) v = ((κ (e.symm x) : ℝ) : ℂ) • σ (e.symm x) v :=
    fun x h v => rfl
  have hσ' : IsAdmissible σ' := (isAdmissible_comp_iff e.symm σ).2 hσ
  have hadm : IsAdmissible ρ := (isAdmissible_comp_iff
    (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)) ρ₀).2
    (isAdmissible_twist κ' hκ' σ' hσ')
  have hirr' : σ'.IsIrreducible := (isIrreducible_comp_iff e.symm σ).2 inferInstance
  have hirr : ρ.IsIrreducible := (isIrreducible_comp_iff
    (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)) ρ₀).2
    (isIrreducible_twist κ' σ')
  have hsm : ∀ ℓ : Module.Dual ℂ W, ℓ ∈ smoothVectors (Representation.dual ρ) ↔
      ℓ ∈ smoothVectors (Representation.dual σ) := fun ℓ => by
    rw [mem_smoothVectors_dual_comp_iff
      (prodPUnitEquiv (∀ a : Set.range β, GL (Fin (blockSize β a)) F)) ρ₀,
      mem_smoothVectors_dual_twist_iff κ' hκ' σ', mem_smoothVectors_dual_comp_iff e.symm σ]

  obtain ⟨ω, hω⟩ := exists_blockChar hσ.1 (σ := σ)
  have hW : Nontrivial W := nontrivial_of_isIrreducible σ
  have hω0 : ∀ a, ω a ≠ 0 := by
    intro a h0
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    apply hv
    have h1 : σ (blockUnif F a)⁻¹ (σ (blockUnif F a) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1, hω, h0, zero_smul, map_zero]
  set αc : Set.range β → ℂ := fun a => ((κ (blockUnif F a) : ℝ) : ℂ) * ω a with hαc
  have hα0 : ∀ a, αc a ≠ 0 := fun a =>
    mul_ne_zero (by simpa using nnrealCharC_ne_zero κ (blockUnif F a)) (hω0 a)
  have hα : ∀ a v, ρ (Pi.mulSingle a (centralUnif F (blockSize β a)), 1) v = αc a • v := by
    intro a v
    rw [hρ, leviEquivPi_symm_mulSingle, hω, smul_smul]

  have hsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ),
      ∃ C : Set (∀ a : Set.range β, GL (Fin (blockSize β a)) F), IsCompact C ∧
        ∀ x, ℓ (ρ (x, 1) v) ≠ 0 →
          ∃ j : Set.range β → ℤ, (fun a => centralUnif F (blockSize β a) ^ j a) * x ∈ C := by
    intro v ℓ hℓ
    have hℓσ := (hsm ℓ).1 hℓ
    obtain ⟨CM, hCM, hCMs⟩ := exists_compact_of_coeff hσ.1 hc v hℓσ (fun _ => 0)
      (fun b => (blockSize β b : ℤ) - 1)
    refine ⟨e '' CM, hCM.image e.continuous, fun x hx => ?_⟩
    have hpos : ∀ b, (0 : ℤ) < blockSize β b := fun b => by exact_mod_cast blockSize_pos β b
    set j : Set.range β → ℤ := fun b => -(ordDet (x b) / blockSize β b) with hj
    refine ⟨j, e.symm ((fun a => centralUnif F (blockSize β a) ^ j a) * x), ?_, by simp⟩
    refine hCMs _ ?_ fun b => ?_
    · have hmul := apply_centralPow ρ hα0 hα j (ρ (x, 1) v)
      have h2 : ρ ((fun a => centralUnif F (blockSize β a) ^ j a) * x, 1) v =
          (∏ a, αc a ^ j a) • ρ (x, 1) v := by
        rw [← hmul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
      have h3 := hρ ((fun a => centralUnif F (blockSize β a) ^ j a) * x) 1 v
      intro h0
      apply hx
      have hprod0 : (∏ a, αc a ^ j a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => zpow_ne_zero _ (hα0 a)
      have hκ0 := nnrealCharC_ne_zero κ (e.symm ((fun a => centralUnif F (blockSize β a) ^ j a) * x))
      rw [nnrealCharC_apply] at hκ0
      have : ℓ (ρ ((fun a => centralUnif F (blockSize β a) ^ j a) * x, 1) v) = 0 := by
        rw [h3, map_smul, smul_eq_mul, h0, mul_zero]
      rw [h2, map_smul, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hprod0
    · rw [← ordDet_leviEquivPi, ContinuousMulEquiv.apply_symm_apply, Pi.mul_apply,
        ordDet_centralUnif_zpow_mul]
      have h1 := Int.emod_nonneg (ordDet (x b)) (hpos b).ne'
      have h2 := Int.emod_lt_of_pos (ordDet (x b)) (hpos b)
      have h3 := Int.emod_def (ordDet (x b)) (blockSize β b)
      simp only [hj]
      constructor <;> nlinarith

  have _ : ∀ a : Set.range β, NeZero (blockSize β a) := fun a => ⟨(blockSize_pos β a).ne'⟩
  set μb : ∀ a : Set.range β, Measure (GL (Fin (blockSize β a)) F) := fun a => Measure.haar
    with hμb
  obtain ⟨γ, hmain⟩ := multiFEStatement_all.{uF, u, w} hψ hψ1
    (Fintype.card (Set.range β)) (Set.range β) rfl (fun a => blockSize β a) μb
    PUnit.{max u uF + 1} ρ hadm hirr αc hα0 hα hsupp
  obtain ⟨s₀, hconv⟩ := exists_integrable_multi ρ hadm.1 hα0 hα hsupp μb

  set em := e.toHomeomorph.toMeasurableEquiv with hem
  have hν : (Measure.map em μM).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μM e.toMulEquiv e.continuous e.symm.continuous
  set c := haarScalarFactor (Measure.map em μM) (Measure.pi μb) with hcdef
  have hc : Measure.map em μM = c • Measure.pi μb :=
    Measure.isMulLeftInvariant_eq_smul (Measure.map em μM) (Measure.pi μb)
  have hemx : ∀ m, e.symm (em m) = m := fun m => e.symm_apply_apply m
  have hint_eq : ∀ f : levi F n β → ℂ,
      ∫ m, f m ∂μM = ((c : ℝ) : ℂ) * ∫ x, f (e.symm x) ∂Measure.pi μb := by
    intro f
    have h1 : ∫ x, f (e.symm x) ∂(Measure.map em μM) = ∫ m, f m ∂μM := by
      rw [integral_map_equiv em]
      simp only [hemx]
    rw [← h1, hc, show (c • Measure.pi μb) = ((c : ℝ≥0∞) • Measure.pi μb) from rfl,
      integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul]
  have hint_of : ∀ f : levi F n β → ℂ,
      Integrable (fun x => f (e.symm x)) (Measure.pi μb) → Integrable f μM := by
    intro f hf
    have h1 : Integrable (fun x => f (e.symm x)) (Measure.map em μM) := by
      rw [hc, show (c • Measure.pi μb) = ((c : ℝ≥0∞) • Measure.pi μb) from rfl]
      exact hf.smul_measure ENNReal.coe_ne_top
    rw [integrable_map_equiv] at h1
    exact h1.congr (Filter.Eventually.of_forall fun m => by simp only [Function.comp_apply, hemx])
  refine ⟨γ, fun φ hφ w ℓ hℓ => ?_⟩
  set Ψ : ∀ a : Set.range β, Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F → ℂ :=
    fun a => blockTensor β φ a with hΨdef
  have hΨ : ∀ a, IsSchwartzBruhat (Ψ a) := fun a => isSchwartzBruhat_blockTensor hφ a
  have hℓρ : ℓ ∈ smoothVectors (Representation.dual ρ) := (hsm ℓ).2 hℓ
  have hA_eq : ∀ s x, leviIntegrand σ κ (leviTensor β φ) w ℓ s (e.symm x) =
      multiA ρ Ψ w ℓ s x := by
    intro s x
    simp only [leviIntegrand, multiA]
    rw [leviTensor_leviEquivPi_symm, detPow_leviEquivPi_symm, hρ, map_smul, smul_eq_mul,
      Finset.prod_mul_distrib]
    ring
  have hB_eq : ∀ s x, leviIntegrandB σ κ (leviTensorHat β ψ φ) w ℓ s (e.symm x) =
      multiB ρ (fun a => GJMatrix.localMatrixFourier ψ (Ψ a)) w ℓ s x := by
    intro s x
    simp only [leviIntegrandB, multiB]
    rw [leviTensorHat_leviEquivPi_symm, leviModulus_leviEquivPi_symm, detPow_leviEquivPi_symm,
      hρ, map_smul, smul_eq_mul, map_inv e.symm x, map_inv κ]
    have hdet : ∀ a, detPow (x a) ((blockSize β a : ℂ) - s) =
        ((detModulusPow (x a) : ℝ) : ℂ) * detPow (x a) (-s) := fun a => by
      rw [sub_eq_add_neg, detPow_add, detPow_natCast]
    simp_rw [hdet]
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  refine ⟨⟨s₀, fun s hs => hint_of _ (((hconv Ψ hΨ w ℓ hℓρ).1 s hs).congr
      (Filter.Eventually.of_forall fun x => (hA_eq s x).symm))⟩,
    ⟨-s₀, fun s hs => hint_of _ (((hconv (fun a => GJMatrix.localMatrixFourier ψ (Ψ a))
      (fun a => (hΨ a).localMatrixFourier hψ hψ1) w ℓ hℓρ).2 s hs).congr
      (Filter.Eventually.of_forall fun x => (hB_eq s x).symm))⟩, ?_⟩
  refine ((hmain Ψ hΨ w ℓ hℓρ).const_mul ((c : ℝ) : ℂ)).congr ⟨0, fun s _ => ?_⟩ ⟨0, fun s _ => ?_⟩
  · rw [hint_eq]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hA_eq s x)
  · rw [hint_eq]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hB_eq s x)

end Main

end GodementJacquet

end GroundTheory.Automorphic
