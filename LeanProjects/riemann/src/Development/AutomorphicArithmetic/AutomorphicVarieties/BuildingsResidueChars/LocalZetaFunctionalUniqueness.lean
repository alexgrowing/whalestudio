import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdDefs

noncomputable section
open MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem val_one_entry_le {n : ℕ} (i j : Fin n) :
    ValuativeRel.valuation F ((1 : Matrix (Fin n) (Fin n) F) i j) ≤ 1 := by
  by_cases h : i = j
  · simp [Matrix.one_apply, h]
  · simp [Matrix.one_apply, h]

private theorem coe_one_entry {n : ℕ} (i j : Fin n) :
    (((1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j : 𝒪[F]) : F) = (1 : Matrix (Fin n) (Fin n) F) i j := by
  by_cases h : i = j
  · simp [Matrix.one_apply, h]
  · simp [Matrix.one_apply, h]

private theorem mem_integralGL_of_congr {n r : ℕ} (hr : 1 ≤ r) {g : GL (Fin n) F}
    (hg : ∀ i j, ValuativeRel.valuation F ((g : Matrix (Fin n) (Fin n) F) i j - (1 : Matrix (Fin n) (Fin n) F) i j) ≤
      ValuativeRel.valuation F (uniformizer F : F) ^ r) : g ∈ integralGL F n := by
  have hπ1 : ValuativeRel.valuation F (uniformizer F : F) ^ r ≤ 1 :=
    pow_le_one' (valuation_uniformizer_lt_one F).le r
  have hent : ∀ i j, (g : Matrix (Fin n) (Fin n) F) i j ∈ (ValuativeRel.valuation F).integer := by
    intro i j
    have e : (g : Matrix (Fin n) (Fin n) F) i j =
        ((g : Matrix (Fin n) (Fin n) F) i j - (1 : Matrix (Fin n) (Fin n) F) i j) +
          (1 : Matrix (Fin n) (Fin n) F) i j := by ring
    show ValuativeRel.valuation F _ ≤ 1
    rw [e]
    exact le_trans ((ValuativeRel.valuation F).map_add _ _)
      (max_le (le_trans (hg i j) hπ1) (val_one_entry_le i j))
  let M : Matrix (Fin n) (Fin n) 𝒪[F] := fun i j => ⟨_, hent i j⟩
  have hdiff : ∀ i j, M i j - (1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    intro i j
    have h1 : M i j - (1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j ∈ IsLocalRing.maximalIdeal 𝒪[F] ^ r := by
      apply (mem_maximalIdeal_pow_iff F).2
      have e : ((M i j - (1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j : 𝒪[F]) : F) =
          (g : Matrix (Fin n) (Fin n) F) i j - (1 : Matrix (Fin n) (Fin n) F) i j := by
        rw [AddSubgroupClass.coe_sub, coe_one_entry]
      rw [e]
      exact hg i j
    exact Ideal.pow_le_self (by omega) h1
  have hmap : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[F])).mapMatrix M = 1 := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Ideal.Quotient.eq.2 (hdiff i j)]
    by_cases h : i = j
    · simp [Matrix.one_apply, h]
    · simp [Matrix.one_apply, h]
  have hdet : IsUnit M.det := by
    by_contra hu
    have hm : M.det ∈ IsLocalRing.maximalIdeal 𝒪[F] := (IsLocalRing.mem_maximalIdeal _).2 hu
    have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[F]) M.det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rw [RingHom.map_det, hmap, Matrix.det_one] at h0
    exact one_ne_zero h0
  have hM : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 hdet
  refine ⟨hM.unit, ?_⟩
  ext i j
  rfl

private theorem mem_valBall_iff_val_le {r : ℕ} {x : F} :
    x ∈ GroundTheory.LocalField.valBall F (r : ℤ) ↔
      ValuativeRel.valuation F x ≤ ValuativeRel.valuation F (uniformizer F : F) ^ r := by
  have hπ : ValuativeRel.valuation F (uniformizer F : F) ^ r ≤ 1 :=
    pow_le_one' (valuation_uniformizer_lt_one F).le r
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := mem_valBall_iff_exists.1 hx
    have hint : (uniformizer F : F) ^ r * a ∈ (ValuativeRel.valuation F).integer :=
      Subring.mul_mem _ (Subring.pow_mem _ (uniformizer F).2 r) ha
    have h1 := GroundTheory.LocalField.mem_maximalIdeal_pow_iff_valBall (y := ⟨_, hint⟩) (n := r)
    exact (mem_maximalIdeal_pow_iff F).1 (h1.2 hx)
  · intro hx
    have hint : x ∈ (ValuativeRel.valuation F).integer := le_trans hx hπ
    have h1 := (mem_maximalIdeal_pow_iff F (y := ⟨x, hint⟩) (m := r)).2 hx
    exact GroundTheory.LocalField.mem_maximalIdeal_pow_iff_valBall.1 h1

private def ballInd (r : ℕ) (a : F) : F → ℂ :=
  {x : F | x - a ∈ GroundTheory.LocalField.valBall F (r : ℤ)}.indicator 1

private theorem ballInd_mem (r : ℕ) (a : F) : ballInd r a ∈ GroundTheory.LocalField.schwartzBruhat F := by
  rw [GroundTheory.LocalField.mem_schwartzBruhat]
  constructor
  · apply GroundTheory.LocalField.isLocallyConstant_of_add_valBall (N := (r : ℤ))
    intro x h hh
    have e : x + h - a = (x - a) + h := by ring
    have key : x + h - a ∈ GroundTheory.LocalField.valBall F (r : ℤ) ↔ x - a ∈ GroundTheory.LocalField.valBall F (r : ℤ) := by
      rw [e]
      exact AddSubgroup.add_mem_cancel_right _ hh
    unfold ballInd
    by_cases hx : x - a ∈ GroundTheory.LocalField.valBall F (r : ℤ)
    · rw [Set.indicator_of_mem (show x + h ∈ {y : F | y - a ∈ GroundTheory.LocalField.valBall F (r : ℤ)} from key.2 hx),
        Set.indicator_of_mem (show x ∈ {y : F | y - a ∈ GroundTheory.LocalField.valBall F (r : ℤ)} from hx)]
      rfl
    · rw [Set.indicator_of_notMem (show x + h ∉ {y : F | y - a ∈ GroundTheory.LocalField.valBall F (r : ℤ)} from fun h' => hx (key.1 h')),
        Set.indicator_of_notMem (show x ∉ {y : F | y - a ∈ GroundTheory.LocalField.valBall F (r : ℤ)} from hx)]
  · apply HasCompactSupport.intro ((GroundTheory.LocalField.isCompact_valBall (r : ℤ)).image (continuous_add_right a))
    intro x hx
    unfold ballInd
    apply Set.indicator_of_notMem
    intro hx'
    exact hx ⟨x - a, hx', by ring⟩

end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β : Fin n → ℕ}

private theorem leviTensor_ball_of_mem {r : ℕ} {m : levi F n β}
    (hm : (m : GL (Fin n) F) ∈ congruenceSubgroup F n r) :
    leviTensor β (fun ij : LeviIndex n β => ballInd r ((1 : Matrix (Fin n) (Fin n) F) ij.1.1 ij.1.2))
      ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [mem_congruenceSubgroup_iff] at hm
  unfold leviTensor
  apply Finset.prod_eq_one
  intro ij _
  unfold ballInd
  apply Set.indicator_of_mem
  exact mem_valBall_iff_val_le.2 (hm.2 ij.1.1 ij.1.2)

private theorem leviTensor_ball_of_notMem {r : ℕ} (hr : 1 ≤ r) {m : levi F n β}
    (hm : (m : GL (Fin n) F) ∉ congruenceSubgroup F n r) :
    leviTensor β (fun ij : LeviIndex n β => ballInd r ((1 : Matrix (Fin n) (Fin n) F) ij.1.1 ij.1.2))
      ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 0 := by
  by_contra h0
  apply hm
  have hall : ∀ i j, ValuativeRel.valuation F (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j -
      (1 : Matrix (Fin n) (Fin n) F) i j) ≤ ValuativeRel.valuation F (uniformizer F : F) ^ r := by
    intro i j
    by_cases hij : β i = β j
    · have h1 := Finset.prod_ne_zero_iff.1 h0 (⟨(i, j), hij⟩ : LeviIndex n β) (Finset.mem_univ _)
      refine mem_valBall_iff_val_le.1 ?_
      by_contra hn
      exact h1 (Set.indicator_of_notMem (s := {x : F | x - (1 : Matrix (Fin n) (Fin n) F) i j ∈ GroundTheory.LocalField.valBall F (r : ℤ)}) hn _)
    · have hne : i ≠ j := fun h => hij (by rw [h])
      rw [mem_levi.1 m.2 i j hij, Matrix.one_apply_ne hne, sub_zero, map_zero]
      exact zero_le'
  exact (mem_congruenceSubgroup_iff F n).2 ⟨mem_integralGL_of_congr hr hall, hall⟩

end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {β : Fin n → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

end

end UpperTheory.V.Z.Gam

theorem UpperTheory.local_zeta_functional_uniqueness :
    UpperTheory.V.Z.Gam.LdUnique := by
  intro F _ _ _ _ _ _ n β W _ _ σ hadm hirr κ hκ μ _ ψ γ γ' h h'
  haveI := hirr
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := σ)
  obtain ⟨m0, hm0⟩ := exists_subgroupOf_congruenceSubgroup_subset (β := β)
    ((hadm.1 v).mem_nhds (Subgroup.one_mem (stabilizerOf σ v)))
  have hr : 1 ≤ m0 + 1 := by omega
  have hKc : IsCompact (((congruenceSubgroup F n (m0 + 1)).subgroupOf (levi F n β) : Subgroup (levi F n β)) :
      Set (levi F n β)) := isCompact_subgroupOf_levi (isCompact_congruenceSubgroup F n (m0 + 1))
  have hKo : IsOpen (((congruenceSubgroup F n (m0 + 1)).subgroupOf (levi F n β) : Subgroup (levi F n β)) :
      Set (levi F n β)) := isOpen_subgroupOf_levi (isOpen_congruenceSubgroup F n (m0 + 1))
  have hvK : v ∈ fixedVectors σ ((congruenceSubgroup F n (m0 + 1)).subgroupOf (levi F n β)) := by
    rw [mem_fixedVectors]
    intro k hk
    have hk' : k ∈ (congruenceSubgroup F n m0).subgroupOf (levi F n β) :=
      Subgroup.mem_subgroupOf.2 (congruenceSubgroup_antitone F n (show m0 ≤ m0 + 1 by omega)
        (Subgroup.mem_subgroupOf.1 hk))
    exact mem_stabilizerOf.1 (hm0 hk')
  haveI : FiniteDimensional ℂ (fixedVectors σ ((congruenceSubgroup F n (m0 + 1)).subgroupOf (levi F n β))) :=
    hadm.2 _ hKc hKo
  have hv' : (⟨v, hvK⟩ : fixedVectors σ ((congruenceSubgroup F n (m0 + 1)).subgroupOf (levi F n β))) ≠ 0 :=
    fun h0 => hv (congrArg Subtype.val h0)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (fixedVectors σ ((congruenceSubgroup F n (m0 + 1)).subgroupOf (levi F n β))),
      f ⟨v, hvK⟩ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv' ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  let E := fixedContragredientEquiv (ρ := σ) hadm.1 hKc hKo
  let x := E.symm f
  have hx : x.1.1 v ≠ 0 := by
    have h1 : E x = f := E.apply_symm_apply f
    rw [fixedContragredientEquiv_apply] at h1
    have h2 := restrictFixed_apply σ _ x ⟨v, hvK⟩
    rw [h1] at h2
    rw [← h2]
    exact hf
  have hφ : ∀ ij : LeviIndex n β, (fun ij : LeviIndex n β =>
      UpperTheory.V.Z.Gam.ballInd (m0 + 1) ((1 : Matrix (Fin n) (Fin n) F) ij.1.1 ij.1.2)) ij ∈
      GroundTheory.LocalField.schwartzBruhat F := fun ij => UpperTheory.V.Z.Gam.ballInd_mem _ _
  have e1 := (h _ hφ v x.1.1 x.1.2).2.2
  have e2 := (h' _ hφ v x.1.1 x.1.2).2.2
  apply RatFE.unique e1 e2
  intro t
  refine ⟨((t + 1 : ℝ) : ℂ), by simp, ?_⟩
  have hfun : (fun m => leviIntegrand σ κ (leviTensor β fun ij : LeviIndex n β =>
        UpperTheory.V.Z.Gam.ballInd (m0 + 1) ((1 : Matrix (Fin n) (Fin n) F) ij.1.1 ij.1.2)) v x.1.1
        ((t + 1 : ℝ) : ℂ) m) =
      (((congruenceSubgroup F n (m0 + 1)).subgroupOf (levi F n β) : Subgroup (levi F n β)) :
        Set (levi F n β)).indicator (fun _ => x.1.1 v) := by
    funext m
    by_cases hm : m ∈ (congruenceSubgroup F n (m0 + 1)).subgroupOf (levi F n β)
    · rw [Set.indicator_of_mem (show m ∈ (((congruenceSubgroup F n (m0 + 1)).subgroupOf (levi F n β) :
        Subgroup (levi F n β)) : Set (levi F n β)) from hm)]
      have hm' : (m : GL (Fin n) F) ∈ congruenceSubgroup F n (m0 + 1) := Subgroup.mem_subgroupOf.1 hm
      unfold leviIntegrand
      rw [UpperTheory.V.Z.Gam.leviTensor_ball_of_mem hm', eq_one_of_mem_compact κ hκ hKc hm,
        detPow_of_mem_integralGL (congruenceSubgroup_le F n (m0 + 1) hm') _,
        (mem_fixedVectors.1 hvK) m hm]
      simp
    · rw [Set.indicator_of_notMem (show m ∉ (((congruenceSubgroup F n (m0 + 1)).subgroupOf (levi F n β) :
        Subgroup (levi F n β)) : Set (levi F n β)) from hm)]
      unfold leviIntegrand
      rw [UpperTheory.V.Z.Gam.leviTensor_ball_of_notMem hr (fun h => hm (Subgroup.mem_subgroupOf.2 h))]
      simp
  have hKset : (((congruenceSubgroup F n (m0 + 1)).subgroupOf (levi F n β) : Subgroup (levi F n β)) :
      Set (levi F n β)) = (fun m : levi F n β => ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) ⁻¹'
        {M : Matrix (Fin n) (Fin n) F | ∀ i j, M i j - (1 : Matrix (Fin n) (Fin n) F) i j ∈
          GroundTheory.LocalField.valBall F ((m0 + 1 : ℕ) : ℤ)} := by
    ext m
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage, Set.mem_setOf_eq,
      mem_congruenceSubgroup_iff]
    constructor
    · intro hm i j
      exact UpperTheory.V.Z.Gam.mem_valBall_iff_val_le.2 (hm.2 i j)
    · intro hm
      have hall := fun i j => UpperTheory.V.Z.Gam.mem_valBall_iff_val_le.1 (hm i j)
      exact ⟨UpperTheory.V.Z.Gam.mem_integralGL_of_congr hr hall, hall⟩
  have hT : MeasurableSet {M : Matrix (Fin n) (Fin n) F | ∀ i j, M i j - (1 : Matrix (Fin n) (Fin n) F) i j ∈
      GroundTheory.LocalField.valBall F ((m0 + 1 : ℕ) : ℤ)} := by
    have hB : MeasurableSet (GroundTheory.LocalField.valBall F ((m0 + 1 : ℕ) : ℤ) : Set F) :=
      (GroundTheory.LocalField.isCompact_valBall _).isClosed.measurableSet
    have e : {M : Matrix (Fin n) (Fin n) F | ∀ i j, M i j - (1 : Matrix (Fin n) (Fin n) F) i j ∈
        GroundTheory.LocalField.valBall F ((m0 + 1 : ℕ) : ℤ)} =
        ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) F => M i j - (1 : Matrix (Fin n) (Fin n) F) i j) ⁻¹'
          (GroundTheory.LocalField.valBall F ((m0 + 1 : ℕ) : ℤ) : Set F) := by
      ext M
      simp
    rw [e]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      hB.preimage (((measurable_pi_apply j).comp (measurable_pi_apply i)).sub_const _)
  show (∫ m, leviIntegrand σ κ (leviTensor β fun ij : LeviIndex n β =>
        UpperTheory.V.Z.Gam.ballInd (m0 + 1) ((1 : Matrix (Fin n) (Fin n) F) ij.1.1 ij.1.2)) v x.1.1
        ((t + 1 : ℝ) : ℂ) m ∂μ) ≠ 0
  rw [hfun, integral_indicator_const (μ := μ) _ ?hm]
  · have hpos : 0 < μ.real (((congruenceSubgroup F n (m0 + 1)).subgroupOf (levi F n β) : Subgroup (levi F n β)) :
        Set (levi F n β)) :=
      ENNReal.toReal_pos (hKo.measure_ne_zero μ ⟨1, Subgroup.one_mem _⟩) hKc.measure_lt_top.ne
    exact smul_ne_zero hpos.ne' hx
  · rw [hKset]
    exact hT.preimage ((comap_measurable Units.val).comp
      (@measurable_subtype_coe (GL (Fin n) F)
        (MeasurableSpace.comap Units.val GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix) _))
