import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdDefs

noncomputable section

open MeasureTheory Measure GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal ENNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

set_option linter.unusedSectionVars false

namespace UpperTheory.V.Z.Gam

theorem ldShape_one (q : ℂ) : LdShape q 1 0 := ⟨1, 1, 0, by simp, by simp, one_ne_zero, by simp⟩

theorem ldShape_mul {q : ℂ} {γ₁ γ₂ : RatFunc ℂ} {k₁ k₂ : ℕ} (h₁ : LdShape q γ₁ k₁) (h₂ : LdShape q γ₂ k₂) :
    LdShape q (γ₁ * γ₂) (k₁ + k₂) := by
  obtain ⟨P₁, c₁, j₁, he₁, hd₁, hc₁, rfl⟩ := h₁
  obtain ⟨P₂, c₂, j₂, he₂, hd₂, hc₂, rfl⟩ := h₂
  have hP₁ : P₁ ≠ 0 := by
    rintro rfl
    simp at he₁
  have hP₂ : P₂ ≠ 0 := by
    rintro rfl
    simp at he₂
  refine ⟨P₁ * P₂, c₁ * c₂, j₁ + j₂, by simp [he₁, he₂], ?_, mul_ne_zero hc₁ hc₂, ?_⟩
  · rw [Polynomial.natDegree_mul hP₁ hP₂, hd₁, hd₂]
  · rw [div_mul_div_comm, Polynomial.mul_comp, map_mul, map_mul, map_mul,
      zpow_add₀ RatFunc.X_ne_zero]
    ring

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  [∀ n : ℕ, MeasurableSpace (GL (Fin n) F)] [∀ n : ℕ, BorelSpace (GL (Fin n) F)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

variable (F W) in

def LdMulti (ψ : AddChar F Circle) (r : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = r →
  ∀ (d : ι → ℕ) [∀ i, NeZero (d i)] (μ : ∀ i, Measure (GL (Fin (d i)) F))
    [∀ i, (μ i).IsHaarMeasure]
    (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SecondCountableTopology H]
    (ρ : Representation ℂ ((∀ i, GL (Fin (d i)) F) × H) W), IsAdmissible ρ → ρ.IsIrreducible →
    ∀ α : ι → ℂ, (∀ i, α i ≠ 0) →
      (∀ i v, ρ (Pi.mulSingle i (centralUnif F (d i)), 1) v = α i • v) →
      (∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ),
        ∃ C : Set (∀ i, GL (Fin (d i)) F), IsCompact C ∧
          ∀ x, ℓ (ρ (x, 1) v) ≠ 0 → ∃ j : ι → ℤ, (fun i => centralUnif F (d i) ^ j i) * x ∈ C) →
    ∃ γ : RatFunc ℂ, LdShape ((GroundTheory.LocalField.residueCard F : ℕ) : ℂ) γ
        (∑ i, if d i = 1 ∧ ∀ g ∈ integralGL F (d i), ρ (Pi.mulSingle i g, 1) = 1 then 1 else 0) ∧
      ∀ Ψ : ∀ i, Matrix (Fin (d i)) (Fin (d i)) F → ℂ,
      (∀ i, IsSchwartzBruhat (Ψ i)) → ∀ w : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ),
        RatFE F γ (fun s => ∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ)
          (fun s => ∫ x, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s x
            ∂Measure.pi μ)

theorem ldMulti_zero (ψ : AddChar F Circle) : LdMulti F W ψ 0 := by
  intro ι _ _ hcard d _ μ _ H _ _ _ _ _ _ _ ρ _ _ α _ _ _
  haveI : IsEmpty ι := Fintype.card_eq_zero_iff.1 hcard
  refine ⟨1, ?_, ?_⟩
  · simpa using ldShape_one ((GroundTheory.LocalField.residueCard F : ℕ) : ℂ)
  · intro Ψ _ w ℓ _
    have hx : ∀ x : (∀ i, GL (Fin (d i)) F), x = 1 := fun x => funext fun i => isEmptyElim i
    have hone : ℓ (ρ (1, 1) w) = ℓ w := by
      rw [Prod.mk_one_one, map_one]
      rfl
    have hA : ∀ s, (∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ) = ℓ w := by
      intro s
      have hf : multiA ρ Ψ w ℓ s = fun _ => ℓ w := by
        funext x
        rw [hx x]
        simpa [multiA] using hone
      rw [hf, integral_const, Measure.pi_of_empty (x := 1)]
      simp
    have hB : ∀ s, (∫ x, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s x
        ∂Measure.pi μ) = ℓ w := by
      intro s
      have hf : multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s = fun _ => ℓ w := by
        funext x
        rw [hx x]
        simpa [multiB] using hone
      rw [hf, integral_const, Measure.pi_of_empty (x := 1)]
      simp
    refine ⟨RatFunc.C (ℓ w), 0, fun s _ => ?_, fun s _ => ?_⟩
    · beta_reduce
      rw [hA]
      simp
    · beta_reduce
      rw [hB]
      simp

theorem ldMulti_succ (hB : LdBlock) {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {r : ℕ}
    (ih : LdMulti F W ψ r) : LdMulti F W ψ (r + 1) := by
  intro ι _ _ hcard d _ μ _ H _ _ _ _ _ _ _ ρ hadm hirr α hα hcent hsupp
  obtain ⟨a⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hcard' : Fintype.card {i // i ≠ a} = r := by
    have h := Set.card_ne_eq a
    simp only [Set.coe_setOf] at h
    omega
  let σ : Representation ℂ (GL (Fin (d a)) F × (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H)) W :=
    ρ.comp (peelFst d H a).symm.toMonoidHom
  let ρ' : Representation ℂ (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × (GL (Fin (d a)) F × H)) W :=
    ρ.comp (peelSnd d H a).symm.toMonoidHom
  have hσ : ∀ g y h, σ (g, (y, h)) = ρ (splitSymm d a g y, h) := by
    intro g y h
    show ρ ((peelFst d H a).symm (g, (y, h))) = _
    rw [peelFst_symm_apply]
  have hρ' : ∀ y g h, ρ' (y, (g, h)) = ρ (splitSymm d a g y, h) := by
    intro y g h
    show ρ ((peelSnd d H a).symm (y, (g, h))) = _
    rw [peelSnd_symm_apply]
  have hσadm : IsAdmissible σ := (isAdmissible_comp_iff (peelFst d H a).symm ρ).2 hadm
  have hσirr : σ.IsIrreducible := (isIrreducible_comp_iff (peelFst d H a).symm ρ).2 hirr
  have hσsm : ∀ ℓ : Module.Dual ℂ W, ℓ ∈ smoothVectors σ.dual ↔ ℓ ∈ smoothVectors ρ.dual :=
    fun ℓ => mem_smoothVectors_dual_comp_iff (peelFst d H a).symm ρ
  have hρ'adm : IsAdmissible ρ' := (isAdmissible_comp_iff (peelSnd d H a).symm ρ).2 hadm
  have hρ'irr : ρ'.IsIrreducible := (isIrreducible_comp_iff (peelSnd d H a).symm ρ).2 hirr
  have hρ'sm : ∀ ℓ : Module.Dual ℂ W, ℓ ∈ smoothVectors ρ'.dual ↔ ℓ ∈ smoothVectors ρ.dual :=
    fun ℓ => mem_smoothVectors_dual_comp_iff (peelSnd d H a).symm ρ
  clear_value σ ρ'
  have hσ1 : ∀ g, σ (g, 1) = ρ (Pi.mulSingle a g, 1) := by
    intro g
    rw [show ((g, 1) : GL (Fin (d a)) F × (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H)) = (g, (1, 1))
      from rfl, hσ, splitSymm_mulSingle_self]
  have hρ'1 : ∀ (j : {i // i ≠ a}) (g : GL (Fin (d j)) F),
      ρ' (Pi.mulSingle j g, 1) = ρ (Pi.mulSingle (j : ι) g, 1) := by
    intro j g
    rw [show ((Pi.mulSingle j g, 1) : ((i : {i // i ≠ a}) → GL (Fin (d i)) F) × (GL (Fin (d a)) F × H))
      = (Pi.mulSingle j g, (1, 1)) from rfl, hρ', splitSymm_one_mulSingle]
  have hσcent : ∀ v, σ (centralUnif F (d a), 1) v = α a • v := by
    intro v
    rw [hσ1]
    exact hcent a v
  have hρ'cent : ∀ (j : {i // i ≠ a}) v, ρ' (Pi.mulSingle j (centralUnif F (d j)), 1) v = α j • v := by
    intro j v
    rw [hρ'1]
    exact hcent j v
  have hσsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors σ.dual, ∃ C : Set (GL (Fin (d a)) F), IsCompact C ∧
      ∀ g, ℓ (σ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F (d a) ^ j * g ∈ C := by
    intro v ℓ hℓ
    obtain ⟨C, hC, hCx⟩ := hsupp v ℓ ((hσsm ℓ).1 hℓ)
    refine ⟨(fun x => x a) '' C, hC.image (continuous_apply a), fun g hg => ?_⟩
    rw [hσ1] at hg
    obtain ⟨j, hj⟩ := hCx _ hg
    exact ⟨j a, _, hj, by simp⟩
  have hρ'supp : ∀ v : W, ∀ ℓ ∈ smoothVectors ρ'.dual,
      ∃ C : Set ((i : {i // i ≠ a}) → GL (Fin (d i)) F), IsCompact C ∧
        ∀ y, ℓ (ρ' (y, 1) v) ≠ 0 → ∃ j : {i // i ≠ a} → ℤ,
          (fun i : {i // i ≠ a} => centralUnif F (d i) ^ j i) * y ∈ C := by
    intro v ℓ hℓ
    obtain ⟨C, hC, hCx⟩ := hsupp v ℓ ((hρ'sm ℓ).1 hℓ)
    refine ⟨(fun x (k : {i // i ≠ a}) => x (k : ι)) '' C,
      hC.image (continuous_pi fun k => continuous_apply (k : ι)), fun y hy => ?_⟩
    rw [show ((y, 1) : ((i : {i // i ≠ a}) → GL (Fin (d i)) F) × (GL (Fin (d a)) F × H))
      = (y, (1, 1)) from rfl, hρ'] at hy
    obtain ⟨j, hj⟩ := hCx _ hy
    exact ⟨fun k => j k, _, hj, funext fun k => centralPow_mul_splitSymm_apply j y k⟩
  haveI := hσirr
  obtain ⟨γa, s₁, hblk⟩ := exists_blockFE (μ a) hσadm hψ hψ1 hσcent hσsupp
  have hsha := hB F (d a) (μ a) _ W σ hσadm hσirr (α a) (hα a) hσcent hσsupp ψ hψ hψ1 γa
    (fun Φ hΦ v ℓ hℓ => (hblk Φ hΦ v ℓ hℓ).2.2)
  obtain ⟨γ', hsh', hFE'⟩ := ih {i // i ≠ a} hcard' (fun i => d i) (fun i => μ i)
    (GL (Fin (d a)) F × H) ρ' hρ'adm hρ'irr (fun i => α i) (fun i => hα i) hρ'cent hρ'supp
  refine ⟨γa * γ', ?_, ?_⟩
  · have h := ldShape_mul hsha hsh'
    rw [Fintype.sum_eq_add_sum_subtype_ne _ a]
    simp only [hσ1, hρ'1] at h
    exact h
  · intro Ψ hΨ w ℓ hℓ
    obtain ⟨s₂, hint⟩ := exists_integrable_multi ρ hadm.1 hα hcent hsupp μ
    obtain ⟨s₃, hint'⟩ := exists_integrable_multi ρ' hρ'adm.1 (α := fun i => α i) (fun i => hα i)
      hρ'cent hρ'supp (fun i => μ i)
    have hstab : (stabilizerOf σ w : Set (GL (Fin (d a)) F × (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H)))
        ∈ nhds ((1, 1) : GL (Fin (d a)) F × (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H)) :=
      (hσadm.1 w).mem_nhds (Subgroup.one_mem _)
    rw [mem_nhds_prod_iff] at hstab
    obtain ⟨u, hu, v, hv, huv⟩ := hstab
    obtain ⟨m0, hm0⟩ := (hΨ a).exists_congruence_invariant
    have hu' : u ∩ (congruenceSubgroup F (d a) m0 : Set (GL (Fin (d a)) F)) ∈ nhds (1 : GL (Fin (d a)) F) :=
      Filter.inter_mem hu ((isOpen_congruenceSubgroup F (d a) m0).mem_nhds (Subgroup.one_mem _))
    obtain ⟨K₁, hK₁c, hK₁u⟩ := exists_openSubgroup_isCompact_subset hu'
    obtain ⟨K₂, hK₂c, hK₂v⟩ := exists_openSubgroup_isCompact_subset hv
    let Ka : Subgroup (GL (Fin (d a)) F) := (K₁ : Subgroup (GL (Fin (d a)) F))
    let K' : Subgroup (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H) :=
      (K₂ : Subgroup (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H))
    have hKc : IsCompact ((Ka.prod K' : Subgroup _) : Set (GL (Fin (d a)) F × (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H))) := by
      rw [Subgroup.coe_prod]
      exact hK₁c.prod hK₂c
    have hKo : IsOpen ((Ka.prod K' : Subgroup _) : Set (GL (Fin (d a)) F × (((i : {i // i ≠ a}) → GL (Fin (d i)) F) × H))) := by
      rw [Subgroup.coe_prod]
      exact K₁.isOpen.prod K₂.isOpen
    haveI : FiniteDimensional ℂ (fixedVectors σ (Ka.prod K')) := hσadm.2 _ hKc hKo
    have hKa : Ka ≤ integralGL F (d a) := fun k hk => congruenceSubgroup_le F (d a) m0 (hK₁u hk).2
    have hΨinv : ∀ k ∈ Ka, ∀ X : Matrix (Fin (d a)) (Fin (d a)) F, Ψ a ((k : Matrix (Fin (d a)) (Fin (d a)) F) * X) = Ψ a X := fun k hk X => (hm0 k (hK₁u hk).2 X).1
    have hΦinv : ∀ k ∈ Ka, ∀ X : Matrix (Fin (d a)) (Fin (d a)) F, GJMatrix.localMatrixFourier ψ (Ψ a) (X * (k : Matrix (Fin (d a)) (Fin (d a)) F)) =
        GJMatrix.localMatrixFourier ψ (Ψ a) X := fun k hk X =>
      localMatrixFourier_mul_right_of_invariant (hKa hk)
        (fun x => (hm0 k⁻¹ (Subgroup.inv_mem _ (hK₁u hk).2) x).1) X
    have hwfix : w ∈ fixedVectors σ (Ka.prod K') := fun h hh =>
      huv ⟨(hK₁u (Subgroup.mem_prod.1 hh).1).1, hK₂v (Subgroup.mem_prod.1 hh).2⟩
    let b := Module.finBasis ℂ (fixedVectors σ (Ka.prod K'))
    let L : Fin (Module.finrank ℂ (fixedVectors σ (Ka.prod K'))) → Module.Dual ℂ W := fun i =>
      (((extendFixed hσadm.1 hKc hKo (b.coord i) : fixedVectors (contragredient σ) (Ka.prod K')) :
        smoothVectors σ.dual) : Module.Dual ℂ W)
    have hL : ∀ i, L i ∈ smoothVectors σ.dual := fun i =>
      ((extendFixed hσadm.1 hKc hKo (b.coord i) : fixedVectors (contragredient σ) (Ka.prod K')) :
        smoothVectors σ.dual).2
    let m : ((i : {i // i ≠ a}) → GL (Fin (d i)) F) → smoothVectors σ.dual := fun y =>
      contragredient σ ((1, (y, 1))⁻¹) ⟨ℓ, (hσsm ℓ).2 hℓ⟩
    have hm : ∀ y v, (m y : Module.Dual ℂ W) v = ℓ (ρ (splitSymm d a 1 y, 1) v) := by
      intro y v
      simp only [m]
      rw [contragredient_apply_apply, inv_inv, hσ]
    have hsplit : ∀ g y, ρ (splitSymm d a g y, 1) = ρ (splitSymm d a 1 y, 1) * σ (g, 1) := by
      intro g y
      rw [← hσ, ← hσ, ← map_mul]
      congr 1
      ext <;> simp
    have hρ'y : ∀ y v, ρ' (y, 1) v = ρ (splitSymm d a 1 y, 1) v := by
      intro y v
      rw [show ((y, 1) : ((i : {i // i ≠ a}) → GL (Fin (d i)) F) × (GL (Fin (d a)) F × H))
        = (y, (1, 1)) from rfl, hρ']
    let e := (Homeomorph.piSplitAt a (fun i => GL (Fin (d i)) F)).toMeasurableEquiv
    have hmp : MeasurePreserving e (Measure.pi μ) ((μ a).prod (Measure.pi fun j : {i // i ≠ a} => μ j)) :=
      measurePreserving_piSplitAt d a μ
    have he : ∀ g y, e.symm (g, y) = splitSymm d a g y := fun g y => rfl
    have hA : ∀ s : ℂ, max s₁ (max s₂ s₃) < s.re →
        (∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ) =
          ∑ i, blockA (μ a) σ (Ψ a) w (L i) s *
            ∫ y, multiA ρ' (fun j => Ψ j) (b i : W) ℓ s y ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
      intro s hs
      have hs₁ : s₁ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
      have hs₂ : s₂ < s.re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
      have hs₃ : s₃ < s.re := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs
      have hinner : ∀ y, (∫ g, multiA ρ Ψ w ℓ s (splitSymm d a g y) ∂μ a) =
          ∑ i, blockA (μ a) σ (Ψ a) w (L i) s * multiA ρ' (fun j => Ψ j) (b i : W) ℓ s y := by
        intro y
        have hpt : ∀ g, multiA ρ Ψ w ℓ s (splitSymm d a g y) =
            (∏ j : {i // i ≠ a}, Ψ j ↑(y j) * detPow (y j) s) *
              (Ψ a ↑g * detPow g s * (m y : Module.Dual ℂ W) (σ (g, 1) w)) := by
          intro g
          simp only [multiA]
          rw [prod_splitSymm (fun i (x : GL (Fin (d i)) F) => Ψ i ↑x * detPow x s), hsplit, Module.End.mul_apply, hm]
          ring
        simp_rw [hpt]
        rw [integral_const_mul]
        have hsum := blockA_eq_sum hσadm.1 hKc hKo hKa hΨinv hwfix
          (fun μ' hμ' => (hblk (Ψ a) (hΨ a) w μ' hμ').1 s hs₁) (m y)
        simp only [blockA] at hsum ⊢
        rw [hsum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [multiA]
        rw [hρ'y, ← hm]
        ring
      have hintA := (hint Ψ hΨ w ℓ hℓ).1 s hs₂
      calc (∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ)
          = ∫ z, multiA ρ Ψ w ℓ s (e.symm z) ∂(μ a).prod (Measure.pi fun j : {i // i ≠ a} => μ j) := by
            rw [← hmp.integral_comp']
            simp
        _ = ∫ y, ∫ g, multiA ρ Ψ w ℓ s (splitSymm d a g y) ∂μ a ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
            rw [integral_prod_symm]
            · rfl
            · apply (hmp.integrable_comp_emb e.measurableEmbedding
                (g := fun z => multiA ρ Ψ w ℓ s (e.symm z))).1
              simpa [Function.comp_def] using hintA
        _ = ∫ y, ∑ i, blockA (μ a) σ (Ψ a) w (L i) s * multiA ρ' (fun j => Ψ j) (b i : W) ℓ s y
              ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
            simp_rw [hinner]
        _ = _ := by
            rw [integral_finset_sum]
            · simp_rw [integral_const_mul]
            · intro i _
              exact ((hint' (fun j => Ψ j) (fun j => hΨ j) (b i : W) ℓ ((hρ'sm ℓ).2 hℓ)).1 s hs₃).const_mul _
    have hB' : ∀ s : ℂ, s.re < -max s₁ (max s₂ s₃) →
        (∫ x, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s x ∂Measure.pi μ) =
          ∑ i, blockB (μ a) σ (GJMatrix.localMatrixFourier ψ (Ψ a)) w (L i) s *
            ∫ y, multiB ρ' (fun j => GJMatrix.localMatrixFourier ψ (Ψ j)) (b i : W) ℓ s y
              ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
      intro s hs
      have hs₁ : s.re < -s₁ := lt_of_lt_of_le hs (neg_le_neg (le_max_left _ _))
      have hs₂ : s.re < -s₂ := lt_of_lt_of_le hs (neg_le_neg ((le_max_left _ _).trans (le_max_right _ _)))
      have hs₃ : s.re < -s₃ := lt_of_lt_of_le hs (neg_le_neg ((le_max_right _ _).trans (le_max_right _ _)))
      have hinner : ∀ y, (∫ g, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s
          (splitSymm d a g y) ∂μ a) =
          ∑ i, blockB (μ a) σ (GJMatrix.localMatrixFourier ψ (Ψ a)) w (L i) s *
            multiB ρ' (fun j => GJMatrix.localMatrixFourier ψ (Ψ j)) (b i : W) ℓ s y := by
        intro y
        have hpt : ∀ g, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s (splitSymm d a g y) =
            (∏ j : {i // i ≠ a}, GJMatrix.localMatrixFourier ψ (Ψ j) ↑(y j) * detPow (y j) (↑(d j) - s)) *
              (GJMatrix.localMatrixFourier ψ (Ψ a) ↑g * detPow g (↑(d a) - s) *
                (m y⁻¹ : Module.Dual ℂ W) (σ (g⁻¹, 1) w)) := by
          intro g
          simp only [multiB]
          rw [prod_splitSymm (fun i (x : GL (Fin (d i)) F) =>
              GJMatrix.localMatrixFourier ψ (Ψ i) ↑x * detPow x (↑(d i) - s)),
            splitSymm_inv, hsplit, Module.End.mul_apply, hm]
          ring
        simp_rw [hpt]
        rw [integral_const_mul]
        have hsum := blockB_eq_sum hσadm.1 hKc hKo hKa hΦinv hwfix
          (fun μ' hμ' => (hblk (Ψ a) (hΨ a) w μ' hμ').2.1 s hs₁) (m y⁻¹)
        simp only [blockB] at hsum ⊢
        rw [hsum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [multiB]
        rw [hρ'y, ← hm]
        ring
      have hintB := (hint (fun i => GJMatrix.localMatrixFourier ψ (Ψ i))
        (fun i => (hΨ i).localMatrixFourier hψ hψ1) w ℓ hℓ).2 s hs₂
      calc (∫ x, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s x ∂Measure.pi μ)
          = ∫ z, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s (e.symm z)
              ∂(μ a).prod (Measure.pi fun j : {i // i ≠ a} => μ j) := by
            rw [← hmp.integral_comp']
            simp
        _ = ∫ y, ∫ g, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s (splitSymm d a g y)
              ∂μ a ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
            rw [integral_prod_symm]
            · rfl
            · apply (hmp.integrable_comp_emb e.measurableEmbedding
                (g := fun z => multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s (e.symm z))).1
              simpa [Function.comp_def] using hintB
        _ = ∫ y, ∑ i, blockB (μ a) σ (GJMatrix.localMatrixFourier ψ (Ψ a)) w (L i) s *
              multiB ρ' (fun j => GJMatrix.localMatrixFourier ψ (Ψ j)) (b i : W) ℓ s y
              ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
            simp_rw [hinner]
        _ = _ := by
            rw [integral_finset_sum]
            · simp_rw [integral_const_mul]
            · intro i _
              exact ((hint' (fun j => GJMatrix.localMatrixFourier ψ (Ψ j))
                (fun j => (hΨ j).localMatrixFourier hψ hψ1) (b i : W) ℓ ((hρ'sm ℓ).2 hℓ)).2 s hs₃).const_mul _
    have hfe : RatFE F (γa * γ')
        (fun z => ∑ i ∈ Finset.univ, blockA (μ a) σ (Ψ a) w (L i) z *
          ∫ y, multiA ρ' (fun j => Ψ j) (b i : W) ℓ z y ∂Measure.pi (fun j : {i // i ≠ a} => μ j))
        (fun z => ∑ i ∈ Finset.univ, blockB (μ a) σ (GJMatrix.localMatrixFourier ψ (Ψ a)) w (L i) z *
          ∫ y, multiB ρ' (fun j => GJMatrix.localMatrixFourier ψ (Ψ j)) (b i : W) ℓ z y
            ∂Measure.pi (fun j : {i // i ≠ a} => μ j)) :=
      RatFE.sum Finset.univ fun i _ => RatFE.mul (hblk (Ψ a) (hΨ a) w (L i) (hL i)).2.2
        (hFE' (fun j => Ψ j) (fun j => hΨ j) (b i : W) ℓ ((hρ'sm ℓ).2 hℓ))
    exact hfe.congr ⟨max s₁ (max s₂ s₃), hA⟩ ⟨-max s₁ (max s₂ s₃), hB'⟩

theorem ldMulti_all (hB : LdBlock) {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∀ r, LdMulti F W ψ r
  | 0 => ldMulti_zero ψ
  | r + 1 => ldMulti_succ hB hψ hψ1 (ldMulti_all hB hψ hψ1 r)

end UpperTheory.V.Z.Gam
