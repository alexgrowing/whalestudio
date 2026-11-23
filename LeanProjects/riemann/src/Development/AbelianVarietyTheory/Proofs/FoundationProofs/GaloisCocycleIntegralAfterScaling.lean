import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoefficientRingFiniteExtensionPadicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import ReciprocityTheory.GaloisValuations.ArithOfA
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.CocInt

theorem norm_natCast_lt_one (l : ℕ) [Fact l.Prime] : ‖((l:ℕ) : Qbar l)‖ < 1 := by
  have : ((l:ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [this, PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem norm_le_one_of_mem {l : ℕ} [Fact l.Prime] (c : Coef l) {y : Qbar l} (hy : y ∈ c.O) : ‖y‖ ≤ 1 := by
  haveI := c.fin
  exact (GlobalTheory.isIntegral_padicInt_iff_norm_le_one y).1
    ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨y, hy⟩ : c.O)).map c.O.val)

theorem exists_field_of_coef {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ K₀ : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] K₀ ∧ ∀ y ∈ c.O, y ∈ K₀ := by
  haveI := c.fin
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] c.O).FG)
  haveI : Finite ((fun y : c.O => (y : Qbar l)) '' (s : Set c.O)) := (s.finite_toSet.image _).to_subtype
  refine ⟨IntermediateField.adjoin ℚ_[l] ((fun y : c.O => (y : Qbar l)) '' (s : Set c.O)),
    IntermediateField.finiteDimensional_adjoin fun z _ => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral, ?_⟩
  intro y hy
  suffices key : ∀ a : c.O, a ∈ Submodule.span ℤ_[l] (s : Set c.O) →
      (a : Qbar l) ∈ IntermediateField.adjoin ℚ_[l] ((fun y : c.O => (y : Qbar l)) '' (s : Set c.O)) from
    key ⟨y, hy⟩ (by rw [hs]; trivial)
  intro a ha
  induction ha using Submodule.span_induction with
  | mem a ha => exact IntermediateField.subset_adjoin _ _ ⟨a, ha, rfl⟩
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul r a _ ha =>
    show ((r • a : c.O) : Qbar l) ∈ _
    rw [Subalgebra.coe_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) ha

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem colRep_apply (W : R2 Ω l) (s : G ℚ Ω) (v : Fin 2 → Qbar l) : Loc.colRep W s v = mat W s *ᵥ v := by
  simp [Loc.colRep, mat, Matrix.toLin'_apply]

theorem mat_mul (W : R2 Ω l) (a b : G ℚ Ω) : mat W (a * b) = mat W a * mat W b := by
  simp [mat, map_mul]

theorem coc {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) (a b : G ℚ Ω) :
    z (a * b) = z a + mat W a *ᵥ z b := by
  rw [((mem_Z1_iff_cocycle _ _).1 hz).2, colRep_apply]

theorem coc_one {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) : z 1 = 0 := by
  have h := coc hz 1 1
  rw [one_mul] at h
  have hm : mat W 1 = 1 := by simp [mat]
  rw [hm, Matrix.one_mulVec] at h
  exact left_eq_add.1 h

theorem coc_inv {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) (a : G ℚ Ω) :
    z a⁻¹ = -(mat W a⁻¹ *ᵥ z a) := by
  have h := coc hz a⁻¹ a
  rw [inv_mul_cancel, coc_one hz] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem coc_conj {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) (g t : G ℚ Ω)
    (x : Fin 2 → Qbar l) (ht : z t = mat W t *ᵥ x - x) :
    z (g * t * g⁻¹) = mat W (g * t * g⁻¹) *ᵥ (mat W g *ᵥ x - z g) - (mat W g *ᵥ x - z g) := by
  have h1 : mat W (g * t * g⁻¹) * mat W g = mat W g * mat W t := by
    rw [← mat_mul, ← mat_mul, inv_mul_cancel_right]
  have h2 : mat W (g * t) * mat W g⁻¹ = mat W (g * t * g⁻¹) := (mat_mul W _ _).symm
  rw [coc hz, coc hz, coc_inv hz, ht]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_mulVec, h1, h2]
  abel

theorem coc_finext (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (K₀ : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K₀] (n : ℕ)
    (θ : Γ → (Fin n → PadicAlgCl l) → (Fin n → PadicAlgCl l)) (c : Γ → Fin n → PadicAlgCl l)
    (hθ : ∀ (L : IntermediateField ℚ_[l] (PadicAlgCl l)), K₀ ≤ L → ∀ g v, (∀ j, v j ∈ L) → ∀ j, θ g v j ∈ L)
    (hc1 : c 1 = 0) (hc : Continuous c)
    (hcoc : ∀ g h, c (g * h) = c g + θ g (c h)) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ K₀ ≤ E ∧ ∀ g j, c g j ∈ E := by
  obtain ⟨ι, _, K, hK, hcov⟩ := GlobalTheory.CompactRepField.exists_countable_family l
  let H : ι → Subgroup Γ := fun i =>
    { carrier := {g | ∀ j, c g j ∈ K₀ ⊔ K i}
      one_mem' := by
        intro j
        rw [hc1]; exact zero_mem _
      mul_mem' := fun {g h} hg hh j => by
        rw [hcoc]
        exact add_mem (hg j) (hθ _ le_sup_left g _ hh j)
      inv_mem' := fun {g} hg j => by
        have h1 := hcoc g⁻¹ g
        rw [inv_mul_cancel, hc1] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm]
        exact neg_mem (hθ _ le_sup_left _ _ hg j) }
  have hcl : ∀ i, IsClosed (H i : Set Γ) := fun i => by
    haveI := hK i
    haveI : FiniteDimensional ℚ_[l] (K₀ ⊔ K i).toSubalgebra.toSubmodule :=
      (inferInstance : FiniteDimensional ℚ_[l] (K₀ ⊔ K i : IntermediateField ℚ_[l] (PadicAlgCl l)))
    have : (H i : Set Γ) = ⋂ j, (fun g => c g j) ⁻¹' ((K₀ ⊔ K i).toSubalgebra.toSubmodule : Set (PadicAlgCl l)) := by
      ext g
      rw [Set.mem_iInter]
      exact Iff.rfl
    rw [this]
    exact isClosed_iInter fun j =>
      (Submodule.closed_of_finiteDimensional (K₀ ⊔ K i).toSubalgebra.toSubmodule).preimage
        ((continuous_apply j).comp hc)
  have hun : ⋃ i, (H i : Set Γ) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨i, hi⟩ := hcov (Set.range (c g)) (Set.finite_range _)
    exact Set.mem_iUnion.2 ⟨i, fun j => (le_sup_right : K i ≤ K₀ ⊔ K i) (hi ⟨j, rfl⟩)⟩
  obtain ⟨i, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hun
  have hop : IsOpen (H i : Set Γ) := Subgroup.isOpen_of_mem_nhds _ (mem_interior_iff_mem_nhds.1 hx)
  haveI : Finite (Γ ⧸ H i) := Subgroup.quotient_finite_of_isOpen _ hop
  have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l]
      (Set.range fun q : (Γ ⧸ H i) × Fin n => c q.1.out q.2)) := by
    haveI : Finite (Set.range fun q : (Γ ⧸ H i) × Fin n => c q.1.out q.2) := (Set.finite_range _).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  haveI := hfd
  haveI := hK i
  refine ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun q : (Γ ⧸ H i) × Fin n => c q.1.out q.2) ⊔ (K₀ ⊔ K i),
    inferInstance, le_sup_left.trans le_sup_right, fun g j => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H i) g
  have hg : g = (g : Γ ⧸ H i).out * (h : Γ)⁻¹ := by
    rw [hh, mul_inv_cancel_right]
  rw [hg, hcoc]
  refine add_mem ?_ (hθ _ (le_sup_left.trans le_sup_right) _ _ (fun k => ?_) j)
  · exact (le_sup_left :
        IntermediateField.adjoin ℚ_[l] (Set.range fun q : (Γ ⧸ H i) × Fin n => c q.1.out q.2) ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨((g : Γ ⧸ H i), j), rfl⟩)
  · exact (le_sup_right : K₀ ⊔ K i ≤ _) ((H i).inv_mem h.2 k)

theorem values_finExt [IsAlgClosure ℚ Ω] (W : R2 Ω l) (K₀ : IntermediateField ℚ_[l] (Qbar l))
    [FiniteDimensional ℚ_[l] K₀] (hW : ∀ s i j, mat W s i j ∈ K₀) {z : G ℚ Ω → Fin 2 → Qbar l}
    (hz : z ∈ Z1 (Loc.colRep W)) :
    ∃ E : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] E ∧ K₀ ≤ E ∧ ∀ s i, z s i ∈ E := by
  haveI : CompactSpace (G ℚ Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))
  refine coc_finext l (G ℚ Ω) K₀ 2 (fun g v => mat W g *ᵥ v) z ?_ (coc_one hz) ((mem_Z1_iff_cocycle _ _).1 hz).1
    (fun g h => coc hz g h)
  intro L hL g v hv j
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun k _ => mul_mem (hL (hW _ _ _)) (hv k)

theorem norm_mulVec_le {c : Coef l} (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (hM : ∀ i j, M i j ∈ c.O)
    (v : Fin 2 → Qbar l) (i : Fin 2) : ‖(M *ᵥ v) i‖ ≤ ‖v 0‖ + ‖v 1‖ := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul] <;>
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_mem c (hM _ _))

end GlobalTheory.CocInt

namespace GlobalTheory.CocInt

open GlobalTheory.CocInt
open scoped Pointwise

theorem integral_after_scaling : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (c : Coef l) (z : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) → z ∈ Z1 (Loc.colRep W) → Unr W z → ∀ A : ValuationSubring Ω, ∃ (c' : Coef l) (k : ℕ), c.O ≤ c'.O ∧ (∀ s i, ((l : ℕ) : Qbar l) ^ k * z s i ∈ c'.O) ∧ (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c'.O) ∧ ∀ s ∈ Ine (F := ℚ) B, ((l : ℕ) : Qbar l) ^ k • z s = mat W s *ᵥ x - x) ∧ (Triv W A z → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c'.O) ∧ ∀ s ∈ Dec (F := ℚ) A, ((l : ℕ) : Qbar l) ^ k • z s = mat W s *ᵥ x - x) ∧ (Gr W A z → ∃ x ∈ c'.O, ∀ s ∈ Dec (F := ℚ) A, ((l : ℕ) : Qbar l) ^ k * z s 1 = mat W s 1 1 * x - x) := by
  intro l _ Ω _ _ _ S W c z _ hWint hWunr hz hzU A
  classical
  haveI : CompactSpace (G ℚ Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))
  choose B hB x hx using hzU

  let X : Pl → Fin 2 → Qbar l := fun q =>
    if h : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal then (if q ∈ S then x q h else 0) else 0
  have hX : ∀ q (h : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal), ∀ s ∈ Ine (F := ℚ) (B q h), z s = mat W s *ᵥ X q - X q := by
    intro q h s hs
    by_cases hq : q ∈ S
    · simp only [X, dif_pos h, if_pos hq]
      exact hx q h s hs
    · have h1 : W s = 1 := hWunr q hq (B q h) (hB q h) hs
      have hm : mat W s = 1 := by simp [mat, h1]
      simp only [X, dif_pos h, if_neg hq]
      rw [hx q h s hs, hm]
      simp
  have hXS : ∀ q, q ∉ S → X q = 0 := by
    intro q hq
    simp only [X]
    split_ifs <;> rfl
  let xT : Fin 2 → Qbar l := if h : Triv W A z then h.choose else 0
  let xG : Qbar l := if h : Gr W A z then h.choose else 0
  obtain ⟨K₀, hK₀fd, hK₀⟩ := exists_field_of_coef c
  let f : ((↥S × Fin 2) ⊕ Fin 2) ⊕ Unit → Qbar l :=
    Sum.elim (Sum.elim (fun p => X p.1.1 p.2) xT) (fun _ => xG)
  haveI hfd₁ : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) := by
    haveI : Finite (Set.range f) := (Set.finite_range _).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun z _ => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  haveI := hK₀fd
  obtain ⟨E, hEfd, hK₁E, hzE⟩ := values_finExt W (K₀ ⊔ IntermediateField.adjoin ℚ_[l] (Set.range f))
    (fun s i j => le_sup_left (b := IntermediateField.adjoin ℚ_[l] (Set.range f)) (hK₀ _ (hWint s i j))) hz
  have hfE : ∀ p, f p ∈ E := fun p =>
    hK₁E (le_sup_right (a := K₀) (IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩))
  have hOE : ∀ y ∈ c.O, y ∈ E := fun y hy =>
    hK₁E (le_sup_left (b := IntermediateField.adjoin ℚ_[l] (Set.range f)) (hK₀ y hy))
  obtain ⟨c', hc'⟩ := GlobalTheory.T.exists_coefficientRing_finiteExtension_padic l E hEfd

  obtain ⟨C, hC⟩ := (isCompact_univ.image ((mem_Z1_iff_cocycle _ _).1 hz).1).isBounded.exists_norm_le
  let M : ℝ := max C 0 + ∑ p, ‖f p‖
  have hM0 : 0 ≤ M := add_nonneg (le_max_right _ _) (Finset.sum_nonneg fun p _ => norm_nonneg _)
  have hfM : ∀ p, ‖f p‖ ≤ M := fun p =>
    (Finset.single_le_sum (f := fun p => ‖f p‖) (fun p _ => norm_nonneg _) (Finset.mem_univ p)).trans
      (le_add_of_nonneg_left (le_max_right _ _))
  have hzM : ∀ s i, ‖z s i‖ ≤ M := fun s i =>
    ((norm_le_pi_norm (z s) i).trans (hC _ ⟨s, Set.mem_univ _, rfl⟩)).trans
      ((le_max_left _ _).trans (le_add_of_nonneg_right (Finset.sum_nonneg fun p _ => norm_nonneg _)))
  have hXE : ∀ q j, X q j ∈ E := by
    intro q j
    by_cases hq : q ∈ S
    · exact hfE (Sum.inl (Sum.inl (⟨q, hq⟩, j)))
    · rw [hXS q hq]; exact zero_mem _
  have hXM : ∀ q j, ‖X q j‖ ≤ M := by
    intro q j
    by_cases hq : q ∈ S
    · exact hfM (Sum.inl (Sum.inl (⟨q, hq⟩, j)))
    · rw [hXS q hq]; simpa using hM0
  set N : ℝ := 3 * M + 1 with hN
  have hN0 : 0 < N := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hN0) (norm_natCast_lt_one l)
  have hkN : ‖((l : ℕ) : Qbar l)‖ ^ k * N ≤ 1 := by
    have := mul_lt_mul_of_pos_right hk hN0
    rw [inv_mul_cancel₀ hN0.ne'] at this
    exact this.le
  have key : ∀ y ∈ E, ‖y‖ ≤ N → ((l : ℕ) : Qbar l) ^ k * y ∈ c'.O := by
    intro y hy hyN
    refine (hc' _).2 ⟨mul_mem (pow_mem (IntermediateField.natCast_mem _ _) _) hy, ?_⟩
    rw [norm_mul, norm_pow]
    exact (mul_le_mul_of_nonneg_left hyN (pow_nonneg (norm_nonneg _) _)).trans hkN
  have hMN : M ≤ N := by rw [hN]; linarith
  refine ⟨c', k, fun y hy => (hc' y).2 ⟨hOE y hy, norm_le_one_of_mem c hy⟩,
    fun s i => key _ (hzE s i) ((hzM s i).trans hMN), ?_, ?_, ?_⟩
  · intro q hq B' hB'
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (hB q hq) hB'
    refine ⟨((l : ℕ) : Qbar l) ^ k • (mat W g *ᵥ X q - z g), fun i => ?_, fun s hs => ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul]
      refine key _ ?_ ?_
      · rw [Pi.sub_apply]
        refine sub_mem ?_ (hzE g i)
        simp only [Matrix.mulVec, dotProduct]
        exact sum_mem fun j _ => mul_mem (hOE _ (hWint _ _ _)) (hXE q j)
      · rw [Pi.sub_apply]
        refine (norm_sub_le _ _).trans ?_
        have := norm_mulVec_le (c := c) (mat W g) (hWint g) (X q) i
        have h0 := hXM q 0
        have h1 := hXM q 1
        have h2 := hzM g i
        rw [hN]; linarith
    · have ht := ReciprocityTheory.Gal.conj_mem_Ine_smul (F := ℚ) (A := g • B q hq) (γ := g⁻¹) hs
      rw [inv_inv, inv_smul_smul] at ht
      have h := coc_conj hz g (g⁻¹ * s * g) (X q) (hX q hq _ ht)
      rw [show g * (g⁻¹ * s * g) * g⁻¹ = s by group] at h
      rw [h, Matrix.mulVec_smul, smul_sub]
  · intro hT
    have hxT : ∀ s ∈ Dec (F := ℚ) A, z s = mat W s *ᵥ xT - xT := by
      simp only [xT, dif_pos hT]
      exact hT.choose_spec
    refine ⟨((l : ℕ) : Qbar l) ^ k • xT, fun i => ?_, fun s hs => ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul]
      exact key _ (hfE (Sum.inl (Sum.inr i))) ((hfM (Sum.inl (Sum.inr i))).trans hMN)
    · rw [hxT s hs, Matrix.mulVec_smul, smul_sub]
  · intro hG
    have hxG : ∀ s ∈ Dec (F := ℚ) A, z s 1 = mat W s 1 1 * xG - xG := by
      simp only [xG, dif_pos hG]
      exact hG.choose_spec
    refine ⟨((l : ℕ) : Qbar l) ^ k * xG, key _ (hfE (Sum.inr ())) ((hfM (Sum.inr ())).trans hMN), fun s hs => ?_⟩
    rw [hxG s hs]
    ring

end GlobalTheory.CocInt
