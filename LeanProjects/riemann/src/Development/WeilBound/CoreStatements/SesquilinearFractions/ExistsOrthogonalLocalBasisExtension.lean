import Development.WeilBound.CoreStatements.SesquilinearFractions.AlgebraMapIntegralCoeffsRaw

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rank_free_prod (L : Type) [AddCommGroup L] [Module (𝓞 E) L] (p : ℕ) :
    Module.rank (𝓞 E) ((Fin p → 𝓞 E) × L) = p + Module.rank (𝓞 E) L := by
  have h := LinearMap.rank_range_add_rank_ker (LinearMap.fst (𝓞 E) (Fin p → 𝓞 E) L)
  rw [LinearMap.range_eq_top_of_surjective _ LinearMap.fst_surjective, rank_top, rank_fin_fun,
    LinearMap.ker_fst] at h
  rw [← h, ← (LinearEquiv.ofInjective (LinearMap.inr (𝓞 E) (Fin p → 𝓞 E) L)
    LinearMap.inr_injective).rank_eq]

theorem family_orthogonal_sum_injective (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (hdet : (gramE D x').det ≠ 0)
    (c : Fin p → 𝓞 E) (z : orthogonalFamilyAlt D x') (h : familyCombination D x' c + (z : D.La) = 0) : c = 0 ∧ z = 0 := by
  have hadd : ∀ u v w : D.La, sesq D u (v + w) = sesq D u v + sesq D u w := by
    intro u v w
    simp only [sesq, map_add, Int.cast_add, add_mul, Finset.sum_add_distrib]
  have hcomb : familyCombination D x' c = ∑ a, c a • x' a := rfl
  have hv : (gramE D x') *ᵥ (fun a => IsCMField.complexConj E ((c a : 𝓞 E) : E)) = 0 := by
    funext b
    have hb := congrArg (sesq D (x' b)) h
    have h0 : sesq D (x' b) 0 = 0 := by simp [sesq]
    have hz : sesq D (x' b) (z : D.La) = 0 := z.2 b
    rw [hadd, hcomb, sesq_integral_combination, hz, h0, _root_.add_zero] at hb
    simpa [Matrix.mulVec, dotProduct] using hb
  have hc0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hv
  have hc : c = 0 := by
    funext a
    have ha := congrFun hc0 a
    simp only [Pi.zero_apply, map_eq_zero] at ha
    first
      | simpa using ha
      | exact RingOfIntegers.coe_eq_zero_iff.mp ha
      | exact_mod_cast ha
  refine ⟨hc, ?_⟩
  subst hc
  have h1 : familyCombination D x' 0 = 0 := map_zero _
  rw [h1, _root_.zero_add] at h
  exact Submodule.coe_eq_zero.mp h

theorem finrank_orthogonal_family (D : Datum H) {p q : ℕ} (x' : Fin p → D.La) (ℓ : Nat.Primes) (hpq : p + q = D.p + D.q)
    (hdet : (gramE D x').det ≠ 0) (m : ℕ) (hm0 : m ≠ 0) (hm : ∀ y a, ∃ g : 𝓞 E, (g : E) = m * projectionCoeffs D x' y a) :
    Module.finrank (𝓞 E) (orthogonalFamilyAlt D x') = q := by
  classical
  haveI := D.fin
  set L2 := orthogonalFamilyAlt D x' with hL2
  let ψ : ((Fin p → 𝓞 E) × L2) →ₗ[𝓞 E] D.La := (familyCombination D x').coprod L2.subtype
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨c, z⟩ h
    obtain ⟨hc, hz⟩ := family_orthogonal_sum_injective D x' hdet c z h
    rw [hc, hz]
    rfl
  have hyp : ∀ y, orthogonalComponent D x' m hm y = m • y - familyCombination D x' (integralCoeffs D x' m hm y) := by
    intro y
    simp only [orthogonalComponent, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, Nat.cast_smul_eq_nsmul]
  let φ : D.La →ₗ[𝓞 E] (Fin p → 𝓞 E) × L2 :=
    (integralCoeffs D x' m hm).prod
      ((orthogonalComponent D x' m hm).codRestrict L2 (fun y => orthogonalComponent_mem D x' m hm hdet y))
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : integralCoeffs D x' m hm y = 0 := congrArg Prod.fst hy
    have h2 : orthogonalComponent D x' m hm y = 0 := by
      have h3 := congrArg (fun w => (w.2 : D.La)) hy
      simpa [φ] using h3
    rw [hyp, h1, map_zero, sub_zero] at h2
    exact nsmul_injective_lattice D hm0 (by rw [h2, smul_zero])
  have hr : Module.rank (𝓞 E) ((Fin p → 𝓞 E) × L2) = Module.rank (𝓞 E) D.La :=
    le_antisymm (LinearMap.rank_le_of_injective ψ hψ) (LinearMap.rank_le_of_injective φ hφ)
  rw [rank_free_prod, ← Module.finrank_eq_rank (𝓞 E) D.La, D.rank, ← hpq,
    ← Module.finrank_eq_rank (𝓞 E) L2] at hr
  norm_cast at hr
  omega

theorem exists_orthogonal_local_basis_extension (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes) (x' : Fin p → D.La) (hpq : p + q = D.p + D.q)
    (hdet : (gramE D x').det ≠ 0) (hlog : ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) :
    ∃ x : Fin p ⊕ Fin q → D.La, x ∘ Sum.inl = x' ∧ IsLocBasis (𝓞 E) ℓ x ∧
      ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0 := by
  classical
  obtain ⟨m, hmℓ, hm⟩ := exists_common_denominator_coeffs D x' ℓ hdet hlog
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hmℓ (dvd_zero _)
  haveI := D.fin
  haveI := D.proj
  set L2 := orthogonalFamilyAlt D x' with hL2
  have hfr : Module.finrank (𝓞 E) L2 = q := finrank_orthogonal_family D x' ℓ hpq hdet m hm0 hm
  obtain ⟨b0, hb0⟩ := exists_local_basis_cm_order.locBasis' (𝓞 E) (ℓ : ℕ) ℓ.prop (M := L2)
  let b : Fin q → L2 := b0 ∘ Fin.cast hfr.symm
  have hbli : LinearIndependent (𝓞 E) b := hb0.1.comp _ (Fin.cast_injective _)
  obtain ⟨n, hnℓ, hn⟩ := hb0.2
  have hrange : Set.range b = Set.range b0 := Function.Surjective.range_comp (fun i => ⟨Fin.cast hfr i, by ext; simp⟩) _
  have hyp : ∀ y, orthogonalComponent D x' m hm y = m • y - familyCombination D x' (integralCoeffs D x' m hm y) := by
    intro y
    simp only [orthogonalComponent, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, Nat.cast_smul_eq_nsmul]
  refine ⟨Sum.elim x' (fun j => (b j : D.La)), rfl, ⟨?_, ?_⟩, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    set z : L2 := ∑ j, g (Sum.inr j) • b j with hz
    have hzc : (z : D.La) = ∑ j, g (Sum.inr j) • (b j : D.La) := by simp [hz]
    have hpsi := family_orthogonal_sum_injective D x' hdet (fun a => g (Sum.inl a)) z (by rw [hzc]; exact hg)
    have hg2 : ∀ j, g (Sum.inr j) = 0 := Fintype.linearIndependent_iff.mp hbli _ hpsi.2
    rintro (a | j)
    · exact congrFun hpsi.1 a
    · exact hg2 j
  · refine ⟨m * n, ?_, ?_⟩
    · rw [ℓ.prop.dvd_mul]
      push_neg
      exact ⟨hmℓ, hnℓ⟩
    · intro y
      have hdec : m • y = familyCombination D x' (integralCoeffs D x' m hm y) + orthogonalComponent D x' m hm y := by
        rw [hyp]
        abel
      rw [_root_.mul_comm m n, mul_smul, hdec, smul_add]
      apply Submodule.add_mem
      · apply nsmul_mem
        show ∑ a, integralCoeffs D x' m hm y a • x' a ∈ _
        refine Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl a, rfl⟩))
      · have h1 := hn ⟨_, orthogonalComponent_mem D x' m hm hdet y⟩
        rw [← hrange] at h1
        have h2 := Submodule.mem_map_of_mem (f := L2.subtype) h1
        rw [Submodule.map_span] at h2
        have h3 := Submodule.span_mono (R := 𝓞 E) (s := L2.subtype '' Set.range b)
          (t := Set.range (Sum.elim x' (fun j => (b j : D.La)))) (by
            rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
            exact ⟨Sum.inr j, rfl⟩) h2
        simpa using h3
  · intro a j
    exact (b j).2 a

end GlobalTheory.CompanionTheory.Ar.Fl

end

namespace PositivityTheory.Xgf

theorem exists_orthogonal_local_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes) (x' : Fin p → D.La), p + q = D.p + D.q → (gramE D x').det ≠ 0 → (∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ = -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → ∃ x : Fin p ⊕ Fin q → D.La, x ∘ Sum.inl = x' ∧ IsLocBasis (𝓞 E) ℓ x ∧ ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0 :=
  fun _ _ _ _ _ D p q ℓ x' hpq hdet hlog => GlobalTheory.CompanionTheory.Ar.Fl.exists_orthogonal_local_basis_extension D p q ℓ x' hpq hdet hlog

end PositivityTheory.Xgf
