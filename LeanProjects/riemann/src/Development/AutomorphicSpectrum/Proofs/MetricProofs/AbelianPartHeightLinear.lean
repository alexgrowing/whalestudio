import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeOrthogonalSumStatement
import GroundTheory.HeightsAndTheta.Heights.Slopes.PCanonicalFiltration
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DegreeTopEqArithDegree
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PInteriorDichotomy
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ClearDenominatorsLattice

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights Polynomial

theorem exists_integral_generator (E : Type) [Field E] [NumberField E] :
    ∃ (θ : 𝓞 E) (m : ℤ[X]), m.Monic ∧ aeval θ m = 0 ∧ m.natDegree = Module.finrank ℚ E ∧
      ∀ a : 𝓞 E, ∃ (n : ℤ) (P : ℤ[X]), n ≠ 0 ∧ (n : 𝓞 E) * a = aeval θ P := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  have halg : IsAlgebraic ℤ α :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic α)
  obtain ⟨n, hn, hint⟩ := halg.exists_integral_multiple
  set β : E := n • α with hβ
  have hnq : ((n : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hn
  have hαβ : α = ((n : ℚ))⁻¹ • β := by
    rw [hβ, ← Int.cast_smul_eq_zsmul ℚ n α, smul_smul, inv_mul_cancel₀ hnq, one_smul]
  have htop : IntermediateField.adjoin ℚ {β} = ⊤ := by
    rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff, hαβ]
    exact (IntermediateField.adjoin ℚ {β}).smul_mem (IntermediateField.mem_adjoin_simple_self ℚ β)
  have hintQ : IsIntegral ℚ β := Algebra.IsIntegral.isIntegral β
  let θ : 𝓞 E := ⟨β, hint⟩
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := RingOfIntegers.coe_injective
  have hcoe : ∀ P : ℤ[X], algebraMap (𝓞 E) E (aeval θ P) = aeval β P := fun P => by
    have := aeval_algHom_apply (IsScalarTower.toAlgHom ℤ (𝓞 E) E) θ P
    exact this.symm
  refine ⟨θ, minpoly ℤ β, minpoly.monic hint, ?_, ?_, ?_⟩
  · apply hinj
    rw [hcoe, minpoly.aeval, map_zero]
  · have h1 := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
    have h2 := IntermediateField.adjoin.finrank hintQ
    rw [htop, IntermediateField.finrank_top', h1, (minpoly.monic hint).natDegree_map] at h2
    exact h2.symm
  · intro a
    have ha : (a : E) ∈ Algebra.adjoin ℚ {β} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hintQ.isAlgebraic, htop]
      exact Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨Q, hQ⟩ := ha
    obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) Q
    refine ⟨b, IsLocalization.integerNormalization (nonZeroDivisors ℤ) Q, nonZeroDivisors.coe_ne_zero b, ?_⟩
    apply hinj
    have hQ' : aeval β Q = (a : E) := hQ
    rw [hcoe, ← aeval_map_algebraMap ℚ, hb, map_mul, map_intCast, zsmul_eq_mul, map_mul, map_intCast, hQ']

theorem ker_aeval_prod_le {L V : Type} [Field L] [AddCommGroup V] [Module L V] (T : Module.End L V) (S : Finset L) :
    LinearMap.ker (aeval T (∏ c ∈ S, (X - C c))) ≤ ⨆ c ∈ S, Module.End.eigenspace T c := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Module.End.one_eq_id]
  | insert c S hc ih =>
    rw [Finset.prod_insert hc]
    have hcop : IsCoprime (X - C c) (∏ d ∈ S, (X - C d)) :=
      IsCoprime.prod_right fun d hd => isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.2 (fun h : c = d => hc (by rw [h]; exact hd))).isUnit
    rw [← sup_ker_aeval_eq_ker_aeval_mul_of_coprime T hcop, Finset.iSup_insert]
    refine sup_le_sup ?_ ih
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Module.End.mem_eigenspace_iff]
    simpa [sub_eq_zero] using hx

theorem iSup_eigSp_eq_top {E L V ι : Type} [Field E] [NumberField E] [Field L] [CharZero L] [AddCommGroup V] [Module L V]
    [Fintype ι] (ρ : 𝓞 E →+* Module.End L V) (σ : ι → (𝓞 E →+* L)) (hσ : Function.Injective σ)
    (hcard : Fintype.card ι = Module.finrank ℚ E) : ⨆ s, eigSp ρ (σ s) = ⊤ := by
  classical
  obtain ⟨θ, m, hmon, hm0, hdeg, hgen⟩ := exists_integral_generator E
  have hagree : ∀ (τ : 𝓞 E →+* L) (P : ℤ[X]), τ (aeval θ P) = aeval (τ θ) P := fun τ P =>
    (aeval_algHom_apply τ.toIntAlgHom θ P).symm
  have hinjc : Function.Injective fun s => σ s θ := by
    intro s t hst
    apply hσ
    ext a
    obtain ⟨n, P, hn, hP⟩ := hgen a
    have h1 := hagree (σ s) P
    have h2 := hagree (σ t) P
    have hst' : σ s θ = σ t θ := hst
    rw [hst', ← h2, ← hP, map_mul, map_mul, map_intCast, map_intCast] at h1
    exact mul_left_cancel₀ (by exact_mod_cast hn) h1
  set S : Finset L := Finset.univ.image fun s => σ s θ with hS
  have hScard : S.card = Module.finrank ℚ E := by
    rw [hS, Finset.card_image_of_injective _ hinjc, Finset.card_univ, hcard]
  set mL : L[X] := m.map (algebraMap ℤ L) with hmL
  have hmLmon : mL.Monic := hmon.map _
  have hmLdeg : mL.natDegree = Module.finrank ℚ E := by rw [hmL, hmon.natDegree_map, hdeg]
  have hprodmon : (∏ c ∈ S, (X - C c)).Monic := monic_prod_of_monic _ _ fun c _ => monic_X_sub_C c
  have hprodeg : (∏ c ∈ S, (X - C c) : L[X]).natDegree = Module.finrank ℚ E := by
    rw [natDegree_prod_of_monic _ _ fun c _ => monic_X_sub_C c]
    simp [hScard]
  have hdvd : (∏ c ∈ S, (X - C c)) ∣ mL := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro c _ d _ hcd
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hcd).isUnit
    · intro c hc
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hc
      rw [dvd_iff_isRoot, IsRoot.def, hmL, eval_map_algebraMap, ← hagree, hm0, map_zero]
  have heq : mL = ∏ c ∈ S, (X - C c) :=
    eq_of_monic_of_dvd_of_natDegree_le hprodmon hmLmon hdvd (by rw [hmLdeg, hprodeg])
  have hρ : ∀ P : ℤ[X], aeval (ρ θ) P = ρ (aeval θ P) := fun P =>
    aeval_algHom_apply ρ.toIntAlgHom θ P
  have hT : aeval (ρ θ) (∏ c ∈ S, (X - C c)) = 0 := by
    rw [← heq, hmL, aeval_map_algebraMap, hρ, hm0, map_zero]
  rw [eq_top_iff]
  have hker : (⊤ : Submodule L V) ≤ LinearMap.ker (aeval (ρ θ) (∏ c ∈ S, (X - C c))) := by
    rw [hT, LinearMap.ker_zero]
  refine hker.trans ((ker_aeval_prod_le (ρ θ) S).trans (iSup₂_le fun c hc => ?_))
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hc
  refine le_trans ?_ (le_iSup _ s)
  intro x hx
  rw [Module.End.mem_eigenspace_iff] at hx
  have hpow : ∀ k : ℕ, ((ρ θ) ^ k) x = (σ s θ) ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]
  have hP : ∀ P : ℤ[X], (aeval (ρ θ) P) x = (aeval (σ s θ) P) • x := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, add_smul]
    | monomial k a =>
      simp only [aeval_monomial, Module.End.mul_apply, hpow, eq_intCast, map_intCast]
      rw [Module.End.intCast_apply, mul_smul, Int.cast_smul_eq_zsmul]
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  intro a
  obtain ⟨n, P, hn, hnP⟩ := hgen a
  have h2 := hP P
  rw [hρ, ← hagree, ← hnP, map_mul, map_mul, map_intCast, map_intCast] at h2
  rw [Module.End.mul_apply, Module.End.intCast_apply, mul_smul, ← Int.cast_smul_eq_zsmul L n] at h2
  exact smul_right_injective V (by exact_mod_cast hn : (n : L) ≠ 0) h2

section Lattice

variable {L V : Type} [Field L] [NumberField L] [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
  [IsScalarTower (𝓞 L) L V]

theorem exists_smul_mem_of_span {Λ : Submodule (𝓞 L) V} (h : Submodule.span L (Λ : Set V) = ⊤) (p : V) :
    ∃ b : 𝓞 L, b ≠ 0 ∧ b • p ∈ Λ :=
  by apply _root_.UpperTheory.Reformulated.B.ClearDenominatorsLattice.exists_integer_smul_mem_of_span_top <;> assumption

end Lattice

namespace LinPt

variable {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] {V : Type} [AddCommGroup V]
  [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V)

theorem img_eq (s : Ψ ⊕ Ψ) :
    A.img s = (((eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L)).comap A.Λ.subtype).map A.f := by
  unfold img eig
  rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]

theorem saturation_iSup_img (hcard : 2 * Fintype.card Ψ = Module.finrank ℚ E) :
    CanonicalFiltration.saturation A.Bq (⨆ s, A.img s) = ⊤ := by
  have htop := iSup_eigSp_eq_top A.ρ A.σ A.σ_bij.1 (by rw [Fintype.card_sum, ← hcard]; ring)
  have key : ∀ x : V, ∃ b : 𝓞 L, b ≠ 0 ∧ ∃ h : b • x ∈ A.Λ, A.f ⟨b • x, h⟩ ∈ ⨆ s, A.img s := by
    intro x
    have hx : x ∈ ⨆ s, eigSp A.ρ (A.σ s) := htop ▸ Submodule.mem_top
    refine Submodule.iSup_induction _
      (motive := fun x => ∃ b : 𝓞 L, b ≠ 0 ∧ ∃ h : b • x ∈ A.Λ, A.f ⟨b • x, h⟩ ∈ ⨆ s, A.img s) hx ?_ ?_ ?_
    · intro s x hx
      obtain ⟨b, hb, hbx⟩ := exists_smul_mem_of_span A.span x
      refine ⟨b, hb, hbx, Submodule.mem_iSup_of_mem s ?_⟩
      rw [img_eq]
      refine Submodule.mem_map_of_mem ?_
      show b • x ∈ eigSp A.ρ (A.σ s)
      rw [← algebraMap_smul L b x]
      exact Submodule.smul_mem _ _ hx
    · have h0 : (1 : 𝓞 L) • (0 : V) ∈ A.Λ := by simp
      refine ⟨1, one_ne_zero, h0, ?_⟩
      have e : (⟨(1 : 𝓞 L) • (0 : V), h0⟩ : A.Λ) = 0 := Subtype.ext (by simp)
      rw [e, map_zero]
      exact Submodule.zero_mem _
    · rintro x y ⟨b, hb, hbx, hfx⟩ ⟨c, hc, hcy, hfy⟩
      have e0 : (b * c) • (x + y) = c • (b • x) + b • (c • y) := by
        rw [smul_add, smul_smul, smul_smul, mul_comm c b]
      have h1 : (b * c) • (x + y) ∈ A.Λ := by
        rw [e0]
        exact A.Λ.add_mem (A.Λ.smul_mem _ hbx) (A.Λ.smul_mem _ hcy)
      have e : (⟨(b * c) • (x + y), h1⟩ : A.Λ) = c • ⟨b • x, hbx⟩ + b • ⟨c • y, hcy⟩ := Subtype.ext e0
      refine ⟨b * c, mul_ne_zero hb hc, h1, ?_⟩
      rw [e, map_add, map_smul, map_smul]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hfx) (Submodule.smul_mem _ _ hfy)
  rw [eq_top_iff]
  intro y _
  obtain ⟨a, x, ha, hfx⟩ := A.full y
  obtain ⟨b, hb, hbx, hf⟩ := key x
  refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
  have e : (⟨b • (x : V), hbx⟩ : A.Λ) = b • x := Subtype.ext rfl
  rw [e, map_smul, hfx, smul_smul] at hf
  exact hf

theorem sum_normDegree_img_le (hcard : 2 * Fintype.card Ψ = Module.finrank ℚ E) :
    ∑ s, A.Bq.normDegree (A.img s) ≤ A.Bq.normDegree ⊤ := by
  have hI := GlobalTheory.T.normalized_degree_orthogonal_sum L A.Bq (Ψ ⊕ Ψ) A.img (fun s s' h => by
    rw [img_eq, img_eq]
    exact A.orth s s' h)
  have hr : A.Bq.rank (⨆ s, A.img s) = A.Bq.rank ⊤ := by
    have := CanonicalFiltration.rank_saturation A.Bq (⨆ s, A.img s)
    rw [A.saturation_iSup_img hcard] at this
    exact this.symm
  rw [← hI.1]
  exact div_le_div_of_nonneg_right (CanonicalFiltration.degree_le_of_le_of_rank_eq A.Bq le_top hr)
    (Nat.cast_nonneg _)

end LinPt

theorem abelianPart_height_linear :
    ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (lab lab' : Ψ → Ψ ⊕ Ψ) (m N : ℕ) (La : ℝ), 2 * Fintype.card Ψ = Module.finrank ℚ E → ((lab = Sum.inl ∧ lab' = Sum.inr) ∨ (lab = Sum.inr ∧ lab' = Sum.inl)) → 1 ≤ Fintype.card Ψ * m → 1 ≤ La → ((Fintype.card Ψ * N : ℕ) : ℝ) ≤ Real.exp La → Module.finrank (𝓞 L) A.Bq.carrier ≤ Fintype.card Ψ * N → (∀ τ, A.Bq.rank (A.img (lab τ)) ≤ m) → A.Bq.slopeMax ≤ ((C₀ * Real.log (2 + Module.finrank (𝓞 L) A.Bq.carrier + max (-A.Bq.normDegree ⊤) 0) : ℝ) : EReal) → (∀ τ, |A.Bq.normDegree (A.img (lab τ)) - A.Bq.normDegree (A.img (lab' τ))| ≤ C₀ * N * La) → ∑ τ, A.Bq.normDegree (A.img (lab τ)) ≤ C * (Fintype.card Ψ * m) * La := by
  intro C₀ hC₀
  obtain ⟨C, hC⟩ := LowerBound.InteriorDichotomy.proof C₀ 0 C₀ hC₀ le_rfl hC₀
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A lab lab' m N La hcard hlab hfm hLa hexp hrank hm hslope hdd
  set f : ℝ := (Fintype.card Ψ : ℝ) with hf
  set h : ℝ := -A.Bq.normDegree ⊤ with hh
  set n : ℝ := (Module.finrank (𝓞 L) A.Bq.carrier : ℝ) with hn
  set g : ℝ := max ((Fintype.card Ψ * N : ℕ) : ℝ) 1 with hg
  set x : ℝ := ∑ τ, A.Bq.normDegree (A.img (lab τ)) with hx
  set y : ℝ := ∑ τ, A.Bq.normDegree (A.img (lab' τ)) with hy
  have hLa0 : 0 < La := by linarith
  have hf0 : 0 ≤ f := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hg1 : 1 ≤ g := le_max_right _ _
  have hfN : f * N ≤ g := by
    have : ((Fintype.card Ψ * N : ℕ) : ℝ) ≤ g := le_max_left _ _
    simpa [hf] using this
  have hng : n ≤ g := by
    have h1 : n ≤ ((Fintype.card Ψ * N : ℕ) : ℝ) := Nat.cast_le.2 hrank
    exact h1.trans (le_max_left _ _)
  have hfj : (1 : ℝ) ≤ f * m := by
    have : ((1 : ℕ) : ℝ) ≤ ((Fintype.card Ψ * m : ℕ) : ℝ) := by exact_mod_cast hfm
    simpa [hf] using this
  have hgexp : g ≤ Real.exp La := max_le hexp (Real.one_le_exp hLa0.le)

  set μ : ℝ := C₀ * Real.log (2 + n + max h 0) with hμ
  have harg : 1 ≤ 2 + n + max h 0 := by
    have h1 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h2 := le_max_right h 0
    linarith
  have hμ0 : 0 ≤ μ := mul_nonneg hC₀ (Real.log_nonneg harg)
  have hμg : μ ≤ C₀ * Real.log (2 + g + max h 0) :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) hC₀
  have hxle : x ≤ f * m * μ := by
    have h1 : ∀ τ, A.Bq.normDegree (A.img (lab τ)) ≤ m * μ := fun τ =>
      (HermitianBundle.normDegree_le_rank_mul A.Bq _ μ hslope).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hm τ) hμ0)
    calc x ≤ ∑ _τ : Ψ, (m : ℝ) * μ := Finset.sum_le_sum fun τ _ => h1 τ
      _ = f * m * μ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hf]; ring

  have hsum : x + y ≤ -h := by
    have h1 := A.sum_normDegree_img_le hcard
    rw [Fintype.sum_sum_type] at h1
    rw [hh, neg_neg]
    rcases hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1
    · rw [hx, hy]; linarith
  have hxy : x - y ≤ f * (C₀ * N * La) := by
    have h1 : x - y ≤ ∑ _τ : Ψ, C₀ * N * La := by
      rw [hx, hy, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun τ _ => (le_abs_self _).trans (hdd τ)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    exact h1
  have hfC : f * (C₀ * N * La) ≤ C₀ * g * La := by
    have : C₀ * (f * N) * La ≤ C₀ * g * La :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfN hC₀) hLa0.le
    calc f * (C₀ * N * La) = C₀ * (f * N) * La := by ring
      _ ≤ _ := this
  have hyp : LowerBound.InteriorDichotomy.Hyp C₀ 0 C₀ h (-x) g (f * m) La :=
    { one_le_g := hg1
      one_le_fj := hfj
      g_le_exp := hgexp
      one_le_La := hLa
      lower := by
        have h1 : f * m * μ ≤ f * m * (C₀ * Real.log (2 + g + max h 0)) :=
          mul_le_mul_of_nonneg_left hμg (by linarith)
        have h2 : f * m * (C₀ * Real.log (2 + g + max h 0) + 0 * La) =
            f * m * (C₀ * Real.log (2 + g + max h 0)) := by ring
        rw [h2]
        linarith
      upper := by linarith }
  have hfin := hC h (-x) g (f * m) La hyp
  have h1 : C * (f * m) * La ≤ max C 0 * (f * m) * La :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)) hLa0.le
  have h2 : x ≤ C * (f * m) * La := by linarith
  exact h2.trans h1

end GlobalTheory.CompanionTheory.Ar.Cusp
