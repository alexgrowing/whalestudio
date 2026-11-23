import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice

noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_sub_mem_intLoc (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    ∃ x : E, y - (1 : Fv F v) ⊗ₜ[F] x ∈ intLoc F E v := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz =>
    obtain ⟨x, hx⟩ := hy
    obtain ⟨x', hx'⟩ := hz
    refine ⟨x + x', ?_⟩
    rw [TensorProduct.tmul_add, add_sub_add_comm]
    exact add_mem hx hx'
  | tmul a e =>
    obtain ⟨m, hm, he⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
    have he' : IsIntegral ℤ (m • e) := he e (Finset.mem_singleton_self e)
    have hmF : (m : F) ≠ 0 := by exact_mod_cast hm
    have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
    have hcont : Continuous fun z : Fv F v => (m : F)⁻¹ • a - z := continuous_sub_left _
    obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) F v).exists_mem_open
      (hO.preimage hcont) ⟨(m : F)⁻¹ • a, by simp⟩
    refine ⟨k • (m • e), ?_⟩
    have hk' : (m : F)⁻¹ • a - algebraMap F (Fv F v) k ∈ v.adicCompletionIntegers F := hk
    have h := tmul_mem_intLoc (E := E) hk' ⟨m • e, he'⟩
    convert h using 1
    change _ = ((m : F)⁻¹ • a - algebraMap F (Fv F v) k) ⊗ₜ[F] (m • e)
    rw [TensorProduct.sub_tmul, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      ← Int.cast_smul_eq_zsmul F m e, inv_smul_smul₀ hmF]

theorem isIntegral_of_absBar_le_one (v : HeightOneSpectrum (𝓞 F)) (x : E)
    (hx : ∀ τ : E →ₐ[F] FvBar F v, absBar F v (τ x) ≤ 1) :
    ∃ p : Polynomial (v.valuationSubringAtPrime F), p.Monic ∧
      p.eval₂ ((algebraMap F E).comp (v.valuationSubringAtPrime F).subtype) x = 0 := by
  classical
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hmon := minpoly.monic hint
  have h1 : (minpoly F x).map (algebraMap F (FvBar F v)) ∈ Polynomial.lifts (valBar F v).integer.subtype := by
    refine Polynomial.Splits.mem_lift_of_roots_mem_range (IsAlgClosed.splits _) (hmon.map _) _ fun a ha => ?_
    have ha' : a ∈ (minpoly F x).rootSet (FvBar F v) := by
      rw [Polynomial.rootSet_def]; simpa [Polynomial.aroots_def] using ha
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at ha'
    obtain ⟨τ, rfl⟩ := ha'
    exact ⟨⟨τ x, hx τ⟩, rfl⟩
  have h2 : minpoly F x ∈ Polynomial.lifts (v.valuationSubringAtPrime F).subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts] at h1 ⊢
    intro n
    obtain ⟨c, hc⟩ := h1 n
    have h3 : absBar F v (algebraMap F (FvBar F v) ((minpoly F x).coeff n)) ≤ 1 := by
      rw [← Polynomial.coeff_map, ← hc]; exact c.2
    rw [IsScalarTower.algebraMap_apply F (Fv F v) (FvBar F v), absBar_algebraMap] at h3
    have h4 : Valued.v (algebraMap F (Fv F v) ((minpoly F x).coeff n)) ≤ 1 :=
      Valued.toNormedField.norm_le_one_iff.1 (by exact_mod_cast h3)
    refine ⟨⟨(minpoly F x).coeff n, ?_⟩, rfl⟩
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le h4
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic h2 hmon
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval₂_map, hq]
  exact minpoly.aeval F x

theorem one_tmul_mem_intLoc (v : HeightOneSpectrum (𝓞 F)) (x : E)
    (hx : absFin F v ((1 : Fv F v) ⊗ₜ[F] x) ≤ 1) : (1 : Fv F v) ⊗ₜ[F] x ∈ intLoc F E v := by
  let : Algebra (v.valuationSubringAtPrime F) E :=
    ((algebraMap F E).comp (v.valuationSubringAtPrime F).subtype).toAlgebra
  have : IsScalarTower (𝓞 F) (v.valuationSubringAtPrime F) E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : IsIntegral (v.valuationSubringAtPrime F) x :=
    isIntegral_of_absBar_le_one v x fun τ => by simpa using (absFin_le_iff F v).1 hx τ
  obtain ⟨⟨s, hs⟩, h2⟩ := IsIntegral.exists_multiple_integral_of_isLocalization v.asIdeal.primeCompl x h1
  have h3 : IsIntegral ℤ ((s : F) • x) := isIntegral_trans _ h2
  have hv : v.valuation F (s : F) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hs
  have hs0 : (s : F) ≠ 0 := fun e => by simp [e] at hv
  have h4 : algebraMap F (Fv F v) (s : F)⁻¹ ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (s : F)⁻¹).trans_le (by rw [map_inv₀, hv, inv_one])
  have h := tmul_mem_intLoc (E := E) h4 ⟨_, h3⟩
  convert h using 1
  change _ = (algebraMap F (Fv F v) (s : F)⁻¹) ⊗ₜ[F] ((s : F) • x)
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, inv_smul_smul₀ hs0]

theorem mem_intLoc_iff_absFin_le_one {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v ⊗[F] E} :
    y ∈ intLoc F E v ↔ absFin F v y ≤ 1 := by
  refine ⟨absFin_le_one_of_mem_intLoc, fun hy => ?_⟩
  obtain ⟨x, hx⟩ := exists_sub_mem_intLoc v y
  have h1 : absFin F v ((1 : Fv F v) ⊗ₜ[F] x) ≤ 1 := by
    have := absFin_add_le F v y (-(y - (1 : Fv F v) ⊗ₜ[F] x))
    rw [absFin_neg, ← sub_eq_add_neg, sub_sub_cancel] at this
    exact this.trans (max_le hy (absFin_le_one_of_mem_intLoc hx))
  simpa using add_mem hx (one_tmul_mem_intLoc v x h1)

theorem algebraMap_basis_repr {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) (i : ι) :
    algebraMap (Fv F v) (FvBar F v) ((Algebra.TensorProduct.basis (Fv F v) b.traceDual).repr y i) =
      ∑ τ : E →ₐ[F] FvBar F v, finEmb F v τ y * τ (b i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz, add_mul, Finset.sum_add_distrib]
  | tmul a e =>
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul,
      ← IsScalarTower.algebraMap_apply, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply,
      trace_eq_sum_embeddings, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [finEmb_tmul, map_mul]; ring

theorem absFin_eq_zero_iff {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v ⊗[F] E} : absFin F v y = 0 ↔ y = 0 := by
  refine ⟨fun hy => ?_, fun h => by rw [h, absFin_zero]⟩
  have h0 : ∀ τ : E →ₐ[F] FvBar F v, finEmb F v τ y = 0 := fun τ =>
    (absBar_eq_zero F v).1 (le_antisymm ((absFin_le_iff F v).1 hy.le τ) zero_le)
  let b := Module.finBasis F E
  refine (Algebra.TensorProduct.basis (Fv F v) b.traceDual).ext_elem fun i => ?_
  refine (algebraMap (Fv F v) (FvBar F v)).injective ?_
  rw [algebraMap_basis_repr]
  simp [h0]

theorem normFin_le_one_iff {v : HeightOneSpectrum (𝓞 F)} {m n : Type} [Fintype m] [Fintype n]
    {y : Matrix m n (Fv F v ⊗[F] E)} : normFin F v y ≤ 1 ↔ ∀ i j, y i j ∈ intLoc F E v := by
  simp only [normFin_le_iff, mem_intLoc_iff_absFin_le_one]

theorem mem_stabLoc_stdLattice_iff_htFin_eq_one {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {v : HeightOneSpectrum (𝓞 F)} {g : GLoc σ J v} :
    g ∈ stabLoc σ J (stdLattice E n) v ↔ htFin F v (matHom _ σ J g) = 1 := by
  rw [htFin, htOf_eq_one]
  constructor
  · intro hg
    have h1 := normFin_conj_le_one isLatticeFrame_one hg
    have h2 := normFin_conj_le_one isLatticeFrame_one (inv_mem hg)
    rw [map_one, inv_one, one_mul, mul_one] at h1 h2
    rw [map_inv] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have key : ∀ (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)), normFin F v M ≤ 1 → ∀ y,
        y ∈ latLoc F (stdLattice E n) v → M *ᵥ y ∈ latLoc F (stdLattice E n) v := fun M hM y hy =>
      mem_latLoc_stdLattice.2 fun i => by
        change ∑ j, M i j * y j ∈ _
        exact sum_mem fun j _ => mul_mem (normFin_le_one_iff.1 hM i j) (mem_latLoc_stdLattice.1 hy j)
    refine mem_stabLoc.2 fun y => ⟨key _ h1 y, fun hy => ?_⟩
    have := key _ h2 _ hy
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

theorem intLoc_absFin_htFin (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) :
    (∀ y : Fv F v ⊗[F] E, y ∈ intLoc F E v ↔ absFin F v y ≤ 1) ∧
    (∀ y : Fv F v ⊗[F] E, absFin F v y = 0 ↔ y = 0) ∧
    ∀ g : GLoc σ J v, g ∈ stabLoc σ J (stdLattice E n) v ↔ htFin F v (matHom _ σ J g) = 1 :=
  ⟨fun _ => mem_intLoc_iff_absFin_le_one, fun _ => absFin_eq_zero_iff,
    fun _ => mem_stabLoc_stdLattice_iff_htFin_eq_one⟩

end GlobalTheory.AdelicU

end
