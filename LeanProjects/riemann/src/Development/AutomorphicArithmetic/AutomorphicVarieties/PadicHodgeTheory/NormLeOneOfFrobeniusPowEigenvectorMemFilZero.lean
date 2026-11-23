import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NormLeOneOfFrobeniusEigenvectorMemFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private theorem shift_prod {R : Type} [CommMonoid R] (a : ℕ → R) (f : ℕ) :
    (∏ i ∈ Finset.range f, a (i + 1)) * a 0 = (∏ i ∈ Finset.range f, a i) * a f := by
  rw [← Finset.prod_range_succ', Finset.prod_range_succ]

private theorem descend {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [IsDomain B]
    (PD : PeriodData G Qp K₀ K B BdR) (f : ℕ) (hσ : ∀ x, (PD.σ ^ f) x = x) (b : B) (δ : K₀) (hb : b ≠ 0)
    (hφ : (PD.φ ^ f) b = algebraMap K₀ B δ * b) (hF : ∀ i : ℕ, PD.ι ((PD.φ ^ i) b) ∈ PD.Fil 0) :
    ∃ (c : B) (x : Qp), c ≠ 0 ∧ PD.φ c = algebraMap Qp B x * c ∧ PD.ι c ∈ PD.Fil 0 ∧
      algebraMap Qp K₀ x = ∏ i ∈ Finset.range f, (PD.σ ^ i) δ := by
  have hinj : ∀ (i : ℕ) (y : B), y ≠ 0 → (PD.φ ^ i) y ≠ 0 := by
    intro i y hy h
    apply hy
    have h1 : Function.Injective (PD.φ ^ i) := by
      rw [AlgHom.coe_pow]; exact PD.φ_inj.iterate i
    exact h1 (h.trans (map_zero _).symm)
  have hK : ∀ (i : ℕ) (y : K₀), (PD.φ ^ i) (algebraMap K₀ B y) = algebraMap K₀ B ((PD.σ ^ i) y) := by
    intro i y
    induction i with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih, PD.φ_K₀]
  have hprod : ∀ a : ℕ → B, (∀ i, PD.ι (a i) ∈ PD.Fil 0) → PD.ι (∏ i ∈ Finset.range f, a i) ∈ PD.Fil 0 := by
    intro a ha
    rw [map_prod]
    exact Finset.prod_induction _ (fun y => y ∈ PD.Fil 0)
      (fun y z hy hz => by simpa using PD.Fil_mul 0 0 y z hy hz) PD.one_mem fun i _ => ha i
  have hδ : δ ≠ 0 := by
    rintro rfl
    exact hinj f b hb (by rw [hφ, map_zero, zero_mul])
  set c := ∏ i ∈ Finset.range f, (PD.φ ^ i) b with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hinj i b hb
  have hφc : PD.φ c = algebraMap K₀ B δ * c := by
    apply mul_right_cancel₀ hb
    have h := shift_prod (fun i => (PD.φ ^ i) b) f
    simp only [pow_succ', AlgHom.mul_apply, pow_zero, AlgHom.one_apply] at h
    rw [← map_prod, ← hc, hφ] at h
    rw [h]; ring
  set N := ∏ i ∈ Finset.range f, (PD.σ ^ i) δ with hN
  have hσN : PD.σ N = N := by
    apply mul_right_cancel₀ hδ
    have h := shift_prod (fun i => (PD.σ ^ i) δ) f
    simp only [pow_succ', AlgHom.mul_apply, pow_zero, AlgHom.one_apply] at h
    rw [← map_prod, ← hN, hσ] at h
    exact h
  obtain ⟨x, hx⟩ := PD.fund (algebraMap K₀ B N) (by rw [PD.φ_K₀, hσN]) (by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K₀ K BdR, Algebra.algebraMap_eq_smul_one]
    exact (PD.Fil 0).smul_mem _ PD.one_mem)
  refine ⟨∏ i ∈ Finset.range f, (PD.φ ^ i) c, x, Finset.prod_ne_zero_iff.2 fun i _ => hinj i c hc0, ?_,
    hprod _ fun i => ?_, ?_⟩
  · rw [hx, hN, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← AlgHom.mul_apply, ← pow_succ', pow_succ, AlgHom.mul_apply, hφc, map_mul, hK]
  · rw [hc, map_prod]
    refine hprod _ fun j => ?_
    rw [← AlgHom.mul_apply, ← pow_add]
    exact hF _
  · rw [IsScalarTower.algebraMap_apply Qp K₀ B] at hx
    exact (algebraMap K₀ B).injective hx

private theorem norm_algHom' {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (Om l)}
    (f : ↥K →ₐ[ℚ_[l]] Om l) (x : ↥K) : ‖f x‖ = ‖(x : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]
  have h1 := minpoly.algHom_eq f f.toRingHom.injective x
  have h2 := minpoly.algHom_eq K.val K.val.toRingHom.injective x
  exact congrArg spectralValue (h1.trans h2.symm)

theorem UpperTheory.norm_le_one_of_frobenius_pow_eigenvector_mem_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), 0 < f → (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ (b : Bcr l) (δ : ↥(K0 K)), b ≠ 0 → ((PP l).φB)^[f] b = algebraMap ↥(K0 K) (Bcr l) δ * b → (∀ i : ℕ, (PP l).ιB (((PP l).φB)^[i] b) ∈ ((PP l).PD (botExt l)).Fil 0) → ‖(δ : Om l)‖ ≤ 1 := by
  intro l _ K f hf hσ b δ hb hφ hF
  obtain ⟨T⟩ := tiedP l
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  have e : ((PP l).PD K).φ = (PP l).φB := AlgHom.ext ((PP l).PD_φ K)
  have hFil : ∀ y, y ∈ ((PP l).PD K).Fil 0 ↔ y ∈ ((PP l).PD (botExt l)).Fil 0 := fun y => by
    rw [← SetLike.mem_coe, (PP l).PD_Fil K (botExt l), SetLike.mem_coe]
  obtain ⟨c, x, hc, hφc, hFc, hx⟩ := descend ((PP l).PD K) f (fun y => by rw [AlgHom.coe_pow, hσ]) b δ hb
    (by rw [e, AlgHom.coe_pow, hφ]) (fun i => by rw [e, AlgHom.coe_pow, (PP l).PD_ι, hFil]; exact hF i)
  rw [e] at hφc
  rw [(PP l).PD_ι, hFil] at hFc
  have h1 := UpperTheory.norm_le_one_of_frobenius_eigenvector_mem_fil_zero c x hc hφc hFc
  have h2 := congrArg (fun y : ↥(K0 K) => ‖(K0 K).val y‖) hx
  simp only [map_prod, norm_prod, AlgHom.commutes] at h2
  have h3 : ∀ i : ℕ, ‖(K0 K).val ((((PP l).PD K).σ ^ i) δ)‖ = ‖(δ : Om l)‖ :=
    fun i => norm_algHom' ((K0 K).val.comp (((PP l).PD K).σ ^ i)) δ
  simp only [h3] at h2
  rw [Finset.prod_const, Finset.card_range, norm_algebraMap'] at h2
  rw [h2] at h1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hf.ne').1 h1
