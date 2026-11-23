import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSFockColumnSubstitutionUnitaryStatement
open Classical MeasureTheory

noncomputable section

namespace GlobalTheory.UnitaryAvg

open MvPolynomial GlobalTheory.MinorFrame
open scoped Pointwise

variable {ι : Type} [Fintype ι]

theorem colSub_comp {d a : ℕ} (u v : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    colSub u (colSub v P) = colSub (fun τ => u τ * v τ) P := by
  have h : (colSub (d := d) u).comp (colSub v) = colSub (fun τ => u τ * v τ) := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [AlgHom.comp_apply, colSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mul_apply,
      Finset.sum_mul, Finset.mul_sum, C_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) h

theorem colSub_one {d a : ℕ} (P : Pol ι d a) :
    colSub (fun _ : ι => (1 : Matrix (Fin a) (Fin a) ℂ)) P = P := by
  have h : (colSub (d := d) (fun _ : ι => (1 : Matrix (Fin a) (Fin a) ℂ))) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro y
    simp [colSub, Matrix.one_apply]
  rw [h]; rfl

theorem support_colSub_bdd {d a : ℕ} (P : Pol ι d a) :
    ∃ S : Finset (Var ι d a →₀ ℕ), ∀ u : ι → Matrix (Fin a) (Fin a) ℂ, (colSub u P).support ⊆ S := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨(C c : Pol ι d a).support, fun u => by rw [algHom_C]; rfl⟩
  | add p q hp hq =>
    obtain ⟨S, hS⟩ := hp
    obtain ⟨T, hT⟩ := hq
    exact ⟨S ∪ T, fun u => by rw [map_add]; exact support_add.trans (Finset.union_subset_union (hS u) (hT u))⟩
  | mul_X p y hp =>
    obtain ⟨S, hS⟩ := hp
    refine ⟨S + Finset.univ.image (fun j : Fin a => Finsupp.single (y.1, y.2.1, j) 1), fun u => ?_⟩
    rw [map_mul]
    refine (support_mul _ _).trans (Finset.add_subset_add (hS u) ?_)
    simp only [colSub, aeval_X]
    refine support_sum.trans ?_
    intro m hm
    simp only [Finset.mem_biUnion] at hm
    obtain ⟨j, _, hj⟩ := hm
    rw [C_mul_X_eq_monomial] at hj
    have := support_monomial_subset hj
    rw [Finset.mem_singleton] at this
    exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, this.symm⟩

section Meas

variable {K : Type} [Group K] [MeasurableSpace K] {a d : ℕ}

theorem coeff_colSub_good (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ))
    (hρ : ∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) (P : Pol ι d a) :
    ∀ m, Measurable (fun g => coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P)) ∧
      ∃ C : ℝ, ∀ g, ‖coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P)‖ ≤ C := by
  have hmul : ∀ p q : Pol ι d a,
      (∀ m, Measurable (fun g => coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) p)) ∧
        ∃ C : ℝ, ∀ g, ‖coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) p)‖ ≤ C) →
      (∀ m, Measurable (fun g => coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) q)) ∧
        ∃ C : ℝ, ∀ g, ‖coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) q)‖ ≤ C) →
      (∀ m, Measurable (fun g => coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (p * q))) ∧
        ∃ C : ℝ, ∀ g, ‖coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (p * q))‖ ≤ C) := by
    intro p q hp hq m
    have hpb : ∀ m, ∃ C : ℝ, ∀ g, ‖coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) p)‖ ≤ C :=
      fun m => (hp m).2
    have hqb : ∀ m, ∃ C : ℝ, ∀ g, ‖coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) q)‖ ≤ C :=
      fun m => (hq m).2
    choose Cp hCp using hpb
    choose Cq hCq using hqb
    simp only [map_mul, coeff_mul]
    refine ⟨Finset.measurable_sum _ fun x _ => (hp x.1).1.mul (hq x.2).1, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, Cp x.1 * Cq x.2,
      fun g => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    refine (norm_mul_le _ _).trans ?_
    exact mul_le_mul (hCp _ g) (hCq _ g) (norm_nonneg _) ((norm_nonneg _).trans (hCp _ g))
  intro m
  induction P using MvPolynomial.induction_on generalizing m with
  | C c =>
    simp only [algHom_C, algebraMap_eq]
    exact ⟨measurable_const, _, fun _ => le_rfl⟩
  | add p q hp hq =>
    simp only [map_add, coeff_add]
    obtain ⟨hpm, Cp, hCp⟩ := hp m
    obtain ⟨hqm, Cq, hCq⟩ := hq m
    exact ⟨hpm.add hqm, Cp + Cq, fun g => (norm_add_le _ _).trans (add_le_add (hCp g) (hCq g))⟩
  | mul_X p y hp =>
    refine hmul p (X y) hp (fun m' => ?_) m
    simp only [colSub, aeval_X, coeff_sum, coeff_C_mul]
    refine ⟨Finset.measurable_sum _ fun j _ => (hρ _ _ _).mul measurable_const,
      ∑ j : Fin a, ‖coeff m' (X (y.1, y.2.1, j) : Pol ι d a)‖, fun g => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (entry_norm_bound_of_unitary (ρ g y.1).2 _ _)

end Meas

end GlobalTheory.UnitaryAvg

namespace GlobalTheory.UnitaryAvg

open MvPolynomial GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι] {K : Type} [Group K] [MeasurableSpace K] {a d : ℕ}

def Mg (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)) (g : K) : ι → Matrix (Fin a) (Fin a) ℂ :=
  fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)

def cc (n : ι → ℕ) (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)) (g : K) : ℂ :=
  ∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(n τ : ℤ))

theorem det_unitary_norm (U : Matrix.unitaryGroup (Fin a) ℂ) : ‖(U : Matrix (Fin a) (Fin a) ℂ).det‖ = 1 :=
  CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary U.2)

theorem det_unitary_ne_zero (U : Matrix.unitaryGroup (Fin a) ℂ) : (U : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 := by
  intro h
  have := det_unitary_norm U
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem norm_cc (n : ι → ℕ) (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)) (g : K) : ‖cc n ρ g‖ = 1 := by
  rw [cc, norm_prod]
  exact Finset.prod_eq_one fun τ _ => by rw [norm_zpow, det_unitary_norm, one_zpow]

theorem Mg_mul (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)) (g0 g : K) :
    Mg ρ (g0 * g) = fun τ => Mg ρ g0 τ * Mg ρ g τ := by
  funext τ
  simp only [Mg, map_mul]
  rfl

theorem cc_mul (n : ι → ℕ) (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)) (g0 g : K) :
    cc n ρ g = detChar n (Mg ρ g0) * cc n ρ (g0 * g) := by
  have h := Mg_mul ρ g0 g
  simp only [cc, detChar]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hτ : (ρ (g0 * g) τ : Matrix (Fin a) (Fin a) ℂ) = Mg ρ g0 τ * Mg ρ g τ := congrFun h τ
  have h0 : (Mg ρ g0 τ).det ≠ 0 := det_unitary_ne_zero _
  rw [hτ, Matrix.det_mul, mul_zpow, ← mul_assoc, zpow_neg ((Mg ρ g0 τ).det), zpow_natCast,
    mul_inv_cancel₀ (pow_ne_zero _ h0), one_mul]
  rfl

theorem measurable_det (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ))
    (hρ : ∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) (τ : ι) :
    Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det := by
  simp only [Matrix.det_apply']
  exact Finset.measurable_sum _ fun σ _ => measurable_const.mul (Finset.measurable_prod _ fun i _ => hρ _ _ _)

theorem measurable_cc (n : ι → ℕ) (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ))
    (hρ : ∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) : Measurable (cc n ρ) := by
  unfold cc
  refine Finset.measurable_prod _ fun τ _ => ?_
  simp only [zpow_neg, zpow_natCast]
  exact ((measurable_det ρ hρ τ).pow_const _).inv

theorem integrable_term (ν : Measure K) [IsProbabilityMeasure ν] (n : ι → ℕ)
    (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ))
    (hρ : ∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) (P : Pol ι d a) (m : Var ι d a →₀ ℕ) :
    Integrable (fun g => cc n ρ g * coeff m (colSub (Mg ρ g) P)) ν := by
  obtain ⟨hm, C, hC⟩ := coeff_colSub_good ρ hρ P m
  refine Integrable.of_bound ((measurable_cc n ρ hρ).mul hm).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun g => ?_)
  rw [norm_mul, norm_cc, one_mul]
  exact hC g

theorem integral_eq_lin (ν : Measure K) [IsProbabilityMeasure ν] (n : ι → ℕ)
    (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ))
    (hρ : ∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) (P : Pol ι d a)
    (S : Finset (Var ι d a →₀ ℕ)) (hS : ∀ u, (colSub u P).support ⊆ S) (ℓ : Pol ι d a →ₗ[ℂ] ℂ) :
    ∫ g, cc n ρ g * ℓ (colSub (Mg ρ g) P) ∂ν =
      ℓ (∑ m ∈ S, monomial m (∫ g, cc n ρ g * coeff m (colSub (Mg ρ g) P) ∂ν)) := by
  have hmono : ∀ (m : Var ι d a →₀ ℕ) (c : ℂ), ℓ (monomial m c) = c * ℓ (monomial m 1) := by
    intro m c
    have : (monomial m c : Pol ι d a) = c • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul]
  have hexp : ∀ Q : Pol ι d a, Q.support ⊆ S → ℓ Q = ∑ m ∈ S, coeff m Q * ℓ (monomial m 1) := by
    intro Q hQ
    conv_lhs => rw [Q.as_sum]
    rw [Finset.sum_subset hQ (fun m _ hm => by rw [notMem_support_iff.1 hm, monomial_zero]), map_sum]
    exact Finset.sum_congr rfl fun m _ => hmono m _
  have hL : ∀ g, cc n ρ g * ℓ (colSub (Mg ρ g) P) =
      ∑ m ∈ S, (cc n ρ g * coeff m (colSub (Mg ρ g) P)) * ℓ (monomial m 1) := by
    intro g
    rw [hexp _ (hS _), Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hL),
    integral_finset_sum _ (fun m _ => (integrable_term ν n ρ hρ P m).mul_const _), map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_mul_const]
  exact (hmono m _).symm

theorem integral_mul_left_inv (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] (F : K → ℂ)
    (hF : Measurable F) (g0 : K) : ∫ g, F (g0 * g) ∂ν = ∫ g, F g ∂ν := by
  have hmap : ν.map (g0 * ·) = ν := map_mul_left_eq_self ν g0
  have hae : AEMeasurable (g0 * ·) ν := by
    by_contra h
    have h0 := Measure.map_of_not_aemeasurable h
    rw [hmap] at h0
    exact IsProbabilityMeasure.ne_zero ν h0
  have := integral_map hae hF.aestronglyMeasurable (μ := ν)
  rw [hmap] at this
  exact this.symm

theorem avg_perp : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) →
    Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
    (∀ I ∈ GlobalTheory.MinorFrame.inv a d n, Formalism.L2.DIV.fockS I P = 0) →
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(n τ : ℤ))) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) ∂ν = 0 := by
  intro ι _ a d n K _ _ ν hν hinv ρ hρ hsurj Λ P hP
  obtain ⟨S, hS⟩ := support_colSub_bdd P
  set Q : Pol ι d a := ∑ m ∈ S, monomial m (∫ g, cc n ρ g * coeff m (colSub (Mg ρ g) P) ∂ν) with hQdef
  have hav : ∀ ℓ : Pol ι d a →ₗ[ℂ] ℂ, ∫ g, cc n ρ g * ℓ (colSub (Mg ρ g) P) ∂ν = ℓ Q :=
    fun ℓ => integral_eq_lin ν n ρ hρ P S hS ℓ
  have hcoef : ∀ m, coeff m Q = ∫ g, cc n ρ g * coeff m (colSub (Mg ρ g) P) ∂ν :=
    fun m => (hav (lcoeff ℂ m)).symm
  have hQinv : Q ∈ inv a d n := by
    intro u
    obtain ⟨g0, rfl⟩ := hsurj u
    change colSub (Mg ρ g0) Q = detChar n (Mg ρ g0) • Q
    ext m
    rw [coeff_smul, smul_eq_mul]
    have h1 := hav ((lcoeff ℂ m).comp (colSub (Mg ρ g0)).toLinearMap)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, lcoeff_apply] at h1
    rw [← h1, hcoef m]
    have hF : Measurable fun g => cc n ρ g * coeff m (colSub (Mg ρ g) P) :=
      (measurable_cc n ρ hρ).mul (coeff_colSub_good ρ hρ P m).1
    rw [← integral_mul_left_inv ν _ hF g0, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only
    rw [colSub_comp, ← Mg_mul, cc_mul n ρ g0 g]
    ring
  have horth : ∀ I ∈ inv a d n, Formalism.L2.DIV.fockS I Q = 0 := by
    intro I hI
    have key : ∀ g, Formalism.L2.DIV.fockS I (colSub (Mg ρ g) P) = 0 := by
      intro g
      have hIu : colSub (fun τ => ((ρ g)⁻¹ τ : Matrix (Fin a) (Fin a) ℂ)) I =
          detChar n (fun τ => ((ρ g)⁻¹ τ : Matrix (Fin a) (Fin a) ℂ)) • I := hI (ρ g)⁻¹
      have hI' : colSub (Mg ρ g) (colSub (fun τ => ((ρ g)⁻¹ τ : Matrix (Fin a) (Fin a) ℂ)) I) = I := by
        rw [colSub_comp]
        have h1 : (fun τ => Mg ρ g τ * ((ρ g)⁻¹ τ : Matrix (Fin a) (Fin a) ℂ)) = fun _ => (1 : Matrix (Fin a) (Fin a) ℂ) := by
          funext τ
          simp [Mg]
        rw [h1, colSub_one]
      rw [← hI', show Mg ρ g = fun τ => ((ρ g τ : Matrix.unitaryGroup (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) from rfl, GlobalTheory.T.fockS_fockColumnSubstitution_unitary, hIu, ← Formalism.L2.DIV.fockL_apply, LinearMap.map_smulₛₗ₂,
        Formalism.L2.DIV.fockL_apply, hP I hI, smul_zero]
    rw [← Formalism.L2.DIV.fockL_apply, ← hav]
    simp only [Formalism.L2.DIV.fockL_apply, key, mul_zero, integral_zero]
  have hQ0 : Q = 0 := by
    by_contra hne
    have := fockS_self_re_pos hne
    rw [horth Q hQinv, Complex.zero_re] at this
    exact lt_irrefl _ this
  change ∫ g, cc n ρ g * Λ (colSub (Mg ρ g) P) ∂ν = 0
  rw [hav Λ, hQ0, map_zero]

end GlobalTheory.UnitaryAvg
