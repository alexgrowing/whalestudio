import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFockFormPureTensorProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraTypeDualWeylModuleFockNormStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjCoefficientsWeylModuleRowActNormFockStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvariantPosDefFormEqSmulInnerOfIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DelSqIrreducibleUnitaryStatement

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

noncomputable section

namespace GlobalTheory.WeylConjType

open MvPolynomial

theorem jm_allPos (k : ℕ) : Formalism.REAL.Jm (allPos k) = 1 := by
  simp [Formalism.REAL.Jm, allPos]

theorem mem_UJset_of_unitary {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ unitaryGroup (Fin k) ℂ) :
    g ∈ UJset (allPos k) := by
  show Formalism.REAL.inUJ (allPos k) g
  unfold Formalism.REAL.inUJ
  rw [jm_allPos, Matrix.mul_one]
  have h := mem_unitaryGroup_iff'.mp hg
  rwa [Matrix.star_eq_conjTranspose] at h

theorem transpose_mem_unitary {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ unitaryGroup (Fin k) ℂ) :
    gᵀ ∈ unitaryGroup (Fin k) ℂ := by
  rw [mem_unitaryGroup_iff]
  have h := mem_unitaryGroup_iff'.mp hg
  have h2 : (star g * g)ᵀ = 1 := by rw [h, Matrix.transpose_one]
  rw [Matrix.transpose_mul] at h2
  convert h2 using 2
  ext i j
  simp [Matrix.star_apply]

theorem star_det_of_unitary {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ unitaryGroup (Fin k) ℂ) :
    star g.det = g.det⁻¹ ∧ g.det ≠ 0 := by
  have h := mem_unitaryGroup_iff'.mp hg
  have h1 : star g.det * g.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, ← Matrix.star_eq_conjTranspose, h, Matrix.det_one]
  have h0 : g.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  exact ⟨eq_inv_of_mul_eq_one_left h1, h0⟩

def glOf {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) (hg : g ∈ unitaryGroup (Fin k) ℂ) : GL (Fin k) ℂ :=
  ⟨g, star g, mem_unitaryGroup_iff.mp hg, mem_unitaryGroup_iff'.mp hg⟩

theorem detPow_glOf {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) (hg : g ∈ unitaryGroup (Fin k) ℂ) (s : ℤ) :
    detPow ℂ k (glOf g hg) s = g.det ^ s := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

def conjL (σ : Type) : MvPolynomial σ ℂ →ₗ⋆[ℂ] MvPolynomial σ ℂ where
  toFun p := MvPolynomial.map (starRingEnd ℂ) p
  map_add' p q := map_add _ p q
  map_smul' c p := by
    simp only [RingHom.id_apply, smul_eq_C_mul, map_mul, map_C]

theorem conjL_conjL {σ : Type} (p : MvPolynomial σ ℂ) : conjL σ (conjL σ p) = p := by
  show MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map (starRingEnd ℂ) p) = p
  rw [MvPolynomial.map_map]
  have h : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun z => by simp
  rw [h, MvPolynomial.map_id]

private theorem extremal_ne_zero' {k : ℕ} (lam : DomWeight k) : extremal ℂ k lam ≠ 0 := by
  intro h
  apply GlobalTheory.FockTen.fockF_extremal_ne lam
  rw [h]
  simp [Formalism.REAL.fockF]

theorem fockF_ext_real {k : ℕ} (lam : DomWeight k) :
    star (Formalism.REAL.fockF (extremal ℂ k lam) (extremal ℂ k lam)) = Formalism.REAL.fockF (extremal ℂ k lam) (extremal ℂ k lam) ∧
    0 < (Formalism.REAL.fockF (extremal ℂ k lam) (extremal ℂ k lam)).re :=
  ⟨(Formalism.GradedWeylDivisibility.fockHerm _ _ _).symm, (Formalism.GradedWeylDivisibility.fockPos _ _ (extremal_ne_zero' lam)).1⟩

private theorem fockF_eq_sum_coeff_mul_star {σ : Type} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ i ∈ m.support, (m i).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  apply Finset.sum_subset hS
  intro m _ hm
  simp only [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

private theorem fockF_add_left' {σ : Type} (f f' g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f + f') g = Formalism.REAL.fockF f g + Formalism.REAL.fockF f' g := by
  classical
  rw [fockF_eq_sum_coeff_mul_star (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    fockF_eq_sum_coeff_mul_star f g (f.support ∪ f'.support) (fun x hx => Finset.mem_union_left _ hx),
    fockF_eq_sum_coeff_mul_star f' g (f.support ∪ f'.support) (fun x hx => Finset.mem_union_right _ hx),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

private theorem fockF_smul_left_eq_mul {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (c • f) g = c * Formalism.REAL.fockF f g := by
  classical
  rw [fockF_eq_sum_coeff_mul_star (c • f) g f.support MvPolynomial.support_smul,
    fockF_eq_sum_coeff_mul_star f g f.support (subset_refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

private theorem fockF_add_right' {σ : Type} (f g g' : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f (g + g') = Formalism.REAL.fockF f g + Formalism.REAL.fockF f g' := by
  unfold Formalism.REAL.fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]
  ring

private theorem fockF_smul_right' {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f (c • g) = star c * Formalism.REAL.fockF f g := by
  unfold Formalism.REAL.fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

private theorem rowAct_rowAct' {r n : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ)
    (q : MvPolynomial (Fin r × Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ A (Formalism.GradedWeylDivisibility.rowAct ℂ B q) = Formalism.GradedWeylDivisibility.rowAct ℂ (B * A) q := by
  have h : (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) A).comp (Formalism.GradedWeylDivisibility.rowAct ℂ B) =
      Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (B * A) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  exact congrArg (fun φ => φ q) h

private theorem rowAct_one_flag_measures {r n : ℕ} (q : MvPolynomial (Fin r × Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin r) (Fin r) ℂ) q = q := by
  have h : Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (1 : Matrix (Fin r) (Fin r) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply]
  rw [h]
  rfl

theorem normFock_unitary {k : ℕ} (lam : DomWeight k) {g : Matrix (Fin k) (Fin k) ℂ}
    (hg : g ∈ unitaryGroup (Fin k) ℂ) (s : ℤ) (p q : MvPolynomial (Fin k × Fin k) ℂ) :
    normFock lam ((g.det ^ s) • Formalism.GradedWeylDivisibility.rowAct ℂ gᵀ p) ((g.det ^ s) • Formalism.GradedWeylDivisibility.rowAct ℂ gᵀ q) =
      normFock lam p q := by
  unfold normFock
  congr 1
  have hT := mem_unitaryGroup_iff.mp (transpose_mem_unitary hg)
  rw [Matrix.star_eq_conjTranspose] at hT
  obtain ⟨hs, h0⟩ := star_det_of_unitary hg
  rw [fockF_smul_left_eq_mul, fockF_smul_right', Formalism.GradedWeylDivisibility.fockRowAdj k k gᵀ p, rowAct_rowAct', hT,
    rowAct_one_flag_measures]
  have h1 : g.det ^ s * star (g.det ^ s) = 1 := by
    rw [star_zpow₀, hs, _root_.inv_zpow', ← zpow_add₀ h0, add_neg_cancel, zpow_zero]
  rw [← mul_assoc, h1, one_mul]

private theorem normFock_add_left' {k : ℕ} (lam : DomWeight k) (f f' g : MvPolynomial (Fin k × Fin k) ℂ) :
    normFock lam (f + f') g = normFock lam f g + normFock lam f' g := by
  unfold normFock
  rw [fockF_add_left', add_div]

private theorem normFock_smul_left' {k : ℕ} (lam : DomWeight k) (c : ℂ) (f g : MvPolynomial (Fin k × Fin k) ℂ) :
    normFock lam (c • f) g = c * normFock lam f g := by
  unfold normFock
  rw [fockF_smul_left_eq_mul, mul_div_assoc]

private theorem normFock_add_right {k : ℕ} (lam : DomWeight k) (f g g' : MvPolynomial (Fin k × Fin k) ℂ) :
    normFock lam f (g + g') = normFock lam f g + normFock lam f g' := by
  unfold normFock
  rw [fockF_add_right', add_div]

private theorem normFock_smul_right {k : ℕ} (lam : DomWeight k) (c : ℂ) (f g : MvPolynomial (Fin k × Fin k) ℂ) :
    normFock lam f (c • g) = star c * normFock lam f g := by
  unfold normFock
  rw [fockF_smul_right', mul_div_assoc]

private theorem map_starRingEnd_smul {σ : Type} (c : ℂ) (p : MvPolynomial σ ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (c • p) = starRingEnd ℂ c • MvPolynomial.map (starRingEnd ℂ) p := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

end GlobalTheory.WeylConjType

namespace GlobalTheory.WeylConjType

theorem exists_conj_weyl : ∀ (k n : ℕ) (h : k = n) (lam : DomWeight n) (u : Fin k → ℝ), (∀ i : Fin k, u i = (lam.w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)), IsHCTypeU k u π → ∃ j : W →ₗ⋆[ℂ] MvPolynomial (Fin n × Fin n) ℂ, (∀ ξ, j ξ ∈ delSq ℂ n lam) ∧ (∀ p ∈ delSq ℂ n lam, ∃ ξ, j ξ = p) ∧ (∀ ξ η, normFock lam (j η) (j ξ) = ⟪η, ξ⟫_ℂ) ∧ ∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ ξ, j (π (g.submatrix (Fin.cast h) (Fin.cast h)) ξ) = (g.det ^ (-lam.detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ gᴴ (j ξ) := by
  intro k n h lam u hu W _ _ π hπ
  subst h
  have hsub : ∀ g : Matrix (Fin k) (Fin k) ℂ, g.submatrix (Fin.cast rfl) (Fin.cast rfl) = g := by
    intro g
    ext i j
    simp
  simp only [hsub]
  have hufun : u = fun i => (lam.w i : ℝ) + ((rhoVec k i : ℚ) : ℝ) := by
    funext i
    rw [hu i]
    simp
  obtain ⟨hnt, hfd, hrep, hK⟩ := hπ
  obtain ⟨H, iN, iI, π0, e, hπ0, he_inj, he_mem, he_eq⟩ := GlobalTheory.T.exists_harishChandraType_dualWeylModuleFockNorm k lam
  have hπ0' : IsHCTypeU k u π0 := by
    rw [hufun]
    exact hπ0
  have hπ' : IsHCTypeU k u π := ⟨hnt, hfd, hrep, hK⟩
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_intertwiner_of_same_harishChandraParam_unitary k u W H π π0 hπ' hπ0'
  obtain ⟨hfin, hdn, hstab, hirr⟩ := GlobalTheory.T.delSq_unitary_stable_and_irreducible k lam
  obtain ⟨hcmem, hcrow, hcnf⟩ := GlobalTheory.T.conj_coefficients_weylModule_rowAct_normFock k lam

  obtain ⟨j0, hj0⟩ : ∃ j0 : W →ₗ[ℂ] MvPolynomial (Fin k × Fin k) ℂ, ∀ ξ, j0 ξ = e (A ξ) :=
    ⟨e.comp A.toLinearMap, fun _ => rfl⟩
  have hj0_eq : ∀ g ∈ unitaryGroup (Fin k) ℂ, ∀ ξ,
      j0 (π g ξ) = (g.det ^ lam.detShift) • Formalism.GradedWeylDivisibility.rowAct ℂ gᵀ (j0 ξ) := by
    intro g hg ξ
    rw [hj0, hj0, hA g hg, show π0 g = π0 ((glOf g hg : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ) from rfl,
      he_eq (glOf g hg) hg]
    unfold sqAct
    rw [detPow_glOf]
    rfl
  have hj0_mem : ∀ ξ, j0 ξ ∈ delSq ℂ k lam := by
    intro ξ
    rw [hj0, hdn]
    exact he_mem _
  have hj0_inj : Function.Injective j0 := by
    intro x y hxy
    rw [hj0, hj0] at hxy
    exact A.injective (he_inj hxy)

  have hrange : LinearMap.range e = delSq ℂ k lam := by
    have hle : LinearMap.range e ≤ delSq ℂ k lam := by
      rintro p ⟨x, rfl⟩
      rw [hdn]
      exact he_mem x
    have hst : ∀ g ∈ unitaryGroup (Fin k) ℂ, ∀ p ∈ LinearMap.range e,
        Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ LinearMap.range e := by
      rintro g hg p ⟨x, rfl⟩
      have hgT := transpose_mem_unitary hg
      have h1 := he_eq (glOf gᵀ hgT) hgT x
      unfold sqAct at h1
      rw [detPow_glOf] at h1
      have h2 : ((glOf gᵀ hgT : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ)ᵀ = g := by
        show gᵀᵀ = g
        exact Matrix.transpose_transpose g
      rw [h2] at h1
      have hd : (gᵀ.det ^ lam.detShift) ≠ 0 := zpow_ne_zero _ (star_det_of_unitary hgT).2
      refine ⟨(gᵀ.det ^ lam.detShift)⁻¹ • π0 ((glOf gᵀ hgT : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ) x, ?_⟩
      rw [map_smul e, h1, inv_smul_smul₀ hd]
    rcases hirr _ hle hst with h0 | h0
    · exfalso
      haveI : Nontrivial H := hπ0.1
      obtain ⟨x, hx⟩ := exists_ne (0 : H)
      have hex : e x ∈ LinearMap.range e := ⟨x, rfl⟩
      rw [h0, Submodule.mem_bot] at hex
      exact hx (he_inj (by rw [hex, map_zero]))
    · exact h0

  obtain ⟨B, hB⟩ : ∃ B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ, ∀ x y, B x y = normFock lam (j0 y) (j0 x) :=
    ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => normFock lam (j0 y) (j0 x))
      (fun x x' y => by simp only [map_add, normFock_add_right])
      (fun c x y => by simp only [map_smul, normFock_smul_right, starRingEnd_apply, smul_eq_mul])
      (fun x y y' => by simp only [map_add, normFock_add_left'])
      (fun c x y => by simp only [map_smul, normFock_smul_left', RingHom.id_apply, smul_eq_mul]),
      fun _ _ => rfl⟩
  haveI : FiniteDimensional ℂ W := hfd
  have hE := fockF_ext_real lam
  have hEim : (Formalism.REAL.fockF (extremal ℂ k lam) (extremal ℂ k lam)).im = 0 :=
    (Formalism.GradedWeylDivisibility.fockPos _ _ (extremal_ne_zero' lam)).2
  obtain ⟨c, hc, hcB⟩ := GlobalTheory.T.invariant_posDef_form_eq_smul_inner_of_irreducible' W (unitaryGroup (Fin k) ℂ) (fun i => π i.1) B
    (fun i v => hrep.2.1 i.1 (mem_UJset_of_unitary i.2) v)
    (fun S hS => hK.2.2.1 S le_top (fun g hg v hv => hS ⟨g, hg.1⟩ v hv))
    (fun i x y => by
      rw [hB, hB, hj0_eq i.1 i.2, hj0_eq i.1 i.2]
      exact normFock_unitary lam i.2 _ _ _)
    (fun x y => by
      rw [hB, hB]
      unfold normFock
      rw [star_div₀, ← Formalism.GradedWeylDivisibility.fockHerm _ (j0 y) (j0 x), hE.1])
    (fun x hx => by
      rw [hB]
      unfold normFock
      have hx0 : j0 x ≠ 0 := fun h0 => hx (hj0_inj (by rw [h0, map_zero]))
      obtain ⟨hp, hpim⟩ := Formalism.GradedWeylDivisibility.fockPos _ _ hx0
      rw [Complex.div_re, hpim, hEim, zero_mul, zero_div, add_zero]
      apply div_pos (mul_pos hp hE.2)
      exact Complex.normSq_pos.mpr (fun h0 => by rw [h0] at hE; simp at hE))
  have hcB' := hcB hnt

  have hsq : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  set r : ℂ := (((Real.sqrt c)⁻¹ : ℝ) : ℂ) with hr
  have hrs : starRingEnd ℂ r = r := Complex.conj_ofReal _
  have hrr0 : (Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ * c = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  have hrR0 : (Real.sqrt c)⁻¹ * Real.sqrt c = 1 := inv_mul_cancel₀ hsq
  have hrr : r * star r * c = 1 := by
    rw [← starRingEnd_apply, hrs, hr]
    exact_mod_cast hrr0
  have hrR : r * (Real.sqrt c : ℂ) = 1 := by
    rw [hr]
    exact_mod_cast hrR0
  let j1 : W →ₗ[ℂ] MvPolynomial (Fin k × Fin k) ℂ := r • j0
  have hj1 : ∀ ξ, j1 ξ = r • j0 ξ := fun _ => rfl
  have hjapp : ∀ ξ, ((conjL (Fin k × Fin k)).comp j1 : W →ₗ⋆[ℂ] MvPolynomial (Fin k × Fin k) ℂ) ξ =
      MvPolynomial.map (starRingEnd ℂ) (r • j0 ξ) := fun _ => rfl
  refine ⟨(conjL (Fin k × Fin k)).comp j1, ?_, ?_, ?_, ?_⟩
  · intro ξ
    rw [hjapp]
    exact hcmem _ (Submodule.smul_mem _ _ (hj0_mem ξ))
  · intro p hp
    have hp' := hcmem p hp
    rw [← hrange] at hp'
    obtain ⟨y, hy⟩ := hp'
    refine ⟨(Real.sqrt c : ℂ) • A.symm y, ?_⟩
    rw [hjapp, map_smul j0, hj0, LinearEquiv.apply_symm_apply, smul_smul, hrR, one_smul, hy]
    exact conjL_conjL p
  · intro η ξ
    rw [hjapp, hjapp, hcnf, normFock_smul_left', normFock_smul_right, ← hB, hcB']
    rw [← mul_assoc, ← mul_assoc, hrr, one_mul]
  · intro g hg ξ
    rw [hjapp, hjapp, hj0_eq g hg]
    simp only [map_starRingEnd_smul, hcrow]
    rw [hrs, map_smul (Formalism.GradedWeylDivisibility.rowAct ℂ gᴴ)]
    obtain ⟨hs, h0⟩ := star_det_of_unitary hg
    have hgm : gᵀ.map (starRingEnd ℂ) = gᴴ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    have hdet : starRingEnd ℂ (g.det ^ lam.detShift) = g.det ^ (-lam.detShift) := by
      rw [map_zpow₀, starRingEnd_apply, hs, _root_.inv_zpow']
    rw [hgm, hdet, smul_comm]

end GlobalTheory.WeylConjType
