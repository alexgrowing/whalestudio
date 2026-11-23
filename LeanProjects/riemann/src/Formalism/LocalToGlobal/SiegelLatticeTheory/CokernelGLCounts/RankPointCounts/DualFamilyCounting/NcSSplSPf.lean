import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSSplS

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Polynomial
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.NcS.LT

namespace LtSplSPf

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sq_of_cm (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let τ : E →+* ℂ := Classical.arbitrary _
  apply τ.injective
  rw [hτ, hτ, star_star]

theorem exists_moved_of_cm (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ y, σ y ≠ y := by
  obtain ⟨-, hC, -, hτ⟩ := h
  by_contra hno
  push Not at hno
  let τ : E →+* ℂ := Classical.arbitrary _
  have hR : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    exact ((hτ τ x).symm.trans (congrArg τ (hno x)) : _)
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (hC.isComplex (InfinitePlace.mk τ)))
    (InfinitePlace.isReal_mk_iff.2 hR)

end CM

section Quad

variable {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero E]

theorem exists_alpha (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hmov : ∃ y, σ y ≠ y) :
    ∃ α : E, α ≠ 0 ∧ σ α = -α := by
  obtain ⟨y, hy⟩ := hmov
  refine ⟨y - σ y, sub_ne_zero.2 (Ne.symm hy), ?_⟩
  rw [map_sub, hσ]
  ring

theorem rep_of (σ : E →ₐ[F] E) (hfin : Module.finrank F E = 2) {α : E} (hα0 : α ≠ 0)
    (hσα : σ α = -α) : ∀ e : E, ∃ a b : F, e = algebraMap F E a + b • α := by
  have hli : LinearIndependent F ![(1 : E), α] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [← Algebra.algebraMap_eq_smul_one, Algebra.smul_def] at hst
    have h1 := congrArg σ hst
    rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσα, map_zero] at h1
    have h2 : (2 : E) * (algebraMap F E t * α) = 0 := by linear_combination hst - h1
    have ht : algebraMap F E t = 0 :=
      (mul_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left two_ne_zero)).resolve_right hα0
    have ht' : t = 0 := (algebraMap F E).injective (ht.trans (map_zero _).symm)
    subst ht'
    rw [map_zero, zero_mul, add_zero] at hst
    exact ⟨(algebraMap F E).injective (hst.trans (map_zero _).symm), rfl⟩
  intro e
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hfin])
  have hb := B.sum_repr e
  rw [Fin.sum_univ_two] at hb
  simp only [B, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hb
  refine ⟨B.repr e 0, B.repr e 1, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one]
  exact hb.symm

theorem exists_d (σ : E →ₐ[F] E) {α : E} (hrep : ∀ e : E, ∃ a b : F, e = algebraMap F E a + b • α)
    (hσα : σ α = -α) : ∃ d : F, algebraMap F E d = α * α := by
  obtain ⟨a, b, hab⟩ := hrep (α * α)
  rw [Algebra.smul_def] at hab
  have h1 := congrArg σ hab
  rw [map_mul, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσα, neg_mul_neg] at h1
  have h2 : (2 : E) * (algebraMap F E b * α) = 0 := by linear_combination h1 - hab
  have hb : algebraMap F E b * α = 0 := (mul_eq_zero.1 h2).resolve_left two_ne_zero
  exact ⟨a, by rw [hab, hb, add_zero]⟩

end Quad

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] {K : Type} [Field K] [Algebra F K]

def ev (φ : E →ₐ[F] K) : K ⊗[F] E →+* K :=
  (Algebra.TensorProduct.lift (AlgHom.id K K) φ (fun _ _ => Commute.all _ _)).toRingHom

theorem ev_rep (φ : E →ₐ[F] K) (α : E) (a b : K) :
    ev φ (algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) b * ((1 : K) ⊗ₜ[F] α)) =
      a + b * φ α := by
  simp [ev, Algebra.TensorProduct.algebraMap_apply]

theorem ev_alg (φ : E →ₐ[F] K) (c : K) : ev φ (algebraMap K (K ⊗[F] E) c) = c := by
  simp [ev, Algebra.TensorProduct.algebraMap_apply]

theorem tens_rep {α : E} (hrep : ∀ e : E, ∃ a b : F, e = algebraMap F E a + b • α)
    (s : K ⊗[F] E) : ∃ a b : K,
      s = algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) b * ((1 : K) ⊗ₜ[F] α) := by
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul r e =>
    obtain ⟨a, b, rfl⟩ := hrep e
    refine ⟨r * algebraMap F K a, r * algebraMap F K b, ?_⟩
    have key : r ⊗ₜ[F] (algebraMap F E a + b • α) =
        (r * algebraMap F K a) ⊗ₜ[F] (1 : E) + (r * algebraMap F K b) ⊗ₜ[F] α := by
      rw [TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one (A := E) a,
        ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def,
        mul_comm (algebraMap F K a), mul_comm (algebraMap F K b)]
    rw [key]
    simp [Algebra.TensorProduct.algebraMap_apply]
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by simp only [map_add]; ring⟩

theorem sigR_rep (σ : E →ₐ[F] E) {α : E} (hσα : σ α = -α) (a b : K) :
    sigR K σ (algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) b * ((1 : K) ⊗ₜ[F] α)) =
      algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) (-b) * ((1 : K) ⊗ₜ[F] α) := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply, hσα, TensorProduct.tmul_neg, TensorProduct.neg_tmul]

theorem u_mul_u {α : E} {d : F} (hd : algebraMap F E d = α * α) :
    ((1 : K) ⊗ₜ[F] α) * ((1 : K) ⊗ₜ[F] α) = algebraMap K (K ⊗[F] E) (algebraMap F K d) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hd, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_eq_smul_one (A := E) d,
    Algebra.algebraMap_eq_smul_one (A := K) d, ← TensorProduct.smul_tmul]

end Tens

theorem main_gen {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F] [CharZero E]
    (K : Type) [Field K] [Algebra F K] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (hmov : ∃ y, σ y ≠ y) (hfin : Module.finrank F E = 2) (hnf : ¬ IsField (K ⊗[F] E)) :
    ∃ π₁ π₂ : K ⊗[F] E →+* K,
      (∀ s, π₁ (sigR K σ s) = π₂ s) ∧ (∀ s, π₂ (sigR K σ s) = π₁ s) ∧
      (∀ c : K, π₁ (algebraMap K (K ⊗[F] E) c) = c ∧ π₂ (algebraMap K (K ⊗[F] E) c) = c) ∧
      (∀ s t, π₁ s = π₁ t → π₂ s = π₂ t → s = t) ∧ (∀ p q : K, ∃ s, π₁ s = p ∧ π₂ s = q) := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hfin]; norm_num)
  have h2K : (2 : K) ≠ 0 := by
    have := (algebraMap F K).injective.ne (two_ne_zero (α := F))
    rwa [map_ofNat, map_zero] at this
  obtain ⟨α, hα0, hσα⟩ := exists_alpha σ hσ hmov
  have hrep := rep_of σ hfin hα0 hσα
  obtain ⟨d, hd⟩ := exists_d σ hrep hσα
  have huu := u_mul_u (K := K) hd
  have hrepS := tens_rep (K := K) hrep
  by_cases hsq : ∃ c : K, c * c = algebraMap F K d
  swap
  · exfalso
    apply hnf
    push Not at hsq
    have : Nontrivial (K ⊗[F] E) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain F K E
        (algebraMap F K).injective (algebraMap F E).injective
    refine ⟨exists_pair_ne _, mul_comm, ?_⟩
    intro s hs
    obtain ⟨a, b, rfl⟩ := hrepS s
    have hN : a * a - b * b * algebraMap F K d ≠ 0 := by
      intro h0
      by_cases hb : b = 0
      · subst hb
        apply hs
        have ha : a = 0 := by simpa using h0
        simp [ha]
      · apply hsq (a / b)
        rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hb hb)]
        linear_combination h0
    refine ⟨(algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) (-b) * ((1 : K) ⊗ₜ[F] α)) *
      algebraMap K (K ⊗[F] E) (a * a - b * b * algebraMap F K d)⁻¹, ?_⟩
    have hprod : (algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) b * ((1 : K) ⊗ₜ[F] α)) *
        (algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) (-b) * ((1 : K) ⊗ₜ[F] α)) =
        algebraMap K (K ⊗[F] E) (a * a - b * b * algebraMap F K d) := by
      simp only [map_sub, map_mul, map_neg, ← huu]
      ring
    rw [← mul_assoc, hprod, ← map_mul, mul_inv_cancel₀ hN, map_one]
  obtain ⟨c, hc⟩ := hsq
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : algebraMap F K d = 0 := by rw [← hc, mul_zero]
    have hd0 : d = 0 := (algebraMap F K).injective (h0.trans (map_zero _).symm)
    rw [hd0, map_zero] at hd
    exact hα0 (mul_self_eq_zero.1 hd.symm)
  have hα_nr : α ∉ (algebraMap F E).range := by
    intro h
    obtain ⟨f, hf⟩ := RingHom.mem_range.1 h
    have h1 : σ α = α := by rw [← hf, AlgHom.commutes]
    rw [hσα] at h1
    have h2 : (2 : E) * α = 0 := by linear_combination -h1
    exact hα0 ((mul_eq_zero.1 h2).resolve_left two_ne_zero)
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hmin : minpoly F α = X ^ 2 - C d := by
    refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (monic_X_pow_sub_C d two_ne_zero) (minpoly.dvd F α ?_) ?_).symm
    · simp [hd, sq]
    · rw [natDegree_X_pow_sub_C]
      have h0 := minpoly.natDegree_pos hint
      have h1 : (minpoly F α).natDegree ≠ 1 := fun h => hα_nr (minpoly.natDegree_eq_one_iff.1 h)
      omega
  have hadj : Algebra.adjoin F {α} = ⊤ := by
    refine eq_top_iff.2 fun e _ => ?_
    obtain ⟨a, b, rfl⟩ := hrep e
    exact add_mem (Subalgebra.algebraMap_mem _ a)
      (Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_singleton α)) b)
  let pb := PowerBasis.ofAdjoinEqTop hint hadj
  have hgen : pb.gen = α := PowerBasis.ofAdjoinEqTop_gen hint hadj
  have hroot : ∀ y : K, y * y = algebraMap F K d → aeval y (minpoly F pb.gen) = 0 := by
    intro y hy
    rw [hgen, hmin]
    simp [sq, hy]
  let φ₁ : E →ₐ[F] K := pb.lift c (hroot c hc)
  let φ₂ : E →ₐ[F] K := pb.lift (-c) (hroot (-c) (by rw [neg_mul_neg]; exact hc))
  have hφ₁ : φ₁ α = c := by rw [← hgen]; exact pb.lift_gen _ _
  have hφ₂ : φ₂ α = -c := by rw [← hgen]; exact pb.lift_gen _ _
  refine ⟨ev φ₁, ev φ₂, ?_, ?_, fun c' => ⟨ev_alg φ₁ c', ev_alg φ₂ c'⟩, ?_, ?_⟩
  · intro s
    obtain ⟨a, b, rfl⟩ := hrepS s
    rw [sigR_rep σ hσα, ev_rep, ev_rep, hφ₁, hφ₂]
    ring
  · intro s
    obtain ⟨a, b, rfl⟩ := hrepS s
    rw [sigR_rep σ hσα, ev_rep, ev_rep, hφ₁, hφ₂]
    ring
  · intro s t h1 h2
    obtain ⟨a, b, rfl⟩ := hrepS s
    obtain ⟨a', b', rfl⟩ := hrepS t
    rw [ev_rep, ev_rep, hφ₁] at h1
    rw [ev_rep, ev_rep, hφ₂] at h2
    have ha : a = a' := by
      have h3 : (2 : K) * (a - a') = 0 := by linear_combination h1 + h2
      have h4 := (mul_eq_zero.1 h3).resolve_left h2K
      linear_combination h4
    have hb : b = b' := by
      have h3 : ((2 : K) * c) * (b - b') = 0 := by linear_combination h1 - h2
      have h4 := (mul_eq_zero.1 h3).resolve_left (mul_ne_zero h2K hc0)
      linear_combination h4
    rw [ha, hb]
  · intro p q
    refine ⟨algebraMap K (K ⊗[F] E) ((p + q) / 2) +
      algebraMap K (K ⊗[F] E) ((p - q) / (2 * c)) * ((1 : K) ⊗ₜ[F] α), ?_, ?_⟩
    · rw [ev_rep, hφ₁]
      field_simp
      ring
    · rw [ev_rep, hφ₂]
      field_simp
      ring

end LtSplSPf

theorem splitStr : SplitStr := by
  intro F E _ _ _ _ _ σ v hCM hnf
  exact LtSplSPf.main_gen (Fv F v) σ (LtSplSPf.sigma_sq_of_cm σ hCM)
    (LtSplSPf.exists_moved_of_cm σ hCM) hCM.2.2.1 hnf

end Formalism.L2.SG.Pf.NcS.LT
