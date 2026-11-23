import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL4.PColStd
import Formalism.LocalToGlobal.GlobalTheory.GL4.KronDetScalar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.Inhabit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.GramMatrixDuality
import Formalism.LocalToGlobal.Columns.CoefficientsModP

open Module MvPolynomial
open scoped Matrix TensorProduct

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions.flipTwoThree Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)

section LI

theorem li_semilin_gen {K F V M ι κ : Type} [Field K] [Field F] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module F M]
    (σ : K →+* F) (e : V →ₛₗ[σ] M) (b : Basis ι K V) (hb : LinearIndependent F fun i => e (b i))
    (v : κ → V) (hv : LinearIndependent K v) : LinearIndependent F fun a => e (v a) := by
  classical
  have hfun : ∀ a : κ, ∃ f : V →ₗ[K] K, ∀ a', f (v a') = if a' = a then 1 else 0 := by
    intro a
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.lapply a).comp hv.repr)
    refine ⟨g, fun a' => ?_⟩
    have h := LinearMap.congr_fun hg ⟨v a', Submodule.subset_span (Set.mem_range_self a')⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Finsupp.lapply_apply] at h
    rw [h, hv.repr_eq_single a' _ rfl, Finsupp.single_apply]
  rw [linearIndependent_iff']
  intro s g hg a ha
  obtain ⟨f, hf⟩ := hfun a
  set T : Finset ι := s.biUnion fun a' => (b.repr (v a')).support with hT
  have hx_eq : ∀ x : V, (b.repr x).support ⊆ T → x = ∑ i ∈ T, b.repr x i • b i := by
    intro x hx
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hx]
    intro i _
    exact zero_smul K _
  have hsub : ∀ a' ∈ s, (b.repr (v a')).support ⊆ T := fun a' ha' =>
    Finset.subset_biUnion_of_mem (fun a' => (b.repr (v a')).support) ha'
  have hexp : ∀ a' ∈ s, e (v a') = ∑ i ∈ T, σ (b.repr (v a') i) • e (b i) := by
    intro a' ha'
    conv_lhs => rw [hx_eq (v a') (hsub a' ha')]
    rw [map_sum]
    simp only [map_smulₛₗ]
  have hfv : ∀ a' ∈ s, f (v a') = ∑ i ∈ T, b.repr (v a') i * f (b i) := by
    intro a' ha'
    conv_lhs => rw [hx_eq (v a') (hsub a' ha')]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  have hcoef : ∀ i ∈ T, ∑ a' ∈ s, g a' * σ (b.repr (v a') i) = 0 := by
    have h2 : ∑ i ∈ T, (∑ a' ∈ s, g a' * σ (b.repr (v a') i)) • e (b i) = 0 := by
      rw [← hg]
      simp_rw [Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a' ha' => ?_
      rw [hexp a' ha', Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul]
    exact (linearIndependent_iff'.1 hb) T _ h2
  calc g a = ∑ a' ∈ s, g a' * σ (f (v a')) := by
        rw [Finset.sum_eq_single a]
        · rw [hf a, if_pos rfl, map_one, mul_one]
        · intro a' _ hne
          rw [hf a', if_neg hne, map_zero, mul_zero]
        · intro h
          exact absurd ha h
    _ = ∑ a' ∈ s, g a' * σ (∑ i ∈ T, b.repr (v a') i * f (b i)) :=
        Finset.sum_congr rfl fun a' ha' => by rw [hfv a' ha']
    _ = ∑ i ∈ T, σ (f (b i)) * ∑ a' ∈ s, g a' * σ (b.repr (v a') i) := by
        simp only [map_sum, map_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a' _ => ?_
        ring
    _ = 0 := Finset.sum_eq_zero fun i hi => by rw [hcoef i hi, mul_zero]

def mapSL {K F σ : Type} [Field K] [Field F] (j : K →+* F) : MvPolynomial σ K →ₛₗ[j] MvPolynomial σ F where
  toFun := MvPolynomial.map j
  map_add' := map_add _
  map_smul' := fun c p => by rw [smul_eq_C_mul, map_mul, map_C, smul_eq_C_mul]

theorem map_int_eq (F : Type) [Field F] [CharZero F] {σ : Type} (p : MvPolynomial σ ℤ) :
    MvPolynomial.map (algebraMap ℚ F) (MvPolynomial.map (Int.castRingHom ℚ) p) = MvPolynomial.map (Int.castRingHom F) p := by
  rw [MvPolynomial.map_map, RingHom.ext_int ((algebraMap ℚ F).comp (Int.castRingHom ℚ)) (Int.castRingHom F)]

theorem li_int (F : Type) [Field F] [CharZero F] {N r : ℕ} {M : Submodule ℤ (MvPolynomial (Fin N × Fin N) ℤ)}
    (e : Basis (Fin r) ℤ M) :
    LinearIndependent F fun i => MvPolynomial.map (Int.castRingHom F) (e i : MvPolynomial (Fin N × Fin N) ℤ) := by
  classical
  set v : Fin r → MvPolynomial (Fin N × Fin N) ℚ :=
    fun i => MvPolynomial.map (Int.castRingHom ℚ) (e i : MvPolynomial (Fin N × Fin N) ℤ) with hvdef
  have hvZ : LinearIndependent ℤ v := by
    have h0 : LinearIndependent ℤ fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ) :=
      e.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
    exact h0.map' (MvPolynomial.map (Int.castRingHom ℚ)).toAddMonoidHom.toIntLinearMap
      (LinearMap.ker_eq_bot.2 (MvPolynomial.map_injective _ Int.cast_injective))
  have hvQ : LinearIndependent ℚ v := by
    first
      | exact (LinearIndependent.iff_fractionRing ℤ ℚ).1 hvZ
      | exact (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).1 hvZ
      | exact hvZ.localization ℚ (nonZeroDivisors ℤ)
  have hb : LinearIndependent F fun m =>
      mapSL (σ := Fin N × Fin N) (algebraMap ℚ F) (MvPolynomial.basisMonomials (Fin N × Fin N) ℚ m) := by
    have h := (MvPolynomial.basisMonomials (Fin N × Fin N) F).linearIndependent
    convert h using 1
    all_goals first
      | rfl
      | (funext m; simp [mapSL, MvPolynomial.coe_basisMonomials])
  have h := li_semilin_gen (algebraMap ℚ F) (mapSL (σ := Fin N × Fin N) (algebraMap ℚ F)) _ hb v hvQ
  convert h using 1
  all_goals first
    | rfl
    | (funext i; exact (map_int_eq F _).symm)

end LI

section One

variable (F : Type) [Field F] [CharZero F] {N r : ℕ} {ν : Fin N → ℕ}

theorem span_int (hν : Antitone ν) (e : Basis (Fin r) ℤ (weyl ℤ N N le_rfl ν)) :
    Submodule.span F (Set.range fun i => MvPolynomial.map (Int.castRingHom F) (e i : MvPolynomial (Fin N × Fin N) ℤ)) =
      dualWeyl F N N ν := by
  rw [dualWeyl_eq_weyl F le_rfl ν hν]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact map_mem_weyl le_rfl ν _ (e i).2
  · unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    have hx : applyWord ℤ w (hw ℤ le_rfl ν) ∈ weyl ℤ N N le_rfl ν := Submodule.subset_span ⟨w, rfl⟩
    have h := congrArg (fun y : weyl ℤ N N le_rfl ν => MvPolynomial.map (Int.castRingHom F) (y : MvPolynomial (Fin N × Fin N) ℤ))
      (e.sum_repr (⟨applyWord ℤ w (hw ℤ le_rfl ν), hx⟩ : weyl ℤ N N le_rfl ν))
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum] at h
    rw [SetLike.mem_coe]
    show applyWord F w (hw F le_rfl ν) ∈ _
    rw [← lclosedeq_hw_map (Int.castRingHom F), lclosedeq_applyWord_map, ← h]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _

end One

section Prod

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (lam : ι → DomWeight n) {r : ι → ℕ}
  (e : ∀ τ, Basis (Fin (r τ)) ℤ (weyl ℤ n n le_rfl (lam τ).natW))

def prodZ (I : ∀ τ, Fin (r τ)) : MvPolynomial (ι × Fin n × Fin n) ℤ :=
  Formalism.MainNotions.flipTwoThree.ten fun τ => (e τ (I τ) : MvPolynomial (Fin n × Fin n) ℤ)

theorem map_prodZ (F : Type) [Field F] (I : ∀ τ, Fin (r τ)) :
    MvPolynomial.map (Int.castRingHom F) (prodZ lam e I) =
      ∏ s, blockEmb F s (MvPolynomial.map (Int.castRingHom F) (e s (I s) : MvPolynomial (Fin n × Fin n) ℤ)) := by
  unfold prodZ Formalism.MainNotions.flipTwoThree.ten blockEmb
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => MvPolynomial.map_rename _ _ _

theorem prodZ_span : Submodule.span ℤ (Set.range (prodZ lam e)) = Submodule.span ℤ
    {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℤ, (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧ p = Formalism.MainNotions.flipTwoThree.ten f} := by
  apply le_antisymm
  · refine Submodule.span_mono ?_
    rintro _ ⟨I, rfl⟩
    exact ⟨fun τ => e τ (I τ), fun τ => (e τ (I τ)).2, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hfτ : ∀ τ, f τ = ∑ i, (e τ).repr ⟨f τ, hf τ⟩ i • (e τ i : MvPolynomial (Fin n × Fin n) ℤ) := by
      intro τ
      have := congrArg Subtype.val ((e τ).sum_repr ⟨f τ, hf τ⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    rw [SetLike.mem_coe]
    unfold Formalism.MainNotions.flipTwoThree.ten
    rw [Finset.prod_congr rfl (fun τ _ => by rw [hfτ τ, map_sum]), Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Submodule.sum_mem _ fun I _ => ?_
    have : (∏ τ, rename (Prod.mk τ) ((e τ).repr ⟨f τ, hf τ⟩ (I τ) • (e τ (I τ) : MvPolynomial (Fin n × Fin n) ℤ))) =
        (∏ τ, (e τ).repr ⟨f τ, hf τ⟩ (I τ)) • prodZ lam e I := by
      unfold prodZ Formalism.MainNotions.flipTwoThree.ten
      rw [← Finset.prod_smul]
      exact Finset.prod_congr rfl fun τ _ => map_zsmul _ _ _
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨I, rfl⟩)

def zOf : ZBasis lam where
  J0 := ∀ τ, Fin (r τ)
  bZ := prodZ lam e
  span_eq := prodZ_span lam e
  li := fun F _ _ => by
    have h := (tensorBasis F F ι n n (fun τ => Fin (r τ)) (fun τ => nablaSq F n (lam τ))
      (fun τ i => MvPolynomial.map (Int.castRingHom F) (e τ i : MvPolynomial (Fin n × Fin n) ℤ))
      (fun τ => li_int F (e τ)) (fun τ => span_int F (natW_anti (lam τ)) (e τ))).1
    simpa only [map_prodZ] using h
  span_F := fun F _ _ => by
    have h := (tensorBasis F F ι n n (fun τ => Fin (r τ)) (fun τ => nablaSq F n (lam τ))
      (fun τ i => MvPolynomial.map (Int.castRingHom F) (e τ i : MvPolynomial (Fin n × Fin n) ℤ))
      (fun τ => li_int F (e τ)) (fun τ => span_int F (natW_anti (lam τ)) (e τ))).2
    simp only [map_prodZ]
    exact h

end Prod

section Gram

theorem fockF_eq_fockS {σ : Type} (f g : MvPolynomial σ ℂ) : fockF f g = fockS g f := by
  classical
  unfold fockF fockS mfact
  rw [Finset.sum_subset (Finset.subset_union_left (s₁ := f.support) (s₂ := g.support)) ?_,
    Finset.sum_subset (Finset.subset_union_right (s₁ := f.support) (s₂ := g.support)) ?_]
  all_goals first
    | exact Finset.sum_congr rfl fun m _ => by ring
    | (intro m _ hm
       have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
       simp [h0])
    | (intro m _ hm
       have h0 : g.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
       simp [h0])

theorem fockF_int {σ : Type} (p q : MvPolynomial σ ℤ) :
    fockF (MvPolynomial.map (Int.castRingHom ℂ) p) (MvPolynomial.map (Int.castRingHom ℂ) q) =
      ((fockQ (MvPolynomial.map (Int.castRingHom ℚ) q) (MvPolynomial.map (Int.castRingHom ℚ) p) : ℚ) : ℂ) := by
  classical
  unfold fockF fockQ
  rw [Rat.cast_sum]
  rw [Finset.sum_subset (Finset.subset_union_left (s₁ := (MvPolynomial.map (Int.castRingHom ℂ) p).support)
      (s₂ := (MvPolynomial.map (Int.castRingHom ℚ) q).support)) ?_,
    Finset.sum_subset (Finset.subset_union_right (s₁ := (MvPolynomial.map (Int.castRingHom ℂ) p).support)
      (s₂ := (MvPolynomial.map (Int.castRingHom ℚ) q).support)) ?_]
  all_goals first
    | (refine Finset.sum_congr rfl fun m _ => ?_
       simp only [MvPolynomial.coeff_map, eq_intCast, star_intCast, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast]
       ring)
    | (intro m _ hm
       simp only [MvPolynomial.mem_support_iff, not_not] at hm
       simp [hm])

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (lam : ι → DomWeight n) {r : ι → ℕ}
  (e : ∀ τ, Basis (Fin (r τ)) ℤ (weyl ℤ n n le_rfl (lam τ).natW))

theorem nfAll_prodZ (I I' : ∀ τ, Fin (r τ)) :
    (nfAll lam (MvPolynomial.map (Int.castRingHom ℂ) (prodZ lam e I')) (MvPolynomial.map (Int.castRingHom ℂ) (prodZ lam e I))).re =
    ∏ τ, ((stdGram (lam τ).natW (e τ) (I τ) (I' τ) : ℚ) : ℝ) := by
  have h1 : fockF (MvPolynomial.map (Int.castRingHom ℂ) (prodZ lam e I')) (MvPolynomial.map (Int.castRingHom ℂ) (prodZ lam e I)) =
      ∏ τ, ((fockQ (MvPolynomial.map (Int.castRingHom ℚ) (e τ (I τ) : MvPolynomial (Fin n × Fin n) ℤ))
        (MvPolynomial.map (Int.castRingHom ℚ) (e τ (I' τ) : MvPolynomial (Fin n × Fin n) ℤ)) : ℚ) : ℂ) := by
    rw [fockF_eq_fockS, map_prodZ, map_prodZ]
    have := fockSTen ℂ ι n (fun s => MvPolynomial.map (Int.castRingHom ℂ) (e s (I s) : MvPolynomial (Fin n × Fin n) ℤ))
      (fun s => MvPolynomial.map (Int.castRingHom ℂ) (e s (I' s) : MvPolynomial (Fin n × Fin n) ℤ))
    unfold Formalism.L2.DIV.ten at this
    rw [this]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← fockF_eq_fockS, fockF_int]
  have h2 : ∀ τ, fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ)) =
      ((fockQ (hw ℚ le_rfl (lam τ).natW) (hw ℚ le_rfl (lam τ).natW) : ℚ) : ℂ) := by
    intro τ
    unfold extremal
    rw [← lclosedeq_hw_map (Int.castRingHom ℂ), fockF_int, lclosedeq_hw_map]
  unfold nfAll
  rw [h1, Finset.prod_congr rfl fun τ _ => h2 τ, ← Finset.prod_div_distrib]
  have h3 : ∀ τ, (((fockQ (MvPolynomial.map (Int.castRingHom ℚ) (e τ (I τ) : MvPolynomial (Fin n × Fin n) ℤ))
        (MvPolynomial.map (Int.castRingHom ℚ) (e τ (I' τ) : MvPolynomial (Fin n × Fin n) ℤ)) : ℚ) : ℂ) /
      ((fockQ (hw ℚ le_rfl (lam τ).natW) (hw ℚ le_rfl (lam τ).natW) : ℚ) : ℂ)) =
      (((stdGram (lam τ).natW (e τ) (I τ) (I' τ) : ℚ) : ℝ) : ℂ) := by
    intro τ
    unfold stdGram
    simp
  rw [Finset.prod_congr rfl fun τ _ => h3 τ, ← Complex.ofReal_prod, Complex.ofReal_re]

theorem gramZ_zOf : gramZ lam (zOf lam e) = kron fun τ => (stdGram (lam τ).natW (e τ)).map (Rat.cast : ℚ → ℝ) := by
  ext I I'
  exact nfAll_prodZ lam e I I'

end Gram

theorem stdGram_det_ne {N r : ℕ} {ν : Fin N → ℕ} (hν : Antitone ν) (e : Basis (Fin r) ℤ (weyl ℤ N N le_rfl ν)) :
    (stdGram ν e).det ≠ 0 := by
  obtain ⟨r', ⟨e'⟩⟩ := PI.SlopeSteps.nabla_operator_basis N ν
  have h := (PI.SlopeSteps.gram_matrix_duality N ν r r' e e' hν).2
  intro h0
  have h1 : (PI.SlopeSteps.gramOf ν fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)).det = 0 := h0
  rw [h1, zero_mul] at h
  exact zero_ne_one h

theorem exists_weylBasis (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) :
    ∃ (r : ℕ) (_ : Basis (Fin r) ℤ (weyl ℤ N N le_rfl ν)), 0 < r := by
  obtain ⟨_, r, e, hr, -⟩ := PI.SlopeSteps.muStd_exists N ν hν
  exact ⟨r, e, hr⟩

theorem standard_basis_z : ZBasisStd := by
  classical
  intro ι _ n lam
  choose r e hr using fun τ => exists_weylBasis n (lam τ).natW (natW_anti (lam τ))
  refine ⟨zOf lam e, fun τ => -Real.log ((stdGram (lam τ).natW (e τ)).det : ℝ) / r τ, ⟨fun τ => ⟨0, hr τ⟩⟩,
    fun τ => ⟨r τ, e τ, hr τ, rfl⟩, ?_⟩
  have hdet : ∀ τ, ((stdGram (lam τ).natW (e τ)).map (Rat.cast : ℚ → ℝ)).det = (((stdGram (lam τ).natW (e τ)).det : ℚ) : ℝ) :=
    fun τ => (RingHom.map_det (Rat.castHom ℝ) _).symm
  have h := log_kron (fun τ => (stdGram (lam τ).natW (e τ)).map (Rat.cast : ℚ → ℝ))
    (fun τ => by rw [hdet τ]; exact_mod_cast stdGram_det_ne (natW_anti (lam τ)) (e τ)) hr
  rw [gramZ_zOf, neg_div]
  show -(Real.log (kron fun τ => (stdGram (lam τ).natW (e τ)).map (Rat.cast : ℚ → ℝ)).det /
    (Fintype.card (∀ τ, Fin (r τ)) : ℝ)) = _
  rw [h, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun τ _ => by rw [hdet τ]; exact (neg_div _ _).symm

theorem colSlopeEq_of_Q (D : D7) (h3 : QSlope D) : ColSlopeEq D := colSlopeEq_of translate_span_eq standard_basis_z D h3

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
