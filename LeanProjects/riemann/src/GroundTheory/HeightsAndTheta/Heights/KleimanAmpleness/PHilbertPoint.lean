import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace HilbertPoint

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

def aff (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) : Fin (N + 1) → Ω := fun l => y l / y j

theorem aff_def (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) : aff y j = fun l => y l / y j := rfl

variable (k) in

def affRing (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) : Subalgebra k Ω :=
  (aeval (aff y j) : Poly k N →ₐ[k] Ω).range

variable (k) in

def affPiece (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) (n : ℕ) : Submodule k Ω :=
  Submodule.span k {z | ∃ f : Poly k N, f.IsHomogeneous n ∧ z = aeval (aff y j) f}

variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}

theorem aeval_aff_of_mem_primeOf {f : Poly k N} (hf : f ∈ primeOf (S := k) y) :
    aeval (aff y j) f = 0 := by
  rw [← sum_homogeneousComponent f, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [aff_def, aeval_div_of_isHomogeneous (homogeneousComponent_isHomogeneous d f),
    (mem_primeOf_of_isHomogeneous y (homogeneousComponent_isHomogeneous d f)).mp
      (homogeneousComponent_mem_primeOf y hf d), zero_div]

theorem le_zero_of_add_one_le_one {d : WithBot ℕ∞} (h : d + 1 ≤ 1) : d ≤ 0 := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    have h' : e + 1 ≤ 1 := by exact_mod_cast h
    induction e using ENat.recTopCoe with
    | top => simp at h'
    | coe m =>
      have : m + 1 ≤ 1 := by exact_mod_cast h'
      have hm : m = 0 := by omega
      subst hm
      simp

theorem isField_affRing (hy : IsSubvar y (primeOf (S := k) y) 0) (hj : y j ≠ 0) :
    IsField (affRing k y j) := by
  let φ : Poly k N →ₐ[k] affRing k y j := (aeval (aff y j)).rangeRestrict
  have hφ : Function.Surjective φ := AlgHom.rangeRestrict_surjective _
  have hker : ∀ f ∈ primeOf (S := k) y, φ.toRingHom f = 0 := fun f hf =>
    Subtype.ext (aeval_aff_of_mem_primeOf hf)
  let ψ : Poly k N ⧸ primeOf (S := k) y →+* affRing k y j :=
    Ideal.Quotient.lift (primeOf (S := k) y) φ.toRingHom hker
  have hψ : Function.Surjective ψ := Ideal.Quotient.lift_surjective_of_surjective _ hker hφ
  let r : Poly k N ⧸ primeOf (S := k) y := Ideal.Quotient.mk _ (X j - 1)
  have hr : r ≠ 0 := by
    intro h
    have hmem : (X j - 1 : Poly k N) ∈ primeOf (S := k) y := Ideal.Quotient.eq_zero_iff_mem.mp h
    have h0 := homogeneousComponent_mem_primeOf y hmem 0
    rw [homogeneousComponent_zero] at h0
    have := (mem_primeOf_of_isHomogeneous y (isHomogeneous_C _ _)).mp h0
    simp at this
  have hr' : r ∈ nonZeroDivisors (Poly k N ⧸ primeOf (S := k) y) := mem_nonZeroDivisors_of_ne_zero hr
  have hψr : ψ r = 0 := by
    apply Subtype.ext
    change aeval (aff y j) (X j - 1 : Poly k N) = 0
    simp [aff, hj]
  have hrψ : ∀ a ∈ Ideal.span {r}, ψ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hψr, mul_zero]
  have hχ : Function.Surjective (Ideal.Quotient.lift (Ideal.span {r}) ψ hrψ) :=
    Ideal.Quotient.lift_surjective_of_surjective _ hrψ hψ
  have h1 : ringKrullDim (affRing k y j) ≤
      ringKrullDim ((Poly k N ⧸ primeOf (S := k) y) ⧸ Ideal.span {r}) := by
    exact ringKrullDim_le_of_surjective _ hχ
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr'
  rw [hy.dim] at h2
  have h3 : ringKrullDim (affRing k y j) ≤ 0 :=
    le_zero_of_add_one_le_one ((add_le_add h1 (le_refl (1 : WithBot ℕ∞))).trans (by simpa using h2))
  have : Ring.KrullDimLE 0 (affRing k y j) := Ring.krullDimLE_iff.mpr (by simpa using h3)
  exact Ring.KrullDimLE.isField_of_isDomain

theorem funField_eq (hj : y j ≠ 0) (hF : IsField (affRing k y j)) :
    funField (k := k) y = (affRing k y j).toIntermediateField' hF := by
  have haff : ∀ l, aff y j l ∈ (affRing k y j).toIntermediateField' hF := fun l =>
    show aff y j l ∈ affRing k y j from ⟨X l, by simp⟩
  apply le_antisymm
  · rw [funField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, l, hi, rfl⟩
    have : y l / y i = aff y j l * (aff y j i)⁻¹ := by
      simp only [aff]; field_simp
    rw [this]
    exact mul_mem (haff l) (inv_mem (haff i))
  · intro z hz
    change z ∈ affRing k y j at hz
    rw [affRing, ← Algebra.adjoin_range_eq_range_aeval] at hz
    refine Algebra.adjoin_le (S := (funField (k := k) y).toSubalgebra) ?_ hz
    rintro _ ⟨l, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨j, l, hj, rfl⟩

theorem finiteDimensional_affField (hy : IsSubvar y (primeOf (S := k) y) 0) (hj : y j ≠ 0) :
    FiniteDimensional k ((affRing k y j).toIntermediateField' (isField_affRing hy hj)) := by
  set E := (affRing k y j).toIntermediateField' (isField_affRing hy hj)
  let g : Poly k N →ₐ[k] E :=
    AlgHom.codRestrict (aeval (aff y j) : Poly k N →ₐ[k] Ω) E.toSubalgebra
      (fun f => show _ ∈ affRing k y j from ⟨f, rfl⟩)
  have hg : Function.Surjective g := by
    rintro ⟨z, f, rfl⟩
    exact ⟨f, rfl⟩
  have : Algebra.FiniteType k E := Algebra.FiniteType.of_surjective g hg
  exact finite_of_finite_type_of_isJacobsonRing k E

theorem affPiece_le (n : ℕ) : affPiece k y j n ≤ Subalgebra.toSubmodule (affRing k y j) :=
  Submodule.span_le.mpr (by rintro _ ⟨f, _, rfl⟩; exact ⟨f, rfl⟩)

theorem affPiece_mono (hj : y j ≠ 0) {m n : ℕ} (h : m ≤ n) :
    affPiece k y j m ≤ affPiece k y j n := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  refine Submodule.subset_span ⟨X j ^ (n - m) * f, ?_, ?_⟩
  · have := (isHomogeneous_X_pow (R := k) j (n - m)).mul hf
    rwa [Nat.sub_add_cancel h] at this
  · simp [aff, hj]

theorem aeval_mem_affPiece (hj : y j ≠ 0) (f : Poly k N) :
    aeval (aff y j) f ∈ affPiece k y j f.totalDegree := by
  rw [show aeval (aff y j) f = ∑ d ∈ Finset.range (f.totalDegree + 1),
      aeval (aff y j) (homogeneousComponent d f) by rw [← map_sum, sum_homogeneousComponent]]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hd' : d ≤ f.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  exact affPiece_mono hj hd' (Submodule.subset_span ⟨_, homogeneousComponent_isHomogeneous d f, rfl⟩)

theorem eventually_affPiece_eq (hy : IsSubvar y (primeOf (S := k) y) 0) (hj : y j ≠ 0) :
    ∀ᶠ n : ℕ in atTop, affPiece k y j n = Subalgebra.toSubmodule (affRing k y j) := by
  have := finiteDimensional_affField hy hj
  have hfin : (Subalgebra.toSubmodule (affRing k y j)).FG := by
    rw [← Module.Finite.iff_fg]
    exact inferInstanceAs (Module.Finite k ((affRing k y j).toIntermediateField' (isField_affRing hy hj)))
  obtain ⟨s, hs⟩ := hfin
  have hex : ∀ z ∈ s, ∃ n, z ∈ affPiece k y j n := fun z hz => by
    have : z ∈ affRing k y j := by
      rw [← Subalgebra.mem_toSubmodule, ← hs]; exact Submodule.subset_span hz
    obtain ⟨f, rfl⟩ := this
    exact ⟨_, aeval_mem_affPiece hj f⟩
  choose! m hm using hex
  refine eventually_atTop.mpr ⟨s.sup m, fun n hn => le_antisymm (affPiece_le n) ?_⟩
  rw [← hs, Submodule.span_le]
  intro z hz
  exact affPiece_mono hj ((Finset.le_sup hz).trans hn) (hm z hz)

theorem coordGraded_piece_eq (hj : y j ≠ 0) (n : ℕ) :
    (coordGraded k y).piece (n : ℤ) = (affPiece k y j n).map (LinearMap.mulLeft k (y j ^ n)) := by
  rw [show (coordGraded k y).piece (n : ℤ) = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ),
    f.IsHomogeneous e ∧ (e : ℤ) = n ∧ z = aeval y f} from rfl, affPiece, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨f, e, hf, he, rfl⟩
    have hen : e = n := by exact_mod_cast he
    subst hen
    refine ⟨aeval (aff y j) f, ⟨f, hf, rfl⟩, ?_⟩
    rw [LinearMap.mulLeft_apply, aff_def, aeval_div_of_isHomogeneous hf]
    field_simp
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨f, n, hf, rfl, ?_⟩
    rw [LinearMap.mulLeft_apply, aff_def, aeval_div_of_isHomogeneous hf]
    field_simp

theorem coordGraded_le_secs (n : ℕ) :
    (coordGraded k y).piece (n : ℤ) ≤ (twistSys k y (n : ℤ)).secs := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, e, hf, he, rfl⟩
  refine (Submodule.mem_iInf _).mpr fun I => ?_
  exact Submodule.subset_span ⟨f, 1, 0, e, one_mem _, hf, isHomogeneous_one _ _, by simp [he],
    by simp⟩

theorem affRing_eq_ampleBase : affRing k y j = ampleBase (S := k) y j := by
  rw [affRing, ampleBase, Algebra.adjoin_range_eq_range_aeval]
  rfl

theorem div_mem_affRing_of_mem_twistMod (hj : y j ≠ 0) (n : ℕ) {z : Ω}
    (hz : z ∈ twistMod k y (n : ℤ) (singleChart hj)) : z / y j ^ n ∈ affRing k y j := by
  refine Submodule.span_induction (p := fun z _ => z / y j ^ n ∈ affRing k y j) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    have hs' : s ∈ Submonoid.closure {(X j : Poly k N)} := by
      have : ((fun i => (X i : Poly k N)) '' ((({j} : Finset (Fin (N + 1))) : Set (Fin (N + 1))))) =
          {X j} := by simp
      rw [← this]; exact hs
    obtain ⟨m, rfl⟩ := Submonoid.mem_closure_singleton.mp hs'
    have hme : e = m := hse.inj_right (isHomogeneous_X_pow j m) (by
      rw [X_pow_eq_monomial, Ne, monomial_eq_zero]; exact one_ne_zero)
    subst hme
    have he' : e' = e + n := by omega
    subst he'
    refine ⟨f, ?_⟩
    change aeval (aff y j) f = _
    rw [aff_def, aeval_div_of_isHomogeneous hf, map_pow, aeval_X, pow_add, div_div]
  · simp
  · intro a b _ _ ha hb
    rw [add_div]; exact add_mem ha hb
  · intro c z _ hz
    rw [chartRing_smul_def, mul_div_assoc]
    refine mul_mem ?_ hz
    rw [affRing_eq_ampleBase]
    exact mem_ampleBase_of_mem_chartRing (S := k) hj c.2

theorem proof : HilbertPoint.Statement.{u, w} := by
  intro k _ Ω _ _ N y hy
  obtain ⟨j, hjX⟩ := hy.relevant
  have hj : y j ≠ 0 := fun h =>
    hjX ((mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j)).mpr (by simp [h]))
  have hF := isField_affRing hy hj
  have hfun := funField_eq hj hF
  have hfd := finiteDimensional_affField hy hj
  have hev := eventually_affPiece_eq hy hj
  refine ⟨hfun ▸ hfd, hev.mono fun n hn => ?_, hev.mono fun n hn => ?_⟩
  · have hinj : Function.Injective (LinearMap.mulLeft k (y j ^ n)) :=
      mul_right_injective₀ (pow_ne_zero n hj)
    rw [coordGraded_piece_eq hj n,
      ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _), hn,
      Subalgebra.finrank_toSubmodule, hfun, ← IntermediateField.finrank_eq_finrank_subalgebra]
    rfl
  · refine le_antisymm ?_ (coordGraded_le_secs n)
    intro z hz
    have hz1 : z ∈ twistMod k y (n : ℤ) (singleChart hj) :=
      (Submodule.mem_iInf _).mp hz (singleChart hj)
    have hd := div_mem_affRing_of_mem_twistMod hj n hz1
    rw [coordGraded_piece_eq hj n, hn]
    refine ⟨z / y j ^ n, hd, ?_⟩
    rw [LinearMap.mulLeft_apply]
    field_simp

end HilbertPoint

end

end GroundTheory.Heights₂.Heights.Kleiman
