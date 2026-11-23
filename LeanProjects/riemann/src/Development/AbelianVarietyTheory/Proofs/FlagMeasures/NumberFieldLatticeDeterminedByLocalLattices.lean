import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsSide
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PlacesRec

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {n : ℕ}

theorem exists_smul_mem (Λ : Submodule (𝓞 E) (Fin n → E))
    (hs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (v : Fin n → E) :
    ∃ D : 𝓞 E, D ≠ 0 ∧ D • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.SaturatedSublattice.main
  | exact _root_.GlobalTheory.SaturatedSublattice.main
  | (apply _root_.GlobalTheory.SaturatedSublattice.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedSublattice.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedSublattice.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedSublattice.main ..)

theorem exists_common (Λ : Submodule (𝓞 E) (Fin n → E))
    (hs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ D : 𝓞 E, D ≠ 0 ∧ ∀ k, D • (Pi.single k 1 : Fin n → E) ∈ Λ := by
  choose Dk h m using fun k => exists_smul_mem Λ hs (Pi.single k 1 : Fin n → E)
  refine ⟨∏ k, Dk k, Finset.prod_ne_zero_iff.2 fun k _ => h k, fun k => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), mul_comm, mul_smul]
  exact Λ.smul_mem _ (m k)

theorem exists_coeffs (Λ : Submodule (𝓞 E) (Fin n → E))
    (hs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (φ : Λ →ₗ[𝓞 E] 𝓞 E) :
    ∃ c : Fin n → E, ∀ y : Λ, ∑ k, c k * (y : Fin n → E) k = ((φ y : 𝓞 E) : E) := by
  obtain ⟨D, hD, m⟩ := exists_common Λ hs
  refine ⟨fun k => ((φ ⟨_, m k⟩ : 𝓞 E) : E) / (D : E), fun y => ?_⟩
  obtain ⟨B, hB⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E))
    (fun k => (y : Fin n → E) k)
  choose b hb using hB
  have hDE : (D : E) ≠ 0 := by simpa using hD
  have hB0 : (B : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero B.2
  have hBE : (((B : 𝓞 E)) : E) ≠ 0 := by simpa using hB0
  have hb' : ∀ k, ((b k : 𝓞 E) : E) = ((B : 𝓞 E) : E) * (y : Fin n → E) k := by
    intro k
    have := hb k
    simpa [Algebra.smul_def] using this
  have hb'' : ∀ k, algebraMap (𝓞 E) E (b k) =
      algebraMap (𝓞 E) E (B : 𝓞 E) * (y : Fin n → E) k := hb'
  have h1 : ((B : 𝓞 E) * D) • y = ∑ k, b k • (⟨_, m k⟩ : Λ) := by
    apply Subtype.ext
    ext i
    simp only [Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Algebra.smul_def (R := 𝓞 E) (A := E), Pi.single_apply]
    have h4 : ∀ x, algebraMap (𝓞 E) E (b x) * (algebraMap (𝓞 E) E D * if i = x then 1 else 0) =
        if i = x then algebraMap (𝓞 E) E (b x) * algebraMap (𝓞 E) E D else 0 := by
      intro x
      split_ifs <;> simp
    simp only [h4, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul]
    rw [hb'' i]
    ring
  have h2 := congrArg φ h1
  rw [map_smul, map_sum] at h2
  simp only [map_smul, smul_eq_mul] at h2
  have h3 := congrArg (fun t : 𝓞 E => (t : E)) h2
  simp only [map_mul, map_sum] at h3
  have hBD : algebraMap (𝓞 E) E (B : 𝓞 E) * algebraMap (𝓞 E) E D ≠ 0 := mul_ne_zero hBE hDE
  apply mul_left_cancel₀ hBD
  refine Eq.trans ?_ h3.symm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hb'' k]
  have hDE' : algebraMap (𝓞 E) E D ≠ 0 := hDE
  change _ * (algebraMap (𝓞 E) E (φ _) / algebraMap (𝓞 E) E D * _) = _
  field_simp

theorem exists_dual_basis (Λ : Submodule (𝓞 E) (Fin n → E)) (h : Submodule.IsLattice E Λ) :
    ∃ (m : ℕ) (g : Fin m → Λ) (φ : Fin m → Λ →ₗ[𝓞 E] 𝓞 E), ∀ y, y = ∑ i, φ i y • g i := by
  haveI := h
  have := Module.IsTorsionFree.trans_faithfulSMul (𝓞 E) E (Fin n → E)
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 h.fg
  have : Module.FinitePresentation (𝓞 E) Λ := Module.finitePresentation_of_finite (𝓞 E) Λ
  have : Module.Flat (𝓞 E) Λ := inferInstance
  have : Module.Projective (𝓞 E) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) Λ
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨m, fun i => f fun j => if i = j then 1 else 0, fun i => LinearMap.proj i ∘ₗ s, fun y => ?_⟩
  have h1 : f (s y) = y := LinearMap.congr_fun hs y
  conv_lhs => rw [← h1, LinearMap.pi_apply_eq_sum_univ f (s y)]
  rfl

section Local

variable (A : Places F E sig)

theorem bc_smul (p : HeightOneSpectrum (𝓞 F)) (a : E) (x : Fin n → E) :
    A.bc p (a • x) = (A.loc p).ιE a • A.bc p x := by
  ext i
  simp [Places.bc]

theorem bc_add (p : HeightOneSpectrum (𝓞 F)) (x y : Fin n → E) :
    A.bc p (x + y) = A.bc p x + A.bc p y := by
  ext i
  simp [Places.bc]

theorem bc_single (p : HeightOneSpectrum (𝓞 F)) (i : Fin n) :
    A.bc p (Pi.single i 1) = (Pi.single i 1 : Fin n → (A.loc p).Ep) := by
  ext j
  by_cases h : j = i
  · subst h; simp [Places.bc]
  · simp [Places.bc, Pi.single_apply, h]

theorem int_mem (p : HeightOneSpectrum (𝓞 F)) (o : 𝓞 E) : (A.loc p).ιE (o : E) ∈ (A.L p).O :=
  ((PlacesInt.integers_local A).1 (o : E)).2 ⟨o, rfl⟩ p

theorem bc_int_smul (p : HeightOneSpectrum (𝓞 F)) (o : 𝓞 E) (x : Fin n → E) :
    A.bc p (o • x) = (⟨_, int_mem A p o⟩ : (A.L p).O) • A.bc p x := by
  ext i
  simp [Places.bc, Subring.smul_def, Algebra.smul_def (R := 𝓞 E) (A := E)]

theorem lat_span (p : HeightOneSpectrum (𝓞 F)) (S : Set (Fin n → E)) :
    A.lat p (Submodule.span (𝓞 E) S) = Submodule.span (A.L p).O (A.bc p '' S) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Submodule.span (𝓞 E) S := hy
    induction hy' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have : A.bc p (0 : Fin n → E) = 0 := by ext i; simp [Places.bc]
      simp [this]
    | add a b ha' hb' ha hb =>
      rw [SetLike.mem_coe, bc_add]
      exact Submodule.add_mem _ (ha ha') (hb hb')
    | smul o a ha' ha =>
      rw [SetLike.mem_coe, bc_int_smul]
      exact Submodule.smul_mem _ _ (ha ha')
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem functional_integral (p : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (c : Fin n → E) (hc : ∀ y ∈ Λ, ∃ o : 𝓞 E, (o : E) = ∑ k, c k * y k)
    (z : Fin n → (A.loc p).Ep) (hz : z ∈ A.lat p Λ) :
    ∑ k, (A.loc p).ιE (c k) * z k ∈ (A.L p).O := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨o, ho⟩ := hc y hy
    have : ∑ k, (A.loc p).ιE (c k) * A.bc p y k = (A.loc p).ιE (o : E) := by
      rw [ho, map_sum]
      simp [Places.bc]
    rw [this]
    exact int_mem A p o
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact add_mem ha hb
  | smul o a _ ha =>
    have : ∑ k, (A.loc p).ιE (c k) * (o • a) k = (o : (A.loc p).Ep) * ∑ k, (A.loc p).ιE (c k) * a k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      ring
    rw [this]
    exact mul_mem o.2 ha

theorem mem_of_forall_lat (Λ : Submodule (𝓞 E) (Fin n → E)) (h : Submodule.IsLattice E Λ)
    (x : Fin n → E) (hx : ∀ p, A.bc p x ∈ A.lat p Λ) : x ∈ Λ := by
  obtain ⟨m, g, φ, hφ⟩ := exists_dual_basis Λ h
  choose c hc using fun i => exists_coeffs Λ h.span_eq_top (φ i)
  have hint : ∀ i, ∃ o : 𝓞 E, (o : E) = ∑ k, c i k * x k := by
    intro i
    refine ((PlacesInt.integers_local A).1 _).1 fun p => ?_
    have := functional_integral A p Λ (c i)
      (fun y hy => ⟨φ i ⟨y, hy⟩, (hc i ⟨y, hy⟩).symm⟩) _ (hx p)
    rw [map_sum]
    simpa [Places.bc] using this
  choose o ho using hint
  obtain ⟨D, hD, hDx⟩ := exists_smul_mem Λ h.span_eq_top x
  have hDE : (D : E) ≠ 0 := by simpa using hD
  have h1 : x = ∑ i, o i • (g i : Fin n → E) := by
    have h2 := congrArg (Subtype.val) (hφ ⟨D • x, hDx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    have h3 : ∀ i, ((φ i ⟨D • x, hDx⟩ : 𝓞 E) : E) = (D : E) * (o i : E) := by
      intro i
      rw [← hc i ⟨D • x, hDx⟩, ho i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.smul_apply, Algebra.smul_def (R := 𝓞 E) (A := E)]
      change _ * ((algebraMap (𝓞 E) E D) * _) = (algebraMap (𝓞 E) E D) * _
      ring
    ext j
    have h4 := congrFun h2 j
    simp only [Pi.smul_apply, Finset.sum_apply, Algebra.smul_def (R := 𝓞 E) (A := E)] at h4 ⊢
    apply mul_left_cancel₀ hDE
    refine Eq.trans h4 ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h5 := h3 i
    change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E D * algebraMap (𝓞 E) E _ at h5
    rw [h5]
    change _ = algebraMap (𝓞 E) E D * _
    ring
  rw [h1]
  exact Λ.sum_mem fun i _ => Λ.smul_mem _ (g i).2

end Local

theorem lattice_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ p, A.bc p x ∈ A.lat p Λ) ∧ (∀ p, IsLat (A.L p) (A.lat p Λ)) ∧ {p | A.lat p Λ ≠ Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite := by
  intro F E _ _ _ _ _ sig A n Λ h
  obtain ⟨D, hD, hm⟩ := exists_common Λ h.span_eq_top
  have hDE : (D : E) ≠ 0 := by simpa using hD
  have hsingle : ∀ p (i : Fin n), (Pi.single i 1 : Fin n → (A.loc p).Ep) =
      (A.loc p).ιE (D : E)⁻¹ • A.bc p (D • (Pi.single i 1 : Fin n → E)) := by
    intro p i
    rw [← bc_smul, ← bc_single A p i]
    congr 1
    ext j
    simp only [Pi.smul_apply, Algebra.smul_def (R := 𝓞 E) (A := E), smul_eq_mul]
    change _ = ((D : E))⁻¹ * ((D : E) * _)
    field_simp
  obtain ⟨S, hS⟩ := h.fg
  refine ⟨fun x => ⟨fun hx p => Submodule.subset_span ⟨x, hx, rfl⟩, mem_of_forall_lat A Λ h x⟩,
    fun p => ⟨?_, ?_⟩, ?_⟩
  · rw [← hS, lat_span]
    exact Submodule.fg_span (S.finite_toSet.image _)
  · rw [eq_top_iff]
    intro v _
    have hv : v = ∑ i, v i • (Pi.single i 1 : Fin n → (A.loc p).Ep) := by
      ext j
      simp [Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [hsingle p i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      (Submodule.subset_span ⟨_, hm i, rfl⟩))
  · have hfin := (PlacesInt.integers_local A).2.1
    have h1 : (⋃ s ∈ (S : Set (Fin n → E)), ⋃ i, {p | (A.loc p).ιE (s i) ∉ (A.L p).O}).Finite :=
      S.finite_toSet.biUnion fun s _ => Set.finite_iUnion fun i => hfin (s i)
    refine (h1.union (hfin (D : E)⁻¹)).subset fun p hp => ?_
    by_contra hnot
    apply hp
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_not] at hnot
    obtain ⟨hn1, hn2⟩ := hnot
    apply le_antisymm
    · rw [← hS, lat_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨s, hs, rfl⟩
      have hv : A.bc p s = ∑ i, (⟨_, hn1 s hs i⟩ : (A.L p).O) •
          (Pi.single i 1 : Fin n → (A.loc p).Ep) := by
        ext j
        simp [Pi.single_apply, Places.bc, Subring.smul_def]
      rw [SetLike.mem_coe, hv]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, rfl⟩)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      have h2 := Submodule.smul_mem (A.lat p Λ) (⟨_, hn2⟩ : (A.L p).O)
        (Submodule.subset_span ⟨_, hm i, rfl⟩ : A.bc p (D • (Pi.single i 1 : Fin n → E)) ∈ A.lat p Λ)
      rw [SetLike.mem_coe]
      beta_reduce
      rw [hsingle p i]
      exact h2

end GlobalTheory.HL.PlacesRec
