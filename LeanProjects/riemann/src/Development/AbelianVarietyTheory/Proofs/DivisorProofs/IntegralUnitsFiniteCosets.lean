import Mathlib
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongNIndex

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def embO : 𝓞 E →+* RInt F E :=
  RingHom.codRestrict
    ((Algebra.TensorProduct.includeLeft : E →ₐ[F] AfE F E).toRingHom.comp (algebraMap (𝓞 E) E))
    (RInt F E) fun o => Subring.subset_closure (Set.mem_union_left _ ⟨⟨_, RingHom.mem_range.2 ⟨o, rfl⟩⟩, rfl⟩)

def redO (N : ℕ) : 𝓞 E →+* RInt F E ⧸ Ideal.span {(N : RInt F E)} :=
  (Ideal.Quotient.mk _).comp (embO F E)

theorem one_tmul_mem {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ intAd F) :
    (1 : E) ⊗ₜ[F] a ∈ RInt F E :=
  Subring.subset_closure (Set.mem_union_right _ ⟨⟨a, ha⟩, rfl⟩)

theorem mk_mem_range (N : ℕ) (hN : 0 < N) (z : RInt F E) :
    Ideal.Quotient.mk (Ideal.span {(N : RInt F E)}) z ∈ (redO F E N).range := by
  let T : Subring (RInt F E) := (redO F E N).range.comap (Ideal.Quotient.mk _)
  have hN0 : Ideal.Quotient.mk (Ideal.span {(N : RInt F E)}) (N : RInt F E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have key : RInt F E ≤ T.map (RInt F E).subtype := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, o, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · exact ⟨embO F E o, ⟨o, rfl⟩, rfl⟩
    · obtain ⟨x, a, ha, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).2 y hy
      refine ⟨embO F E (algebraMap (𝓞 F) (𝓞 E) x) + (N : RInt F E) * ⟨_, one_tmul_mem F E (a := a) ha⟩,
        ⟨algebraMap (𝓞 F) (𝓞 E) x, ?_⟩, ?_⟩
      · show redO F E N _ = Ideal.Quotient.mk _ _
        rw [map_add, map_mul, hN0, zero_mul, add_zero]
        rfl
      · show ((algebraMap F E (x : F)) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) + (N : AfE F E) * ((1 : E) ⊗ₜ[F] a) = (1 : E) ⊗ₜ[F] y
        rw [e, TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 F) F),
          TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one,
          TensorProduct.tmul_smul, nsmul_eq_mul]
  obtain ⟨w, hw, e⟩ := key z.2
  have : w = z := Subtype.ext e
  subst this
  exact hw

theorem finite_quot (N : ℕ) (hN : 0 < N) : Finite (RInt F E ⧸ Ideal.span {(N : RInt F E)}) := by
  haveI : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := by
    apply Ideal.finiteQuotientOfFreeOfNeBot
    simp [Ideal.span_singleton_eq_bot]; omega
  have hN0 : Ideal.Quotient.mk (Ideal.span {(N : RInt F E)}) (N : RInt F E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  let φ : 𝓞 E ⧸ Ideal.span {(N : 𝓞 E)} →+* RInt F E ⧸ Ideal.span {(N : RInt F E)} :=
    Ideal.Quotient.lift _ (redO F E N) fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, map_natCast, ← map_natCast (Ideal.Quotient.mk (Ideal.span {(N : RInt F E)})), hN0, mul_zero]
  refine Finite.of_surjective φ fun q => ?_
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨o, ho⟩ := mk_mem_range F E N hN z
  exact ⟨Ideal.Quotient.mk _ o, ho⟩

def toU : intU F E ≃* (RInt F E)ˣ := Submonoid.unitsEquivUnitsType (RInt F E).toSubmonoid

theorem exists_finset (N : ℕ) (hN : 0 < N) :
    ∃ S : Finset (AfE F E)ˣ, ∀ k ∈ intU F E, ∃ s ∈ S, s⁻¹ * k ∈ congN F E N := by
  classical
  haveI := finite_quot F E N hN
  let I := Ideal.span {(N : RInt F E)}
  let f : (AfE F E)ˣ → (RInt F E ⧸ I)ˣ := fun k =>
    if h : k ∈ intU F E then Units.map (Ideal.Quotient.mk I).toMonoidHom (toU F E ⟨k, h⟩) else 1
  let g : (RInt F E ⧸ I)ˣ → (AfE F E)ˣ := fun q =>
    if h : ∃ k ∈ intU F E, f k = q then h.choose else 1
  refine ⟨(Set.finite_range g).toFinset, fun k hk => ?_⟩
  have hex : ∃ k' ∈ intU F E, f k' = f k := ⟨k, hk, rfl⟩
  have hg : g (f k) = hex.choose := dif_pos hex
  obtain ⟨hs, hfs⟩ := hex.choose_spec
  refine ⟨g (f k), (Set.finite_range g).mem_toFinset.2 ⟨_, rfl⟩, ?_⟩
  rw [hg]
  set s := hex.choose
  refine ⟨(toU F E ⟨s, hs⟩)⁻¹ * toU F E ⟨k, hk⟩, ?_, ?_⟩
  · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    have h1 : f s = _ := dif_pos hs
    have h2 : f k = _ := dif_pos hk
    rw [← h1, ← h2, hfs]
  · ext
    simp only [map_mul, map_inv, Units.val_mul]
    rfl

end GlobalTheory.CongNIndex

theorem GlobalTheory.congN_finite_index : ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N →
    ∃ S : Finset (AfE ℚ L)ˣ, ∀ k ∈ intU ℚ L, ∃ s ∈ S, s⁻¹ * k ∈ congN ℚ L N :=
  fun L _ _ N hN => GlobalTheory.CongNIndex.exists_finset ℚ L N hN
