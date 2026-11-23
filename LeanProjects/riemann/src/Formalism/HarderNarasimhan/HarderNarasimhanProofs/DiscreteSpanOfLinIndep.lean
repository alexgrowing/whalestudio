import Formalism.HarderNarasimhan.StatementPl
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe

open Module NumberField

noncomputable section

namespace Formalism.HN

namespace PlaceLattice

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

theorem realize_apply0 (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (v : InfinitePlace K) (i : ι) :
    (Formalism.HermitianLatticesTheory.realize b X x) (v, i, 0) = (Formalism.HermitianLatticesTheory.fcoord b X v x i).re := by
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw]

theorem realize_apply1 (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (v : InfinitePlace K) (i : ι) :
    (Formalism.HermitianLatticesTheory.realize b X x) (v, i, 1) = (Formalism.HermitianLatticesTheory.fcoord b X v x i).im := by
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw]

theorem realize_injective (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) : Function.Injective (Formalism.HermitianLatticesTheory.realize b X) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hf : ∀ v i, Formalism.HermitianLatticesTheory.fcoord b X v x i = 0 := by
    intro v i
    apply Complex.ext
    · rw [← realize_apply0, hx]
      rfl
    · rw [← realize_apply1, hx]
      rfl
  have hv : ∀ v, Formalism.HermitianLatticesTheory.vecAt b v x = 0 := by
    intro v
    have h0 : (X v)⁻¹.mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) = 0 := funext (hf v)
    have h1 := congrArg (X v).mulVec h0
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec,
      Matrix.mulVec_zero] at h1
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  apply b.repr.injective
  ext i
  have := congrFun (hv v) i
  simp only [Formalism.HermitianLatticesTheory.vecAt, Pi.zero_apply, map_eq_zero] at this
  simpa using this

theorem sum_embedding_eq_zero {t : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ}
    (h : ∀ v : InfinitePlace K, ∑ k, (t k : ℂ) * v.embedding (integralBasis K k) = 0) : t = 0 := by
  have hφ : ∀ φ : K →+* ℂ, ∑ k, (t k : ℂ) * φ (integralBasis K k) = 0 := by
    intro φ
    rcases InfinitePlace.embedding_mk_eq φ with hφ | hφ
    · simpa [hφ] using h (InfinitePlace.mk φ)
    · have h2 := congrArg (starRingEnd ℂ) (h (InfinitePlace.mk φ))
      simpa [hφ, map_sum, map_mul, Complex.conj_ofReal] using h2
  have hli := (canonicalEmbedding.latticeBasis K).linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have hz := hli (fun k => (t k : ℂ)) (by
    funext φ
    simpa [canonicalEmbedding.latticeBasis_apply, Finset.sum_apply, smul_eq_mul] using hφ φ)
  funext k
  exact_mod_cast hz k

theorem vecAt_smul_basis (b : Basis ι K V) (v : InfinitePlace K) (a : K) (i : ι) :
    Formalism.HermitianLatticesTheory.vecAt b v (a • b i) = Pi.single i (v.embedding a) := by
  funext i'
  simp only [Formalism.HermitianLatticesTheory.vecAt, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.single_apply, Pi.single_apply]
  by_cases h : i = i'
  · subst h; simp
  · simp [h, Ne.symm h]

end PlaceLattice
end Formalism.HN

namespace Formalism.HN
namespace PlaceLattice

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

theorem linIndep_real (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (c : K) (hc : c ≠ 0) :
    LinearIndependent ℝ (fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι =>
      Formalism.HermitianLatticesTheory.realize b X (integralBasis K p.1 • c • b p.2)) := by
  rw [Fintype.linearIndependent_iff]
  intro t ht p
  have hcoord : ∀ v i r, ∑ q, t q * (Formalism.HermitianLatticesTheory.realize b X (integralBasis K q.1 • c • b q.2)) (v, i, r) = 0 := by
    intro v i r
    have := congrArg (fun z => z (v, i, r)) ht
    simpa using this
  have hC : ∀ v i, ∑ q, (t q : ℂ) * Formalism.HermitianLatticesTheory.fcoord b X v (integralBasis K q.1 • c • b q.2) i = 0 := by
    intro v i
    apply Complex.ext
    · have := hcoord v i 0
      simp only [realize_apply0] at this
      simpa [Complex.re_sum] using this
    · have := hcoord v i 1
      simp only [realize_apply1] at this
      simpa [Complex.im_sum] using this
  have hV : ∀ v, ∑ q, (t q : ℂ) • Formalism.HermitianLatticesTheory.vecAt b v (integralBasis K q.1 • c • b q.2) = 0 := by
    intro v
    have h0 : Matrix.mulVec (X v)⁻¹ (∑ q, (t q : ℂ) • Formalism.HermitianLatticesTheory.vecAt b v (integralBasis K q.1 • c • b q.2)) = 0 := by
      funext i
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      simpa [Formalism.HermitianLatticesTheory.fcoord] using hC v i
    have hinv : X v * (X v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hX v)
    calc _ = Matrix.mulVec (X v * (X v)⁻¹) (∑ q, (t q : ℂ) • Formalism.HermitianLatticesTheory.vecAt b v (integralBasis K q.1 • c • b q.2)) := by
          rw [hinv, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  have hS : ∀ v : InfinitePlace K, ∑ k, ((t (k, p.2) : ℝ) : ℂ) * v.embedding (integralBasis K k) = 0 := by
    intro v
    have h1 := congrFun (hV v) p.2
    simp only [smul_smul, vecAt_smul_basis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fintype.sum_prod_type, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, map_mul] at h1
    have hc' : v.embedding c ≠ 0 := by simpa using hc
    have h2 : (∑ k, (t (k, p.2) : ℂ) * v.embedding (integralBasis K k)) * v.embedding c = 0 := by
      rw [Finset.sum_mul]
      simpa [mul_assoc] using h1
    exact (mul_eq_zero.mp h2).resolve_right hc'
  have := sum_embedding_eq_zero hS
  exact congrFun this p.1

theorem discrete_span_of_linIndep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι' : Type*} {f : ι' → E} (hf : LinearIndependent ℝ f) :
    DiscreteTopology (Submodule.span ℤ (Set.range f)) := by
  classical
  haveI : Finite ι' := hf.finite
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend (Basis.span hf).equivFun.toLinearMap
  have hψW : ∀ w : Submodule.span ℝ (Set.range f), ψ w = (Basis.span hf).equivFun w :=
    fun w => LinearMap.congr_fun hψ w
  have hψf : ∀ i, ψ (f i) = Pi.basisFun ℝ ι' i := by
    intro i
    have h : ψ (f i) = (Basis.span hf).equivFun (Basis.span hf i) := by
      rw [Basis.span_apply]
      exact hψW ⟨f i, Submodule.subset_span ⟨i, rfl⟩⟩
    rw [h]
    ext j
    simp [Basis.equivFun_self, Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hmem : ∀ x ∈ Submodule.span ℤ (Set.range f),
      ψ x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι')) := by
    intro x hx
    have hle : Submodule.map (ψ.restrictScalars ℤ) (Submodule.span ℤ (Set.range f)) ≤
        Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι')) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨i, (hψf i).symm⟩
    exact hle ⟨x, hx, rfl⟩
  have hW : ∀ z ∈ Submodule.span ℤ (Set.range f), z ∈ Submodule.span ℝ (Set.range f) :=
    fun z hz => Submodule.span_le_restrictScalars ℤ ℝ _ hz
  haveI := ZSpan.discreteTopology_pi_basisFun (ι := ι')
  refine DiscreteTopology.of_continuous_injective
    (f := fun x : Submodule.span ℤ (Set.range f) =>
      (⟨ψ x, hmem x x.2⟩ : Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι')))) ?_ ?_
  · fun_prop
  · intro x y hxy
    have h1 : ψ x = ψ y := congrArg Subtype.val hxy
    have h2 : (⟨(x : E), hW _ x.2⟩ : Submodule.span ℝ (Set.range f)) = ⟨y, hW _ y.2⟩ :=
      (Basis.span hf).equivFun.injective (by rw [← hψW, ← hψW]; exact h1)
    exact Subtype.ext (Subtype.mk.inj h2)

end PlaceLattice
end Formalism.HN

namespace Formalism.HN
namespace PlaceLattice

variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem zl_span_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (ρ : V →+ E) {ι' : Type} [Fintype ι'] (e : ι' → V) :
    zl ρ (Submodule.span (𝓞 K) (Set.range e)) =
      Submodule.span ℤ (Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
        ρ (integralBasis K p.1 • e p.2)) := by
  have hs : Submodule.span ℤ (Set.range (RingOfIntegers.basis K)) = ⊤ := (RingOfIntegers.basis K).span_eq
  have h1 := Submodule.span_smul_of_span_eq_top hs (Set.range e)
  open Pointwise in
  have hset : Set.range (RingOfIntegers.basis K) • Set.range e =
      Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' => integralBasis K p.1 • e p.2 := by
    ext x
    simp only [Set.mem_smul, Set.mem_range, Prod.exists, integralBasis_apply, algebraMap_smul]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      exact ⟨i, j, rfl⟩
    · rintro ⟨i, j, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
  rw [hset] at h1
  have h2 : Submodule.span ℤ (Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
      ρ (integralBasis K p.1 • e p.2)) =
      (Submodule.span ℤ (Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
        integralBasis K p.1 • e p.2)).map ρ.toIntLinearMap := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [h2, h1]
  ext x
  exact Iff.rfl

theorem linIndep_int {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (ρ : V →+ E) (hρ : Function.Injective ρ) {ι' : Type} [Fintype ι']
    (e : ι' → V) (he : LinearIndependent K e) :
    LinearIndependent ℤ (fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
        ρ (integralBasis K p.1 • e p.2)) := by
  have hb : LinearIndependent ℤ (integralBasis K) :=
    (integralBasis K).linearIndependent.restrict_scalars' ℤ
  have hc : LinearIndependent ℤ fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
      integralBasis K p.1 • e p.2 :=
    linearIndependent_smul hb he
  exact hc.map' ρ.toIntLinearMap (LinearMap.ker_eq_bot.mpr hρ)

theorem rk_span_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (ρ : V →+ E) (hρ : Function.Injective ρ) {ι' : Type} [Fintype ι']
    (e : ι' → V) (he : LinearIndependent K e) :
    rk ρ (Submodule.span (𝓞 K) (Set.range e)) = Module.finrank ℚ K * Fintype.card ι' := by
  unfold rk Formalism.F.rk
  rw [zl_span_eq, finrank_span_eq_card (linIndep_int ρ hρ e he), Fintype.card_prod,
    ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]

theorem exists_denom {ι' : Type} [Fintype ι'] (e : ι' → V) (N : Submodule (𝓞 K) V) (hN : N.FG)
    (hsub : ∀ x ∈ N, x ∈ Submodule.span K (Set.range e)) :
    ∃ y : ℤ, y ≠ 0 ∧ N ≤ Submodule.span (𝓞 K) (Set.range fun a => ((y : K)⁻¹) • e a) := by
  classical
  obtain ⟨S, rfl⟩ := hN
  have hc : ∀ x : S, ∃ c : ι' → K, ∑ j, c j • e j = (x : V) := fun x =>
    (Submodule.mem_span_range_iff_exists_fun K).1 (hsub x (Submodule.subset_span x.2))
  choose c hc using hc
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.biUnion fun x : S => Finset.univ.image (c x))
  refine ⟨y, hy0, ?_⟩
  rw [Submodule.span_le]
  intro x hx
  have hyK : (y : K) ≠ 0 := Int.cast_ne_zero.2 hy0
  suffices h : ∑ j, c ⟨x, hx⟩ j • e j ∈ Submodule.span (𝓞 K) (Set.range fun a => ((y : K)⁻¹) • e a) by
    rwa [hc ⟨x, hx⟩] at h
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨r, hr⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).1
    (hy (c ⟨x, hx⟩ j) (Finset.mem_biUnion.2 ⟨⟨x, hx⟩, Finset.mem_univ _,
      Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩))
  have : c ⟨x, hx⟩ j • e j = r • ((y : K)⁻¹ • e j) := by
    rw [← algebraMap_smul K r, hr, smul_smul, zsmul_eq_mul, mul_assoc, mul_comm (c _ _),
      ← mul_assoc, mul_inv_cancel₀ hyK, one_mul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end PlaceLattice
end Formalism.HN

namespace Formalism.HN

private theorem place_lattice_structure_lemma {E : Type*} [NormedAddCommGroup E] {A B : Submodule ℤ E}
    (h : A ≤ B) [Module.Finite ℤ B] : Module.finrank ℤ A ≤ Module.finrank ℤ B :=
  LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion h) (Submodule.inclusion_injective h)

private theorem place_lattice_structure_lemma_2 {R : Type*} [Ring R] {V : Type*} [AddCommGroup V] [Module R V]
    {E : Type*} [NormedAddCommGroup E] (ρ : V →+ E) {N₁ N₂ : Submodule R V} (h : N₁ ≤ N₂) :
    zl ρ N₁ ≤ zl ρ N₂ := by
  intro x hx
  change x ∈ AddSubgroup.map ρ N₁.toAddSubgroup at hx
  change x ∈ AddSubgroup.map ρ N₂.toAddSubgroup
  obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.mp hx
  exact AddSubgroup.mem_map.mpr ⟨a, h ha, rfl⟩

open PlaceLattice in
theorem place_lattice_structure : PlLat := by
  intro K V ι _ _ _ _ _ _ _ _ _ b X hX L hL
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  have hinj : Function.Injective ρ := realize_injective b X hX
  obtain ⟨y, hy0, hyL⟩ := exists_denom (K := K) (⇑b) L hL (fun x _ => by rw [b.span_eq]; trivial)
  have hyK : ((y : K))⁻¹ ≠ 0 := inv_ne_zero (Int.cast_ne_zero.mpr hy0)
  have hdM : DiscreteTopology (zl ρ (Submodule.span (𝓞 K) (Set.range fun a => ((y : K))⁻¹ • b a))) := by
    rw [zl_span_eq]
    exact discrete_span_of_linIndep (linIndep_real b X hX _ hyK)
  have hdL : DiscreteTopology (zl ρ L) :=
    DiscreteTopology.of_continuous_injective (continuous_inclusion (place_lattice_structure_lemma_2 ρ hyL))
      (Set.inclusion_injective (place_lattice_structure_lemma_2 ρ hyL))
  refine ⟨⟨hinj.injOn, hdL⟩, ?_, ?_⟩
  · obtain ⟨t, htL, hspan, hli⟩ := exists_linearIndependent K (L : Set V)
    haveI : Module.Finite K V := Module.Finite.of_basis b
    have htf : t.Finite := hli.setFinite
    haveI : Fintype t := htf.fintype
    have hcard : rkK L = Fintype.card t := by
      have hc := finrank_span_eq_card hli
      rw [Subtype.range_coe] at hc
      unfold rkK
      rw [← hspan]
      exact hc
    have hsub : ∀ x ∈ L, x ∈ Submodule.span K (Set.range ((↑) : t → V)) := by
      intro x hx
      rw [Subtype.range_coe, hspan]
      exact Submodule.subset_span hx
    obtain ⟨z, hz0, hzL⟩ := exists_denom (K := K) ((↑) : t → V) L hL hsub
    have hzK : ((z : K))⁻¹ ≠ 0 := inv_ne_zero (Int.cast_ne_zero.mpr hz0)
    have hli' : LinearIndependent K (fun a : t => ((z : K))⁻¹ • (a : V)) :=
      hli.units_smul (fun _ => Units.mk0 _ hzK)
    have hlow : Submodule.span (𝓞 K) (Set.range ((↑) : t → V)) ≤ L := by
      rw [Submodule.span_le, Subtype.range_coe]
      exact htL
    have h1 : rk ρ (Submodule.span (𝓞 K) (Set.range ((↑) : t → V))) = Module.finrank ℚ K * Fintype.card t :=
      (rk_span_eq ρ hinj _ hli).trans (congrArg _ (Fintype.card_congr (Equiv.refl _)))
    have h2 : rk ρ (Submodule.span (𝓞 K) (Set.range fun a : t => ((z : K))⁻¹ • (a : V))) =
        Module.finrank ℚ K * Fintype.card t :=
      (rk_span_eq ρ hinj _ hli').trans (congrArg _ (Fintype.card_congr (Equiv.refl _)))
    haveI : Module.Finite ℤ (zl ρ (Submodule.span (𝓞 K) (Set.range fun a : t => ((z : K))⁻¹ • (a : V)))) := by
      rw [zl_span_eq]
      exact Module.Finite.span_of_finite ℤ (Set.finite_range _)
    haveI : Module.Finite ℤ (zl ρ L) :=
      Module.Finite.of_injective (Submodule.inclusion (place_lattice_structure_lemma_2 ρ hzL))
        (Submodule.inclusion_injective _)
    have hA : Module.finrank ℤ (zl ρ (Submodule.span (𝓞 K) (Set.range ((↑) : t → V)))) ≤
        Module.finrank ℤ (zl ρ L) := place_lattice_structure_lemma (place_lattice_structure_lemma_2 ρ hlow)
    have hB : Module.finrank ℤ (zl ρ L) ≤
        Module.finrank ℤ (zl ρ (Submodule.span (𝓞 K) (Set.range fun a : t => ((z : K))⁻¹ • (a : V)))) :=
      place_lattice_structure_lemma (place_lattice_structure_lemma_2 ρ hzL)
    rw [hcard]
    exact le_antisymm (hB.trans h2.le) (h1.symm.le.trans hA)
  · unfold ht
    haveI := hdL
    have hd : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
    exact mul_pos (mul_pos (pow_pos two_pos _) (Real.rpow_pos_of_pos hd _)) (F.covol_pos _)

end Formalism.HN
