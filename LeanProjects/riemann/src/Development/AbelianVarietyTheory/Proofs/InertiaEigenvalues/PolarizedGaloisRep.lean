import Mathlib
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DeterminantInTorus
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseChangeInertUnramified
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsComplDescCompl

noncomputable section

namespace GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.DeterminantInTorus
open scoped Pointwise Matrix

theorem exists_conj_integral {O K Γ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Group Γ] (n : ℕ) (r : Γ →* GL (Fin n) K) (U : Subgroup Γ)
    [U.FiniteIndex]
    (hU : ∀ h ∈ U, ∀ i j, (r h : Matrix (Fin n) (Fin n) K) i j ∈ (algebraMap O K).range) :
    ∃ P : GL (Fin n) K, ∀ g i j,
      ((P * r g * P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ (algebraMap O K).range := by
  classical
  let col : Γ → Fin n → (Fin n → K) := fun g j i => (r g : Matrix (Fin n) (Fin n) K) i j
  have hcol : ∀ g h j, col (g * h) j = (r g : Matrix (Fin n) (Fin n) K) *ᵥ col h j := by
    intro g h j
    funext i
    simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  let Λ : Submodule O (Fin n → K) := Submodule.span O (Set.range fun p : Γ × Fin n => col p.1 p.2)
  have hst : ∀ g, ∀ v ∈ Λ, (r g : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ Λ := by
    intro g v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact Submodule.subset_span ⟨(g * p.1, p.2), hcol _ _ _⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Λ.add_mem hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Λ.smul_mem a hx
  have hfg : Λ.FG := by
    have : Λ = Submodule.span O (Set.range fun p : (Γ ⧸ U) × Fin n => col p.1.out p.2) := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨⟨g, j⟩, rfl⟩
        obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U g
        have hg : g = (QuotientGroup.mk g : Γ ⧸ U).out * (h⁻¹ : U) := by rw [hh]; simp
        choose c hc using hU _ (h⁻¹).2
        have : col g j = ∑ k, c k j • col (QuotientGroup.mk g : Γ ⧸ U).out k := by
          conv_lhs => rw [hg, hcol]
          funext i
          simp only [col, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]
          exact Finset.sum_congr rfl fun k _ => by rw [Algebra.smul_def, hc, mul_comm]
        show col g j ∈ _
        rw [this]
        exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(_, k), rfl⟩)
      · exact Submodule.span_mono (by rintro _ ⟨p, rfl⟩; exact ⟨(p.1.out, p.2), rfl⟩)
    rw [this]
    exact Submodule.fg_span (Set.finite_range _)
  have htop : Submodule.span K (Λ : Set (Fin n → K)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun K (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨(1, j), ?_⟩
    funext i
    simp [col, Matrix.one_apply, Pi.single_apply]
  haveI : Λ.IsLattice K := ⟨hfg, htop⟩
  haveI : Module.Free O Λ := Submodule.IsLattice.free K Λ
  haveI : Module.Finite O Λ := Module.Finite.iff_fg.2 hfg
  have hrk : Module.finrank O Λ = n := by
    rw [Submodule.IsLattice.finrank_of_pi K Λ, Fintype.card_fin]
  let b : Module.Basis (Fin n) O Λ := Module.finBasisOfFinrankEq O Λ hrk
  let B := b.extendOfIsLattice K
  let e := Pi.basisFun K (Fin n)
  let P : GL (Fin n) K := ⟨B.toMatrix e, e.toMatrix B, by simp, by simp⟩
  refine ⟨P, fun g i j => ?_⟩
  have hB : ∀ j, B j = b j := fun j => b.extendOfIsLattice_apply K j
  have h1 : ((P * r g * P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      LinearMap.toMatrix B B (Matrix.toLin' (r g : Matrix (Fin n) (Fin n) K)) := by
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix B e B e]
    simp [P, e]
  rw [h1, LinearMap.toMatrix_apply, Matrix.toLin'_apply, hB]
  set v : Λ := ⟨_, hst g _ (b j).2⟩ with hv
  refine ⟨b.repr v i, ?_⟩
  have h2 : (v : Fin n → K) = ∑ k, algebraMap O K (b.repr v k) • B k := by
    have h3 := congrArg Λ.subtype (b.sum_repr v)
    rw [map_sum] at h3
    refine h3.symm.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [hB, algebraMap_smul]
    rfl
  show _ = B.repr (v : Fin n → K) i
  rw [h2, B.repr_sum_self]

theorem isSSRep_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {ρ ρ' : Γ →* GL (Fin n) k} (h : GL (Fin n) k)
    (hh : ∀ g, ρ' g = h * ρ g * h⁻¹) (hρ : IsSSRep ρ) : IsSSRep ρ' := by
  let e : (Fin n → k) ≃ₗ[k] (Fin n → k) := Matrix.toLin'OfInv (M := (h : Matrix (Fin n) (Fin n) k))
    (M' := ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (by simp) (by simp)
  have he : ∀ v, e v = ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ v := fun v => rfl
  have key : ∀ g v, e ((ρ' g : Matrix (Fin n) (Fin n) k) *ᵥ v) = (ρ g : Matrix (Fin n) (Fin n) k) *ᵥ e v := by
    intro g v
    rw [he, he, hh, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  intro W hW
  obtain ⟨W', hW', hc⟩ := hρ (W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))) (by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨_, hW g v hv, key g v⟩)
  refine ⟨W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k)), fun g v hv => ?_, ?_⟩
  · show e _ ∈ W'
    rw [key]
    exact hW' g _ hv
  · have := (Submodule.orderIsoMapComap e).symm.isCompl hc
    have h2 : IsCompl ((W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))).comap (e : (Fin n → k) →ₗ[k] (Fin n → k)))
      (W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))) := this
    rwa [Submodule.comap_map_eq_of_injective e.injective] at h2

theorem isSSRep_of_mapRep {Γ k k' : Type} [Group Γ] [Field k] [Field k'] {n : ℕ} (ι : k →+* k')
    (ρ : Γ →* GL (Fin n) k) (hρ : IsSSRep (mapRep ι ρ)) : IsSSRep ρ :=
  _root_.GlobalTheory.RetractionComplement.isSSRep_of_mapRep ι ρ hρ

section Topology

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (φ : O →+* Qbar l)
  (hφ : ∀ z : ℤ_[l], φ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))

include hφ

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem norm_le_one (x : O) : ‖φ x‖ ≤ 1 := by
  obtain ⟨p, hp, hx⟩ : IsIntegral ℤ_[l] x := Algebra.IsIntegral.isIntegral x
  by_contra hlt
  push Not at hlt
  have h0 : (φ x) ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree,
      algebraMap ℚ_[l] (Qbar l) (p.coeff i : ℚ_[l]) * φ x ^ i = 0 := by
    have := congrArg φ hx
    rw [hp.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_finset_sum] at this
    simpa [hφ] using this
  have hpos : 0 < p.natDegree := by
    by_contra h
    have h' : p.natDegree = 0 := by omega
    simp [h'] at h0
  have h1 : ‖∑ i ∈ Finset.range p.natDegree, algebraMap ℚ_[l] (Qbar l) (p.coeff i : ℚ_[l]) * φ x ^ i‖ ≤
      ‖φ x‖ ^ (p.natDegree - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow, norm_algebraMap']
    calc _ ≤ 1 * ‖φ x‖ ^ i := by gcongr; exact (p.coeff i).2
      _ ≤ _ := by
        rw [one_mul]
        exact pow_le_pow_right₀ hlt.le (by have := Finset.mem_range.1 hi; omega)
  rw [← eq_neg_iff_add_eq_zero] at h0
  rw [← norm_neg, ← h0, norm_pow] at h1
  exact absurd h1 (not_le.2 (pow_lt_pow_right₀ hlt (by omega)))

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem norm_unit (u : Oˣ) : ‖φ u‖ = 1 := by
  have h1 := norm_le_one φ hφ u
  have h2 := norm_le_one φ hφ ↑u⁻¹
  have h3 : ‖φ u‖ * ‖φ ↑u⁻¹‖ = 1 := by rw [← norm_mul, ← map_mul]; simp
  nlinarith [norm_nonneg (φ u), norm_nonneg (φ ↑u⁻¹)]

theorem norm_lt_one {ϖ : O} (hϖ : Irreducible ϖ) : ‖φ ϖ‖ < 1 := by
  have hl : ‖φ (l : O)‖ < 1 := by
    have := hφ (l : ℤ_[l])
    rw [map_natCast] at this
    rw [this, norm_algebraMap']
    exact_mod_cast (PadicInt.norm_lt_one_iff_dvd (l : ℤ_[l])).2 dvd_rfl
  have hl0 : (l : O) ≠ 0 := by
    intro h
    have : φ (l : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at this
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  rw [hu, map_mul, norm_mul, norm_unit φ hφ, one_mul, map_pow, norm_pow] at hl
  by_contra h
  exact absurd hl (not_lt.2 (one_le_pow₀ (not_lt.1 h)))

theorem mem_pow_iff (hinj : Function.Injective φ) {ϖ : O} (hϖ : Irreducible ϖ) (k : ℕ) (x : O) :
    x ∈ IsLocalRing.maximalIdeal O ^ k ↔ ‖φ x‖ ≤ ‖φ ϖ‖ ^ k := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have h0 : 0 < ‖φ ϖ‖ := norm_pos_iff.2 ((map_ne_zero_iff φ hinj).2 hϖ.ne_zero)
  constructor
  · rintro ⟨y, rfl⟩
    rw [map_mul, norm_mul, map_pow, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (norm_le_one φ hφ y)
  · intro h
    by_cases hx : x = 0
    · simp [hx]
    obtain ⟨j, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    rw [map_mul, norm_mul, norm_unit φ hφ, one_mul, map_pow, norm_pow,
      pow_le_pow_iff_right_of_lt_one₀ h0 (norm_lt_one φ hφ hϖ)] at h
    exact Dvd.dvd.mul_left (pow_dvd_pow _ h) _

theorem isInducing [TopologicalSpace O] [IsTopologicalRing O] (had : IsAdic (IsLocalRing.maximalIdeal O))
    (hinj : Function.Injective φ) : Topology.IsInducing φ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h0 : 0 < ‖φ ϖ‖ := norm_pos_iff.2 ((map_ne_zero_iff φ hinj).2 hϖ.ne_zero)
  have h1 := norm_lt_one φ hφ hϖ
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  refine had.hasBasis_nhds_zero.eq_of_same_basis ?_
  have hb : (nhds (0 : Qbar l)).HasBasis (fun _ : ℕ => True) (fun k => Metric.closedBall 0 (‖φ ϖ‖ ^ k)) :=
    Metric.nhds_basis_closedBall_pow h0 h1
  convert hb.comap φ using 2 with k
  ext x
  simp [mem_pow_iff φ hφ hinj hϖ]

end Topology

theorem mem_range_iff {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Field K] [Algebra O K] [IsFractionRing O K] (ι : K →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O K (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (x : K) : x ∈ (algebraMap O K).range ↔ ‖ι x‖ ≤ 1 := by
  let φ := ι.comp (algebraMap O K)
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨y, rfl⟩
    exact norm_le_one φ hι y
  obtain ⟨y, hy | hy⟩ := ValuationRing.isInteger_or_isInteger O x |>.elim
    (fun ⟨y, hy⟩ => (⟨y, Or.inl hy⟩ : ∃ y : O, algebraMap O K y = x ∨ algebraMap O K y = x⁻¹))
    (fun ⟨y, hy⟩ => ⟨y, Or.inr hy⟩)
  · exact ⟨y, hy⟩
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hx (by simpa using hy.symm)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨j, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have h1 : ‖φ y‖ = ‖ι x‖⁻¹ := by
    show ‖ι (algebraMap O K y)‖ = _
    rw [hy, map_inv₀, norm_inv]
  have h2 : 1 ≤ ‖φ y‖ := by
    rw [h1]
    exact (one_le_inv₀ (norm_pos_iff.2 ((map_ne_zero ι).2 hx))).2 h
  rw [hu, map_mul, norm_mul, norm_unit φ hι, one_mul, map_pow, norm_pow] at h2
  have hj : j = 0 := by
    by_contra hj
    exact absurd h2 (not_le.2 (pow_lt_one₀ (norm_nonneg _) (norm_lt_one φ hι hϖ) hj))
  rw [hj, pow_zero, mul_one] at hu
  refine ⟨↑u⁻¹, ?_⟩
  rw [← inv_inv x, ← hy, hu]
  simp

theorem isClosed_submodule {O X : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [Fintype X]
    [TopologicalSpace O] [IsTopologicalRing O] (had : IsAdic (IsLocalRing.maximalIdeal O))
    (T : Submodule O (X → O)) : IsClosed (T : Set (X → O)) := by
  classical
  refine isClosed_of_closure_subset fun f hf => ?_
  have key := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := (X → O) ⧸ T) (IsLocalRing.maximalIdeal O)
    (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  show f ∈ T
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mem_bot O, ← key, Submodule.mem_iInf]
  intro k
  have ho : IsOpen {t : X → O | ∀ x, f x - t x ∈ IsLocalRing.maximalIdeal O ^ k} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun x =>
      (((isAdic_iff.1 had).1 k).preimage (by fun_prop : Continuous fun t : X → O => f x - t x))
  obtain ⟨t, ht, htT⟩ := mem_closure_iff.1 hf _ ho (by simp)
  have h1 : (Submodule.Quotient.mk f : (X → O) ⧸ T) = T.mkQ (f - t) := by
    rw [map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero T).2 htT, sub_zero]
  rw [h1, pi_eq_sum_univ (f - t), map_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem_smul (ht x) Submodule.mem_top

theorem isSplitPl_of_degree_one {R : Ranks} (H : Host R) (v : PlE H) (hf : v.asIdeal.inertiaDeg ℤ = 1)
    (he : v.asIdeal.ramificationIdx ℤ = 1) : IsSplitPl H v := by
  have hG : IsGalois ℚ H.E := H.hostE_isGalois
  have := v.isPrime
  have := v.isMaximal
  have h3 := Ideal.card_stabilizer_eq (G := H.E ≃ₐ[ℚ] H.E) (v.asIdeal.under ℤ) v.asIdeal
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ v.asIdeal (H.E ≃ₐ[ℚ] H.E),
    Ideal.inertiaDegIn_eq_inertiaDeg _ v.asIdeal (H.E ≃ₐ[ℚ] H.E), he, hf] at h3
  have hbot : MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) v.asIdeal = ⊥ := Subgroup.card_eq_one.1 h3
  by_contra hn
  unfold IsSplitPl at hn
  push Not at hn
  have hle : H.conj • v.asIdeal ≤ v.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hz, hzv⟩ := hn _ hy
    have e : z = y := RingOfIntegers.ext (hz.trans (H.conj.apply_symm_apply (y : H.E)))
    exact e ▸ hzv
  have hmax : (H.conj • v.asIdeal).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => v.ne_bot ?_
    rw [← inv_smul_smul H.conj v.asIdeal, h0, Ideal.smul_bot]
  have heq : H.conj • v.asIdeal = v.asIdeal := hmax.eq_of_le v.isPrime.ne_top hle
  have h1 : H.conj = 1 := Subgroup.mem_bot.1 (hbot ▸ heq)
  have hsq := H.sqrtMinusD_sq
  have hc := H.conj_sqrtMinusD
  rw [h1, AlgEquiv.one_apply] at hc
  have h0 : H.sqrtMinusD = 0 := by linear_combination (1 / 2 : H.E) * hc
  rw [h0] at hsq
  have h4 : (H.d : H.E) = 0 := by linear_combination hsq
  have h5 : H.d = 0 := by exact_mod_cast h4
  have := H.qd_big.2
  omega

def frobSet (D : D7) (i : D.nd.Loc) : Set (GE D.nd) :=
  {σ | ∃ w, SplitOut D.nd i w ∧ ∃ B : ValuationSubring D.nd.Om,
    IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ}

theorem isSSRep_of_prod {Γ k : Type} [Group Γ] [Field k] {n a b : ℕ} {ρ : Γ →* GL (Fin n) k}
    {ρ₁ : Γ →* GL (Fin a) k} {ρ₂ : Γ →* GL (Fin b) k} (e : (Fin n → k) ≃ₗ[k] (Fin a → k) × (Fin b → k))
    (he : ∀ g v, e ((ρ g : Matrix (Fin n) (Fin n) k) *ᵥ v) =
      ((ρ₁ g : Matrix (Fin a) (Fin a) k) *ᵥ (e v).1, (ρ₂ g : Matrix (Fin b) (Fin b) k) *ᵥ (e v).2))
    (h₁ : IsSSRep ρ₁) (h₂ : IsSSRep ρ₂) : IsSSRep ρ := by
  intro W hW
  let W₁ : Submodule k (Fin a → k) := W.comap (e.symm.toLinearMap ∘ₗ LinearMap.inl k _ _)
  let W₂ : Submodule k (Fin b → k) := W.map (LinearMap.snd k _ _ ∘ₗ e.toLinearMap)
  obtain ⟨C₁, hC₁, hc₁⟩ := h₁ W₁ fun g v hv => by
    have h := hW g _ hv
    show e.symm (_, 0) ∈ W
    convert h using 1
    rw [LinearEquiv.symm_apply_eq, he]
    simp
  obtain ⟨C₂, hC₂, hc₂⟩ := h₂ W₂ (by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨_, hW g v hv, congrArg Prod.snd (he g v)⟩)
  refine ⟨(C₁.prod C₂).comap e.toLinearMap, fun g v hv => ?_, ?_, ?_⟩
  · show e _ ∈ C₁.prod C₂
    rw [he]
    exact ⟨hC₁ g _ hv.1, hC₂ g _ hv.2⟩
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    have h2 : (e v).2 = 0 := Submodule.disjoint_def.1 hc₂.disjoint _ ⟨v, hv, rfl⟩ hv'.2
    have h3 : e.symm ((e v).1, 0) = v := by rw [← h2]; simp
    have h1 : (e v).1 = 0 := Submodule.disjoint_def.1 hc₁.disjoint _
      (show e.symm ((e v).1, 0) ∈ W by rwa [h3]) hv'.1
    rw [← h3, h1]
    exact map_zero e.symm
  · rw [codisjoint_iff, eq_top_iff]
    rintro v -
    obtain ⟨_, ⟨w, hw, rfl⟩, c₂, hc, h2⟩ := Submodule.mem_sup.1
      (show (e v).2 ∈ W₂ ⊔ C₂ by rw [hc₂.sup_eq_top]; trivial)
    obtain ⟨w₁, hw₁, c₁, hc', h1⟩ := Submodule.mem_sup.1
      (show (e v).1 - (e w).1 ∈ W₁ ⊔ C₁ by rw [hc₁.sup_eq_top]; trivial)
    refine Submodule.mem_sup.2 ⟨w + e.symm (w₁, 0), W.add_mem hw hw₁, e.symm (c₁, c₂), ?_, ?_⟩
    · show e (e.symm _) ∈ C₁.prod C₂
      rw [e.apply_symm_apply]
      exact ⟨hc', hc⟩
    · apply e.injective
      have h2' : (e w).2 + c₂ = (e v).2 := h2
      ext1
      · simp only [map_add, e.apply_symm_apply, Prod.fst_add]
        rw [add_assoc, h1]; abel
      · simp only [map_add, e.apply_symm_apply, Prod.snd_add]
        rw [add_zero, h2']

theorem exists_sum_rep {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [Field k] [TopologicalSpace k] {a b : ℕ}
    (ρ₁ : Γ →* GL (Fin a) k) (ρ₂ : Γ →* GL (Fin b) k)
    (c₁ : Continuous fun g => (ρ₁ g : Matrix (Fin a) (Fin a) k))
    (c₂ : Continuous fun g => (ρ₂ g : Matrix (Fin b) (Fin b) k)) (h₁ : IsSSRep ρ₁) (h₂ : IsSSRep ρ₂) :
    ∃ ρ : Γ →* GL (Fin (a + b)) k, (Continuous fun g => (ρ g : Matrix (Fin (a + b)) (Fin (a + b)) k)) ∧
      IsSSRep ρ ∧ ∀ g, (ρ g : Matrix (Fin (a + b)) (Fin (a + b)) k).charpoly =
        (ρ₁ g : Matrix (Fin a) (Fin a) k).charpoly * (ρ₂ g : Matrix (Fin b) (Fin b) k).charpoly := by
  let m : Γ →* Matrix (Fin (a + b)) (Fin (a + b)) k :=
    { toFun := fun g => Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ₁ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ₂ g : Matrix (Fin b) (Fin b) k))
      map_one' := by simp
      map_mul' := fun g g' => by simp [Matrix.fromBlocks_multiply] }
  have hm : ∀ g, (m.toHomUnits g : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ₁ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ₂ g : Matrix (Fin b) (Fin b) k)) :=
    fun g => rfl
  refine ⟨m.toHomUnits, ?_, ?_, fun g => ?_⟩
  · simp only [hm]
    exact (c₁.matrix_fromBlocks continuous_const continuous_const c₂).matrix_reindex _ _
  · refine isSSRep_of_prod ((LinearEquiv.funCongrLeft k k finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) h₁ h₂
    rw [hm]
    ext i <;>
      simp [Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft] <;> rfl
  · rw [hm, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₂₁]

section Construction

variable (D : D7)

def GaloisRepOfPolarized_at : Prop :=
  ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → ∀ s : ℝ,
    (∀ τ, (D.naut.infG π τ).Nodup ∧
      ∀ z ∈ D.naut.infG π τ, ∃ m : ℤ, z + (s : ℂ) = (m : ℂ) + ((a : ℂ) - 1) / 2) →
    ∃ r : GE D.nd →* GL (Fin a) (Qbar (D.nd.l i)),
      Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i)))) ∧ IsSSRep r ∧
      ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
        D.naut.wdOf i r w = D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2)

variable (i : D.nd.Loc)

def Realised (m : ℕ) (L : ∀ w, D.naut.LP w) : Prop :=
  ∃ r : GE D.nd →* GL (Fin m) (Qbar (D.nd.l i)),
    Continuous (fun g => (r g : Matrix (Fin m) (Fin m) (Qbar (D.nd.l i)))) ∧ IsSSRep r ∧
    ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.unr (L w) →
      ∀ (B : ValuationSubring D.nd.Om) (σ : GE D.nd), IsPlaceOver (F := D.host.E) B w →
        IsFrob (F := D.host.E) B (normV w) σ →
        (r σ : Matrix (Fin m) (Fin m) (Qbar (D.nd.l i))).charpoly.map (D.naut.iotaQC i).toRingHom =
          galPol D.naut (D.naut.lpTw (L w) ((1 - (D.R.nV : ℝ)) / 2))

variable {D i}

theorem Realised.sum {m m' : ℕ} {L L' : ∀ w, D.naut.LP w} (h : Realised D i m L) (h' : Realised D i m' L') :
    Realised D i (m + m') fun w => D.naut.lpSum (L w) (L' w) := by
  obtain ⟨r, c, s, f⟩ := h
  obtain ⟨r', c', s', f'⟩ := h'
  obtain ⟨ρ, cρ, sρ, hρ⟩ := exists_sum_rep r r' c c' s s'
  refine ⟨ρ, cρ, sρ, fun w hw hu B σ hB hσ => ?_⟩
  obtain ⟨u, u'⟩ := (D.naut.unr_sum _ _).1 hu
  rw [hρ, Polynomial.map_mul, f w hw u B σ hB hσ, f' w hw u' B σ hB hσ, galPol, galPol, galPol,
    D.naut.lpTw_sum, D.naut.frobEig_sum _ _ ((D.naut.unr_tw _ _).2 u) ((D.naut.unr_tw _ _).2 u'),
    Multiset.map_add, Multiset.prod_add]

end Construction

def GaloisRepOfPolarizedF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x : ℝ, Fm.x1 < x → ∀ p : Fm.Ix x, GaloisRepOfPolarized_at (Fm.D x p)

def GaloisRepOfPolarized (C : FamClass) : Prop :=
  Closed C (fun Fm _ => GaloisRepOfPolarizedF Fm)

end GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate

end
