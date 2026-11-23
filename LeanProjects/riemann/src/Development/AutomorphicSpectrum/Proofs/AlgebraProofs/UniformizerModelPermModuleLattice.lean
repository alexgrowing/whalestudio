import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChernClassOnFlagPairStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.CkRelations

noncomputable def allOne (q : ℕ) : Fin q →₀ ℕ := ∑ j, Finsupp.single j 1

theorem toMultiset_allOne (q : ℕ) : (allOne q).toMultiset = Finset.univ.val := by
  ext j
  simp [allOne, Finsupp.count_toMultiset, Finsupp.finset_sum_apply, Finsupp.single_apply]

theorem degree_allOne (q : ℕ) : (allOne q).degree = q := by
  simp [allOne, map_sum]

theorem isHomogeneous_allOne (q n : ℕ) (h : q = n) :
    (monomial (allOne q) (1 : ℤ) : MvPolynomial (Fin q) ℤ).IsHomogeneous n :=
  isHomogeneous_monomial _ ((degree_allOne q).trans h)

theorem classList_allOne {K : Type} (Q : List (K → ℤ)) :
    (classList Q.get (allOne Q.length)).Perm Q := by
  rw [← Multiset.coe_eq_coe, classList, Multiset.coe_toList, toMultiset_allOne, Fin.univ_val_map,
    List.ofFn_get]

theorem sum_allOne (q : ℕ) (F : (Fin q →₀ ℕ) → ℤ) :
    ∑ μ ∈ (monomial (allOne q) (1 : ℤ) : MvPolynomial (Fin q) ℤ).support,
      (monomial (allOne q) (1 : ℤ) : MvPolynomial (Fin q) ℤ).coeff μ * F μ = F (allOne q) := by
  classical
  rw [support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl, one_mul]

theorem classNum_perm {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ : Type} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ)
    {Q Q' : List (K → ℤ)} (h : Q.Perm Q') (W : Ideal (MRing ι O)) :
    classNum cls H Q W = classNum cls H Q' W := by
  unfold classNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  have : LeftCommutative (diffStep (K := K)) := ⟨fun a b f => by
    funext m
    simp only [diffStep]
    rw [sub_right_comm m a b]
    ring⟩
  simp only [vNumL, vNum, intNum, mixedDiff, List.ofFn_get]
  rw [(h.append_left _).foldr_eq]

theorem key (hC : GroundTheory.Heights₂.Heights.NumbersDVR.ChernClassOnFlagPair.Statement) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (ϖ : O) (hϖ : Irreducible ϖ) (d : ℕ)
    (hM : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d)
    (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V)
    (hE : SameGeneric O x E E') (T : LocPair ι O (Fin N)) (b b' : Module.Basis (Fin N) Ω V)
    (hT : IsFlagPair ϖ x E E' b b' T.x T.x' T.f T.g) (k : ℕ) (hk : 1 ≤ k) (Q : List (K → ℤ))
    (hQ : Q.length + k = d + 1) :
    ck O x d N E E' k Q.get (monomial (allOne Q.length) 1) = T.ck (pointIdeal O x) k Q ∧
    ∀ a : O, a ≠ 0 →
      (k : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) Q.get (monomial (allOne Q.length) 1) a =
        laNum (pointIdeal O x) a T.x k Q := by
  obtain ⟨hK, hW⟩ := (BundleExamples.isModelOver_iff O _ d).mp hM
  obtain ⟨h1, h2⟩ := hC O ϖ hϖ Ω K ι x d hK hW N V E E'
    ((BundleExamples.sameGeneric_iff hϖ x E E').mp hE) b b' T.x T.x' T.f T.g hT
  refine ⟨?_, fun a ha => ?_⟩
  · refine (h1 k hk (by omega) _ (isPairExpansion_psum N k) _ Q.get _
      (isHomogeneous_allOne _ _ (by omega))).trans ?_
    rw [sum_allOne Q.length
      (fun μ => pairNum (pointIdeal O x) T.x T.x' T.f T.g (psumExpansion N k) (classList Q.get μ))]
    simp only [LocPair.ck, pairNum, classNum_perm _ _ (classList_allOne Q)]
  · have h3 := h2 (k - 1) _ (psum_isSymmetric _ _ (k - 1)) (isHomogeneous_psum N (k - 1)) (by omega)
      _ Q.get _ (isHomogeneous_allOne _ _ (by omega)) a ha
    rw [sum_allOne Q.length
      (fun μ => cycEval (fun W => classNum T.x (psum (Fin N) ℤ (k - 1)) (classList Q.get μ) W)
        (divCycle (pointIdeal O x) (C a)))] at h3
    simp only [classNum_perm _ _ (classList_allOne Q)] at h3
    unfold laNum
    exact congrArg _ h3

theorem main_of (hC : GroundTheory.Heights₂.Heights.NumbersDVR.ChernClassOnFlagPair.Statement) : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {Sg : Type} {r s : Sg → ℕ} (p : ℕ), (p : O) ≠ 0 → ∀ (φ : Equiv.Perm Sg) {VL VO : Sg → Type} [∀ τ, AddCommGroup (VL τ)] [∀ τ, Module Ω (VL τ)] [∀ τ, AddCommGroup (VO τ)] [∀ τ, Module Ω (VO τ)] (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (VL τ)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (VO τ)), (∀ τ, SameGeneric O x (Lie τ) (W τ) ∧ SameGeneric O x (Om τ) (OmHT τ)) → CkRelations O x d p φ Lie W Om OmHT → ∀ (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, (∃ b b' : Module.Basis (Fin (r τ)) Ω (VL τ), IsFlagPair ϖ x (Lie τ) (W τ) b b' (lie τ).x (lie τ).x' (lie τ).f (lie τ).g) ∧ ∃ b b' : Module.Basis (Fin (s τ)) Ω (VO τ), IsFlagPair ϖ x (Om τ) (OmHT τ) b b' (om τ).x (om τ).x' (om τ).f (om τ).g) → Relations (pointIdeal O x) d p φ lie om := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hM Sg r s p hp φ VL VO _ _ _ _ Lie W Om OmHT hS hR lie om hF
    k hk Q hQ
  obtain ⟨h, h1, h2⟩ := hR k hk (by omega) Q.length Q.get _
    (isHomogeneous_allOne _ _ (by omega))
  have hL := fun τ => (hF τ).1.elim fun b hb => hb.elim fun b' hb' =>
    key hC O Ω K ι x ϖ hϖ d hM _ _ _ _ (hS τ).1 (lie τ) b b' hb' k hk Q hQ
  have hO := fun τ => (hF τ).2.elim fun b hb => hb.elim fun b' hb' =>
    key hC O Ω K ι x ϖ hϖ d hM _ _ _ _ (hS τ).2 (om τ) b b' hb' k hk Q hQ
  refine ⟨h, fun τ => ?_, fun τ => ?_⟩
  · rw [← (hL τ).1, ← (hO τ).1, ← (hL τ).2 _ hp, h1 τ]
    push_cast
    ring
  · rw [← (hL (φ τ)).2 _ hp, h2 τ]
    push_cast
    ring

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {Sg : Type} {r s : Sg → ℕ} (p : ℕ), (p : O) ≠ 0 → ∀ (φ : Equiv.Perm Sg) {VL VO : Sg → Type} [∀ τ, AddCommGroup (VL τ)] [∀ τ, Module Ω (VL τ)] [∀ τ, AddCommGroup (VO τ)] [∀ τ, Module Ω (VO τ)] (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (VL τ)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (VO τ)), (∀ τ, SameGeneric O x (Lie τ) (W τ) ∧ SameGeneric O x (Om τ) (OmHT τ)) → CkRelations O x d p φ Lie W Om OmHT → ∀ (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, (∃ b b' : Module.Basis (Fin (r τ)) Ω (VL τ), IsFlagPair ϖ x (Lie τ) (W τ) b b' (lie τ).x (lie τ).x' (lie τ).f (lie τ).g) ∧ ∃ b b' : Module.Basis (Fin (s τ)) Ω (VO τ), IsFlagPair ϖ x (Om τ) (OmHT τ) b b' (om τ).x (om τ).x' (om τ).f (om τ).g) → Relations (pointIdeal O x) d p φ lie om :=
  main_of GlobalTheory.T.chern_class_on_flag_pair

end GlobalTheory.CompanionTheory.CkRelations
