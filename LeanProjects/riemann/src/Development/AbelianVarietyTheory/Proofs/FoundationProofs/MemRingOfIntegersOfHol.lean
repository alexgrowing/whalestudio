import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionHolomorphic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerSlActionRowVector
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelInvariantPrincipalCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionSiegelUnitInTowerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariantStatement

noncomputable section

open scoped MatrixGroups UpperHalfPlane
open Polynomial

namespace GlobalTheory.K4.TopUnits

open GlobalTheory.KZ GlobalTheory.Sieg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def holSub (X : Tower Ω ε) : Subring X.K where
  carrier := {f | ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an f = (φ : Mero)}
  mul_mem' := by
    rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
    exact ⟨φ * ψ, h1.mul h3, by rw [map_mul, h2, h4, Filter.Germ.coe_mul]⟩
  one_mem' := ⟨1, differentiableOn_const 1, by rw [map_one, Filter.Germ.coe_one]⟩
  add_mem' := by
    rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
    exact ⟨φ + ψ, h1.add h3, by rw [map_add, h2, h4, Filter.Germ.coe_add]⟩
  zero_mem' := ⟨0, differentiableOn_const 0, by rw [map_zero, Filter.Germ.coe_zero]⟩
  neg_mem' := by
    rintro f ⟨φ, h1, h2⟩
    exact ⟨-φ, h1.neg, by rw [map_neg, h2, Filter.Germ.coe_neg]⟩

theorem finite_conj (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) {f : X.K} (hf : f ∈ topL X M) :
    (Set.range fun γ : SL(2, ℤ) => X.sl (ofSL γ) f).Finite := by
  haveI : NeZero M := ⟨hM⟩
  haveI : (CongruenceSubgroup.Gamma M).FiniteIndex := by
    show (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))).ker.FiniteIndex
    exact Subgroup.finiteIndex_ker _
  refine (Set.finite_range fun q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M => X.sl (ofSL q.out⁻¹) f).subset ?_
  rintro _ ⟨γ, rfl⟩
  obtain ⟨δ, hδ⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma M) γ⁻¹
  refine ⟨QuotientGroup.mk γ⁻¹, ?_⟩
  show X.sl (ofSL _) f = X.sl (ofSL γ) f
  rw [hδ, mul_inv_rev, inv_inv, map_mul, X.sl_mul, (mem_lev_iff X _ f).1 hf _ (inv_mem δ.2)]

theorem mem_ringOfIntegers_of_hol [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) {f : X.K} (hf : f ∈ topL X M)
    (hh : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) f ∈ holSub X) :
    letI := algPoly X (CongruenceSubgroup.Gamma M)
    (⟨f, hf⟩ : topL X M) ∈ FunctionField.ringOfIntegers Ω (topL X M) := by
  letI := algPoly X (CongruenceSubgroup.Gamma M)
  classical
  set s : Finset X.K := (finite_conj X hM hf).toFinset with hs
  have hmem : ∀ g, g ∈ s ↔ ∃ γ : SL(2, ℤ), X.sl (ofSL γ) f = g := fun g => by simp [hs]
  set P : Polynomial X.K := ∏ g ∈ s, (Polynomial.X - C g) with hP
  have hmon : P.Monic := monic_prod_of_monic _ _ fun g _ => monic_X_sub_C g
  have hhol : ∀ n, P.coeff n ∈ holSub X := by
    have h1 : P ∈ Polynomial.liftsRing (holSub X).subtype := by
      refine Subring.prod_mem _ fun g hg => ?_
      obtain ⟨γ, rfl⟩ := (hmem g).1 hg
      exact ⟨Polynomial.X - C ⟨_, hh γ⟩, by simp⟩
    intro n
    obtain ⟨y, hy⟩ := (Polynomial.lifts_iff_coeff_lifts P).1 ((Polynomial.lifts_iff_liftsRing _ P).2 h1) n
    rw [← hy]
    exact y.2
  have hinv : ∀ (γ : SL(2, ℤ)) n, X.sl (ofSL γ) (P.coeff n) = P.coeff n := by
    intro γ n
    have e : P.map (X.sl (ofSL γ) : X.K →+* X.K) = P := by
      rw [hP, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C]
      refine Finset.prod_nbij (fun g => X.sl (ofSL γ) g) (fun g hg => ?_) (fun a _ b _ h => (X.sl (ofSL γ)).injective h)
        (fun g hg => ?_) (fun g _ => rfl)
      · obtain ⟨δ, rfl⟩ := (hmem g).1 hg
        exact (hmem _).2 ⟨δ * γ, by rw [map_mul, X.sl_mul]⟩
      · obtain ⟨δ, rfl⟩ := (hmem g).1 hg
        refine ⟨X.sl (ofSL (δ * γ⁻¹)) f, (hmem _).2 ⟨_, rfl⟩, ?_⟩
        show X.sl (ofSL γ) _ = _
        rw [← X.sl_mul, ← map_mul, inv_mul_cancel_right]
    have := congrArg (fun Q => Polynomial.coeff Q n) e
    simpa only [Polynomial.coeff_map, RingHom.coe_coe] using this
  let A : (Polynomial Ω) →+* X.K := (Polynomial.aeval X.jK : (Polynomial Ω) →ₐ[Ω] X.K)
  have hl : P ∈ Polynomial.lifts A := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have h := GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant ε X ε.injective (X.j_hol.imp fun _ h => h.symm) _ (fun γ => hinv γ n) (hhol n)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h
    exact h
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hmon
  refine ⟨q, hqm, ?_⟩
  apply (topL X M).subtype.injective
  have eA : (topL X M).subtype.comp (algebraMap (Polynomial Ω) (topL X M)) = A := RingHom.ext fun p => coe_jPoly X _ p
  rw [Polynomial.hom_eval₂, eA, map_zero, ← Polynomial.eval_map, hq, hP, Polynomial.eval_prod]
  refine Finset.prod_eq_zero ((hmem f).2 ⟨1, by rw [map_one, X.sl_one]⟩) ?_
  simp

theorem siegel_hol [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {c : ℕ} {y : Fin 2 → ℚ} (hy : admitted c y) :
    siegel X c y ∈ holSub X ∧ (siegel X c y)⁻¹ ∈ holSub X := by
  have hd : DifferentiableOn ℂ (sgC c y) Hs :=
    UpperHalfPlane.mdifferentiable_iff.1 (GlobalTheory.Sieg.mdifferentiable_sg c y hy)
  have hne : ∀ z, sgC c y z ≠ 0 := fun z => GlobalTheory.Sieg.sg_ne_zero c y _ hy
  have ha := SiegelMem.an_siegel_eq Ω ε X c y hy
  refine ⟨⟨_, hd, ha⟩, (sgC c y)⁻¹, hd.inv fun z _ => hne z, ?_⟩
  have h1 : X.an (siegel X c y)⁻¹ * X.an (siegel X c y) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (GlobalTheory.T.siegelUnitInTower_ne_zero Ω ε X c y hy), map_one]
  have h2 : X.an (siegel X c y) * (((sgC c y)⁻¹ : ℂ → ℂ) : Mero) = 1 := by
    rw [ha, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_one]
    congr 1
    funext z
    exact mul_inv_cancel₀ (hne z)
  rw [← mul_one (X.an _), ← h2, ← mul_assoc, h1, one_mul]

def IsTopUnit (X : Tower Ω ε) (M : ℕ) (f : X.K) : Prop :=
  f ≠ 0 ∧ f ∈ topF X M ∧ ∃ hf : f ∈ topL X M,
    letI := algPoly X (CongruenceSubgroup.Gamma M)
    (⟨f, hf⟩ : topL X M) ∈ FunctionField.ringOfIntegers Ω (topL X M) ∧
      (⟨f, hf⟩ : topL X M)⁻¹ ∈ FunctionField.ringOfIntegers Ω (topL X M)

theorem isTopUnit_siegel [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {c M a b : ℕ} (ha : a < M)
    (hy : admitted c ![(a : ℚ) / M, (b : ℚ) / M]) : IsTopUnit X M (siegel X c ![(a : ℚ) / M, (b : ℚ) / M]) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le a) ha
  have hL : siegel X c ![(a : ℚ) / M, (b : ℚ) / M] ∈ topL X M :=
    (mem_lev_iff X _ _).2 (GlobalTheory.T.siegel_invariant_principal_congruence Ω ε X c _ M hy hM ⟨a, b, by simp, by simp⟩)
  have hconj : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) (siegel X c ![(a : ℚ) / M, (b : ℚ) / M]) = _ :=
    fun γ => SiegelSL.sl_siegel Ω ε X c _ γ hy
  refine ⟨GlobalTheory.T.siegelUnitInTower_ne_zero Ω ε X c _ hy, (mem_mdl_iff X _ _ _).2 ⟨hL, fun s hs => ?_⟩, hL, ?_, ?_⟩
  · have h := GlobalTheory.T.galois_action_siegelUnitInTower Ω ε X c M a b 1 s hM ha
      (by rw [Nat.cast_one]; exact (mem_fixMu_iff s).1 hs _ (isPrimitiveRoot_eOm ε hM.ne').pow_eq_one) hy
      (by rw [one_mul]; exact hy)
    rwa [one_mul] at h
  · exact mem_ringOfIntegers_of_hol X hM.ne' hL fun γ => by
      rw [hconj]; exact (siegel_hol X (SiegelMem.admissible_act_SL2 hy γ)).1
  · exact mem_ringOfIntegers_of_hol X hM.ne' (inv_mem hL) fun γ => by
      rw [map_inv₀, hconj]; exact (siegel_hol X (SiegelMem.admissible_act_SL2 hy γ)).2

theorem not_int {l c a M : ℕ} (hl : l.Prime) (hM : M ≠ 0) (hlM : l ∣ M) (hc : ¬ l ∣ c) (ha : ¬ l ∣ a) :
    (c : ℚ) * ((a : ℚ) / M) ∉ Set.range ((↑) : ℤ → ℚ) := by
  rintro ⟨m, hm⟩
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have e : ((c * a : ℕ) : ℤ) = (M : ℤ) * m := by
    have : ((c * a : ℕ) : ℚ) = (M : ℚ) * m := by rw [hm]; push_cast; field_simp
    exact_mod_cast this
  have h : l ∣ c * a := hlM.trans (Int.natCast_dvd_natCast.1 ⟨m, e⟩)
  exact (hl.dvd_mul.1 h).elim hc ha

theorem isTopUnit_topU_topV [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {l s N c d : ℕ} (x : ZMod N) (hl : l.Prime) (hN : 0 < N)
    (hs : 1 ≤ s) (hlN : Nat.Coprime l N) (hc1 : 1 < c) (hd1 : 1 < d) (hc : Nat.Coprime c (6 * l * N))
    (hd : Nat.Coprime d (6 * l * N)) :
    IsTopUnit X (l ^ s * N) (topU X l s N x c) ∧ IsTopUnit X (l ^ s * N) (topV X l s N d) := by
  have hM : l ^ s * N ≠ 0 := mul_ne_zero (pow_ne_zero s hl.ne_zero) hN.ne'
  have hls : l ∣ l ^ s := dvd_pow_self l (by omega)
  have hlM : l ∣ l ^ s * N := hls.mul_right N
  have hnd : ∀ {e : ℕ}, Nat.Coprime e (6 * l * N) → ¬ l ∣ e := fun {e} h =>
    (hl.coprime_iff_not_dvd).1 (h.coprime_dvd_right ((dvd_mul_left l 6).mul_right N)).symm
  have h6 : ∀ {e : ℕ}, Nat.Coprime e (6 * l * N) → Nat.Coprime e 6 := fun {e} h =>
    h.coprime_dvd_right ((dvd_mul_right 6 l).mul_right N)
  have hlN' : ¬ l ∣ N := (hl.coprime_iff_not_dvd).1 hlN
  have hlq : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  constructor
  · have e : (![1 / (l : ℚ) ^ s, (x.val : ℚ) * (topT l s N : ℚ) / N] : Fin 2 → ℚ) =
        ![(N : ℚ) / (l ^ s * N : ℕ), ((x.val * topT l s N * l ^ s : ℕ) : ℚ) / (l ^ s * N : ℕ)] := by
      congr 1
      · push_cast; field_simp
      · congr 1; push_cast; field_simp
    unfold topU
    rw [e]
    refine isTopUnit_siegel X ?_ ⟨hc1, h6 hc, fun h => not_int hl hM hlM (hnd hc) hlN' h.1⟩
    have : 1 < l ^ s := Nat.one_lt_pow (by omega) hl.one_lt
    nlinarith
  · have e : (![0, 1 / (l : ℚ) ^ s + (topT l s N : ℚ) / N] : Fin 2 → ℚ) =
        ![((0 : ℕ) : ℚ) / (l ^ s * N : ℕ), ((N + topT l s N * l ^ s : ℕ) : ℚ) / (l ^ s * N : ℕ)] := by
      congr 1
      · simp
      · congr 1; push_cast; field_simp
    unfold topV
    rw [e]
    refine isTopUnit_siegel X (Nat.pos_of_ne_zero hM) ⟨hd1, h6 hd, fun h => not_int hl hM hlM (hnd hd) (fun h' => hlN' ?_) h.2⟩
    exact (Nat.dvd_add_left (hls.mul_left _)).1 h'

end GlobalTheory.K4.TopUnits

namespace GlobalTheory.K4

open GlobalTheory.KZ

end GlobalTheory.K4
