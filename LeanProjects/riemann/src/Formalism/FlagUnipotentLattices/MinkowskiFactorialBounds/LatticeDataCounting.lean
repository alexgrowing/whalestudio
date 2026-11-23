import Formalism.FlagUnipotentLattices.OmSumLong
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ColonCountWeighted
import Formalism.HyperbolicPlaceProducts.SecondLevelArithmeticNorm

open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField

namespace Formalism.HermitianLatticeCounting.P
namespace LatticeDataCounting

lemma gen_of_local {R Q : Type*} [CommRing R] [AddCommGroup Q] [Module R Q] [Finite Q] (e : ℕ)
    (H : ∀ P : Ideal R, P.IsMaximal →
      ∃ s : Fin e → Q, Submodule.span R (Set.range s) ⊔ P • (⊤ : Submodule R Q) = ⊤) :
    ∃ s : Fin e → Q, Submodule.span R (Set.range s) = ⊤ := by
  classical
  let S : Set (Ideal R) := {P | P.IsMaximal ∧ P • (⊤ : Submodule R Q) ≠ ⊤}
  have hinj : Set.InjOn (fun P : Ideal R => P • (⊤ : Submodule R Q)) S := by
    intro P hP P' hP' hPP'
    by_contra hne
    have hsup : P ⊔ P' = ⊤ := hP.1.coprime_of_ne hP'.1 hne
    apply hP.2
    have hPP'' : P • (⊤ : Submodule R Q) = P' • (⊤ : Submodule R Q) := hPP'
    have h1 : (P ⊔ P') • (⊤ : Submodule R Q) = P • (⊤ : Submodule R Q) := by
      rw [Submodule.sup_smul, ← hPP'', sup_idem]
    rw [← h1, hsup, Submodule.top_smul]
  have hfin : S.Finite := Set.Finite.of_finite_image (Set.toFinite _) hinj
  have : Finite S := hfin
  let _ := Fintype.ofFinite S
  choose! sP hsP using H
  have hcop : Pairwise (Function.onFun IsCoprime (fun i : S => (i : Ideal R))) := by
    intro i j hij
    show IsCoprime (i : Ideal R) (j : Ideal R)
    rw [Ideal.isCoprime_iff_sup_eq]
    exact i.2.1.coprime_of_ne j.2.1 (fun h => hij (Subtype.ext h))
  have hε : ∀ i : S, ∃ r : R, ∀ j : S, r - (if j = i then 1 else 0) ∈ (j : Ideal R) :=
    fun i => Ideal.exists_forall_sub_mem_ideal hcop _
  choose ε hε using hε
  let s : Fin e → Q := fun k => ∑ i : S, ε i • sP i k
  refine ⟨s, ?_⟩
  by_contra hne
  obtain ⟨N', hN', hle⟩ := (eq_top_or_exists_le_coatom _).resolve_left hne
  have hsimple : IsSimpleModule R (Q ⧸ N') := isSimpleModule_iff_isCoatom.mpr hN'
  obtain ⟨P, hPmax, ⟨f⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
  have hPN : P • (⊤ : Submodule R Q) ≤ N' := by
    rw [Submodule.smul_le]
    intro r hr x _
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    apply f.injective
    rw [map_smul, map_zero]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (f (Submodule.Quotient.mk x))
    rw [← hy, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact P.mul_mem_right y hr
  have hPS : P ∈ S := ⟨hPmax, fun h => hN'.1 (top_le_iff.mp (h ▸ hPN))⟩
  have hk : ∀ k, sP P k ∈ N' := by
    intro k
    have h1 : s k - sP P k ∈ P • (⊤ : Submodule R Q) := by
      have h2 : sP P k = ∑ i : S, (if (⟨P, hPS⟩ : S) = i then (1 : R) else 0) • sP i k := by
        simp [ite_smul]
      have h3 : s k - sP P k =
          ∑ i : S, (ε i - (if (⟨P, hPS⟩ : S) = i then (1 : R) else 0)) • sP i k := by
        conv_lhs => rw [h2]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
      rw [h3]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hε i ⟨P, hPS⟩) trivial
    have h4 : s k ∈ N' := hle (Submodule.subset_span ⟨k, rfl⟩)
    have h5 : sP P k = s k - (s k - sP P k) := by abel
    rw [h5]
    exact N'.sub_mem h4 (hPN h1)
  have h6 : Submodule.span R (Set.range (sP P)) ⊔ P • (⊤ : Submodule R Q) ≤ N' := by
    refine sup_le ?_ hPN
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hk k
  rw [hsP P hPmax] at h6
  exact hN'.1 (top_le_iff.mp h6)

open TensorProduct in

lemma gen_mod_max {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (P : Ideal R) [hP : P.IsMaximal] :
    ∃ s : Fin (Module.finrank R M) → M,
      Submodule.span R (Set.range s) ⊔ P • (⊤ : Submodule R M) = ⊤ := by
  let _ := Ideal.Quotient.field P
  have e : ((R ⧸ P) ⊗[R] M) ≃ₗ[R] M ⧸ (P • (⊤ : Submodule R M)) :=
    TensorProduct.quotTensorEquivQuotSMul M P
  have hrk : Module.finrank (R ⧸ P) ((R ⧸ P) ⊗[R] M) = Module.finrank R M := by
    let q : PrimeSpectrum (R ⧸ P) := ⟨⊥, Ideal.isPrime_bot⟩
    have h1 := Module.rankAtStalk_baseChange (R := R) (M := M) (S := R ⧸ P) q
    rw [Module.rankAtStalk_eq_finrank_of_free] at h1
    have h2 : Module.rankAtStalk M (q.comap (algebraMap R (R ⧸ P))) = Module.finrank R M := by
      rw [Module.rankAtStalk_eq]
      exact Ideal.finrank_fiber_eq_finrank _
    rw [← h2, ← h1]
    rfl
  let b := Module.finBasisOfFinrankEq (R ⧸ P) ((R ⧸ P) ⊗[R] M) hrk
  have hb : Submodule.span R (Set.range b) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ P) Ideal.Quotient.mk_surjective, b.span_eq]
    rfl
  choose s hs using fun i => Submodule.Quotient.mk_surjective (P • (⊤ : Submodule R M)) (e (b i))
  refine ⟨s, ?_⟩
  rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
  have h3 : ((P • (⊤ : Submodule R M)).mkQ ∘ s) = e ∘ b := funext hs
  have h4 : Submodule.span R (e '' Set.range b) =
      (Submodule.span R (Set.range b)).map (e : _ →ₗ[R] _) := (Submodule.map_span _ _).symm
  rw [h3, Set.range_comp, h4, hb, Submodule.map_top, LinearMap.range_eq_top]
  exact e.surjective

lemma exists_quotient_spanning_family_finrank {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (I : Ideal R) [Finite (M ⧸ (I • (⊤ : Submodule R M)))] :
    ∃ s : Fin (Module.finrank R M) → M ⧸ (I • (⊤ : Submodule R M)),
      Submodule.span R (Set.range s) = ⊤ := by
  apply gen_of_local
  intro P hP
  obtain ⟨s, hs⟩ := gen_mod_max (M := M) P
  refine ⟨(I • (⊤ : Submodule R M)).mkQ ∘ s, ?_⟩
  have h1 : (Submodule.span R (Set.range s) ⊔ P • (⊤ : Submodule R M)).map
      (I • (⊤ : Submodule R M)).mkQ = ⊤ := by
    rw [hs, Submodule.map_top, Submodule.range_mkQ]
  rw [Submodule.map_sup, Submodule.map_span, ← Set.range_comp, Submodule.map_smul'', Submodule.map_top,
    Submodule.range_mkQ] at h1
  exact h1

theorem quotGen_proof' : QuotGen := by
  intro E _ _ M _ _ _ _ I hI
  have hc := height_loss_bound E M I
  have h0 : Ideal.absNorm I ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  have : Finite (M ⧸ (I • (⊤ : Submodule (𝓞 E) M))) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ h0)
  exact exists_quotient_spanning_family_finrank I

lemma pad {R X : Type*} [Semiring R] [AddCommMonoid X] [Module R X] {n j : ℕ} (hnj : n ≤ j) (s : Fin n → X)
    (B : Submodule R X) (hs : ∀ i, s i ∈ B) :
    ∃ t : Fin j → X, (∀ i, t i ∈ B) ∧
      Submodule.span R (Set.range s) ≤ Submodule.span R (Set.range t) := by
  refine ⟨fun i => if h : (i : ℕ) < n then s ⟨i, h⟩ else 0, fun i => ?_, ?_⟩
  · by_cases h : (i : ℕ) < n
    · simp only [h, dif_pos]; exact hs _
    · simp only [h, dif_neg, not_false_eq_true]; exact B.zero_mem
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, lt_of_lt_of_le i.2 hnj⟩, by simp⟩

section Lat

variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

lemma finrank_sub_le [FiniteDimensional E V] (B : Submodule (𝓞 E) V) :
    Module.finrank (𝓞 E) B ≤ Module.finrank E V := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := B) le_rfl
  have h1 : LinearIndependent (𝓞 E) (B.subtype ∘ f) := hf.map' B.subtype (Submodule.ker_subtype B)
  have h2 : LinearIndependent E (B.subtype ∘ f) := (LinearIndependent.iff_fractionRing (𝓞 E) E).mp h1
  simpa using h2.fintype_card_le_finrank

lemma latGen [FiniteDimensional E V] (j : ℕ) (hj : Module.finrank E V ≤ j) (A B : Submodule (𝓞 E) V)
    (hB : B.FG) (d : 𝓞 E) (hd : d ≠ 0) (hdB : ∀ x ∈ B, d • x ∈ A) :
    ∃ t : Fin j → V, (∀ i, t i ∈ B) ∧ B ≤ A ⊔ Submodule.span (𝓞 E) (Set.range t) := by
  have : Module.Finite (𝓞 E) B := Module.Finite.iff_fg.mpr hB
  have : Module.IsTorsionFree (𝓞 E) V := Module.IsTorsionFree.trans E
  have : Module.IsTorsionFree (𝓞 E) B :=
    Function.Injective.moduleIsTorsionFree B.subtype B.injective_subtype (fun _ _ => rfl)
  have : Module.FinitePresentation (𝓞 E) B := Module.finitePresentation_of_finite (𝓞 E) B
  have : Module.Projective (𝓞 E) B := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := quotGen_proof' E B (Ideal.span {d}) (by simpa using hd)
  choose s' hs' using fun i => Submodule.Quotient.mk_surjective _ (s i)
  obtain ⟨t, ht, hst⟩ := pad (R := 𝓞 E) ((finrank_sub_le B).trans hj) (fun i => (s' i : V)) B
    (fun i => (s' i).2)
  refine ⟨t, ht, ?_⟩
  have htop : Ideal.span {d} • (⊤ : Submodule (𝓞 E) B) ⊔ Submodule.span (𝓞 E) (Set.range s') = ⊤ := by
    rw [← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
    have : ((Ideal.span {d} • (⊤ : Submodule (𝓞 E) B)).mkQ ∘ s') = s := funext hs'
    rw [this, hs]
  intro x hx
  have hx' : (⟨x, hx⟩ : B) ∈
      Ideal.span {d} • (⊤ : Submodule (𝓞 E) B) ⊔ Submodule.span (𝓞 E) (Set.range s') := by
    rw [htop]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx'
  have hyA : (y : V) ∈ A := by
    rw [Submodule.ideal_span_singleton_smul] at hy
    obtain ⟨y', _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    exact hdB _ y'.2
  have hzS : (z : V) ∈ Submodule.span (𝓞 E) (Set.range t) := by
    apply hst
    have h1 : B.subtype z ∈ (Submodule.span (𝓞 E) (Set.range s')).map B.subtype :=
      Submodule.mem_map_of_mem hz
    rw [Submodule.map_span, ← Set.range_comp] at h1
    exact h1
  have hxe : x = (y : V) + (z : V) := by
    have := congrArg Subtype.val hyz
    exact this.symm
  rw [hxe]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hyA) (Submodule.mem_sup_right hzS)

lemma fg_of_smul_le (A B : Submodule (𝓞 E) V) (hA : A.FG) (d : 𝓞 E) (hd : d ≠ 0)
    (hdB : ∀ x ∈ B, d • x ∈ A) : B.FG := by
  have : Module.IsTorsionFree (𝓞 E) V := Module.IsTorsionFree.trans E
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 E) V d) := by
    intro x y hxy
    exact smul_right_injective V hd hxy
  apply Submodule.fg_of_fg_map_injective _ hinj
  have hN : IsNoetherian (𝓞 E) A := isNoetherian_of_fg_of_noetherian A hA
  apply isNoetherian_submodule.mp hN
  rintro _ ⟨x, hx, rfl⟩
  exact hdB x hx

end Lat

section Dual

variable {E U : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup U] [Module E U]
  [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U]

def hdualSub (h : U →ₗ[E] U →ₗ⋆[E] E) (N : Submodule (𝓞 E) U) : Submodule (𝓞 E) U :=
  { hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup with
    smul_mem' := by
      intro a x hx y hy
      rw [← algebraMap_smul E a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact (algebraMap (𝓞 E) E).range.mul_mem ⟨a, rfl⟩ (hx y hy) }

lemma star_mem (b : 𝓞 E) : star (algebraMap (𝓞 E) E b) ∈ (algebraMap (𝓞 E) E).range :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd E) b, rfl⟩

lemma mem_sup_span_iff {R X : Type*} [CommRing R] [AddCommGroup X] [Module R X] {n : ℕ} (N : Submodule R X)
    (t : Fin n → X) (x : X) :
    x ∈ N ⊔ Submodule.span R (Set.range t) ↔ ∃ c : Fin n → R, x - ∑ i, c i • t i ∈ N := by
  constructor
  · intro hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
    exact ⟨c, by simpa using ha⟩
  · rintro ⟨c, hc⟩
    have : x = (x - ∑ i, c i • t i) + ∑ i, c i • t i := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hc)
      (Submodule.mem_sup_right ((Submodule.mem_span_range_iff_exists_fun R).mpr ⟨c, rfl⟩))

theorem dualGen_span (h : U →ₗ[E] U →ₗ⋆[E] E) (M N : Submodule (𝓞 E) U) (e : ℕ) (s : Fin e → U)
    (hfin : N.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0)
    (hM : M ≤ N ⊔ Submodule.span (𝓞 E) (Set.range s)) (hs : ∀ i, s i ∈ M) :
    ∃ t : Fin e → U, (∀ i, t i ∈ hdualSub h N) ∧
      hdualSub h N ≤ hdualSub h M ⊔ Submodule.span (𝓞 E) (Set.range t) := by
  let φ : U →ₗ[𝓞 E] (Fin e → E) :=
    LinearMap.pi fun i => (h.flip (s i)).restrictScalars (𝓞 E)
  have hφ : ∀ x i, φ x i = h x (s i) := fun x i => rfl
  let A : Submodule (𝓞 E) (Fin e → E) := LinearMap.range ((Algebra.linearMap (𝓞 E) E).compLeft (Fin e))
  have hA : ∀ v : Fin e → E, v ∈ A ↔ ∀ i, v i ∈ (algebraMap (𝓞 E) E).range := by
    intro v
    constructor
    · rintro ⟨c, rfl⟩ i
      exact ⟨c i, rfl⟩
    · intro hv
      choose c hc using hv
      exact ⟨c, funext hc⟩
  have hAfg : A.FG := by
    show (LinearMap.range ((Algebra.linearMap (𝓞 E) E).compLeft (Fin e))).FG
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  let B : Submodule (𝓞 E) (Fin e → E) := (hdualSub h N).map φ
  set n := N.toAddSubgroup.relIndex M.toAddSubgroup with hn
  have hd : ((n : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast hfin
  have hdB : ∀ v ∈ B, ((n : ℕ) : 𝓞 E) • v ∈ A := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hA]
    intro i
    have h1 : n • s i ∈ N.toAddSubgroup := AddSubgroup.nsmul_relIndex_mem _ (hs i)
    have h2 := hx (n • s i) h1
    rw [map_nsmul] at h2
    rw [Nat.cast_smul_eq_nsmul, Pi.smul_apply, hφ]
    exact h2
  have hBfg : B.FG := fg_of_smul_le A B hAfg _ hd hdB
  obtain ⟨t', ht', hBt⟩ := latGen e (by simp) A B hBfg _ hd hdB
  choose t ht using ht'
  refine ⟨t, fun i => (ht i).1, ?_⟩
  intro x hx
  have h1 : φ x ∈ A ⊔ Submodule.span (𝓞 E) (Set.range t') := hBt ⟨x, hx, rfl⟩
  obtain ⟨c, hc⟩ := (mem_sup_span_iff A t' (φ x)).mp h1
  rw [mem_sup_span_iff]
  refine ⟨c, ?_⟩
  set x' := x - ∑ i, c i • t i with hx'
  have hx'N : x' ∈ hdualSub h N :=
    Submodule.sub_mem _ hx (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ht i).1)
  have hφx' : φ x' ∈ A := by
    have : φ x' = φ x - ∑ i, c i • t' i := by
      rw [hx', map_sub, map_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, (ht i).2]
    rw [this]; exact hc
  rw [hA] at hφx'
  intro m hm
  obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.mp (hM hm)
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp hy
  rw [map_add, map_sum]
  refine (algebraMap (𝓞 E) E).range.add_mem (hx'N a ha) (Subring.sum_mem _ fun i _ => ?_)
  rw [← algebraMap_smul E (b i) (s i), LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul]
  exact (algebraMap (𝓞 E) E).range.mul_mem (star_mem (b i)) (hφx' i)

end Dual

theorem dualGen_proof' : DualGen := by
  intro E _ _ _ U _ _ _ _ h M N e s _ hfin hM hs
  obtain ⟨t, ht, hle⟩ := dualGen_span h M N e s hfin hM hs
  exact ⟨t, ht, fun x hx => (mem_sup_span_iff _ t x).mp (hle hx)⟩

lemma split_pow (i' : ℝ) (hi : 1 ≤ i') (k : ℕ) (c : ℝ) : i' ^ ((k : ℝ) + c) = i' ^ k * i' ^ c := by
  rw [Real.rpow_add (by linarith), Real.rpow_natCast]

end LatticeDataCounting

theorem dual_generators : DualGen := LatticeDataCounting.dualGen_proof'

end Formalism.HermitianLatticeCounting.P
