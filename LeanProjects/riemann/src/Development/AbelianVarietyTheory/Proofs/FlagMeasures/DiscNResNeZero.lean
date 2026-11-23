import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveSublatticesGenusDefiniteLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairsIsometryNoFixedVectorCountBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountIsometryPairsWithGivenFixedSpaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianGenusMassEqOrbitStabilizerMassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootDiscrGeThreeHalvesOfIsTotallyComplex

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.PairMean

section Cyclic

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

def GoodAt (A B : Submodule R W) (P : Ideal R) (v : W) : Prop :=
  ∀ b ∈ B, ∃ s, s ∉ P ∧ ∃ r : R, s • b - r • v ∈ A

theorem goodAt_comb {A B : Submodule R W} {P : Ideal R} (hP : P.IsPrime) {v w : W} {e e' : R}
    (hw : GoodAt A B P w) (hv : v ∈ B) (he : e ∈ P) (he' : e' ∉ P) : GoodAt A B P (e • v + e' • w) := by
  intro b hb
  obtain ⟨s, hs, r, h⟩ := hw v hv
  obtain ⟨s', hs', r', h'⟩ := hw b hb
  refine ⟨(e * r + s * e') * s', fun hm => ?_, r' * s, ?_⟩
  · rcases hP.mem_or_mem hm with h1 | h1
    · have : s * e' ∈ P := by simpa using P.sub_mem h1 (P.mul_mem_right r he)
      exact (hP.mem_or_mem this).elim hs he'
    · exact hs' h1
  · have := A.sub_mem (A.smul_mem (e * r + s * e') h') (A.smul_mem (r' * e) h)
    convert this using 1
    module

theorem exists_goodAt {A B : Submodule R W} (S : Finset (Ideal R)) (hS : ∀ P ∈ S, P.IsMaximal)
    (h : ∀ P ∈ S, ∃ v ∈ B, GoodAt A B P v) : ∃ v ∈ B, ∀ P ∈ S, GoodAt A B P v := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, B.zero_mem, by simp⟩
  | insert P S hPS ih =>
    obtain ⟨v, hv, hg⟩ := ih (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ))
      (fun Q hQ => h Q (Finset.mem_insert_of_mem hQ))
    obtain ⟨w, hw, hgw⟩ := h P (Finset.mem_insert_self _ _)
    have hP := hS P (Finset.mem_insert_self _ _)
    have hn : ¬ S.inf id ≤ P := by
      rw [hP.isPrime.inf_le']
      rintro ⟨Q, hQ, hle⟩
      have := (hS Q (Finset.mem_insert_of_mem hQ)).eq_of_le hP.ne_top hle
      exact hPS (this ▸ hQ)
    obtain ⟨y, hy, hyP⟩ := SetLike.not_le_iff_exists.1 hn
    obtain ⟨a, e, he, hae⟩ := hP.exists_inv hyP
    refine ⟨e • v + (a * y) • w, B.add_mem (B.smul_mem _ hv) (B.smul_mem _ hw), fun Q hQ => ?_⟩
    rcases Finset.mem_insert.1 hQ with rfl | hQ'
    · refine goodAt_comb hP.isPrime hgw hv he fun hm => hP.ne_top ?_
      rw [Ideal.eq_top_iff_one, ← hae]
      exact Q.add_mem hm he
    · have hyQ : a * y ∈ Q := Q.mul_mem_left a (Finset.inf_le (f := id) hQ' hy)
      rw [add_comm]
      refine goodAt_comb (hS Q hQ).isPrime (hg Q hQ') hw hyQ fun hm => (hS Q hQ).ne_top ?_
      rw [Ideal.eq_top_iff_one, ← hae]
      exact Q.add_mem hyQ hm

theorem cyclic_of_local [IsDedekindDomain R] {A B : Submodule R W} (hAB : A ≤ B) (c : R) (hc : c ≠ 0)
    (hcB : ∀ b ∈ B, c • b ∈ A) (h : ∀ P : Ideal R, P.IsMaximal → ∃ v ∈ B, GoodAt A B P v) :
    ∃ v, B = A ⊔ Submodule.span R {v} := by
  have h0 : Ideal.span {c} ≠ ⊥ := by simpa using hc
  obtain ⟨v, hv, hg⟩ := exists_goodAt (A := A) (B := B)
    ((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {c})).toFinset.filter fun P => P.IsMaximal)
    (fun P hP => (Finset.mem_filter.1 hP).2) (fun P hP => h P (Finset.mem_filter.1 hP).2)
  refine ⟨v, le_antisymm (fun b hb => ?_) (sup_le hAB ((Submodule.span_singleton_le_iff_mem _ _).2 hv))⟩
  let I : Ideal R := (A ⊔ Submodule.span R {v}).comap (LinearMap.toSpanSingleton R W b)
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal I hne
    have hcP : c ∈ P := hle (Submodule.mem_sup_left (hcB b hb))
    obtain ⟨s, hs, r, hr⟩ := hg P (Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2
      ((Ideal.mem_normalizedFactors_iff h0).2 ⟨hP.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hcP⟩), hP⟩) b hb
    refine hs (hle ?_)
    change s • b ∈ A ⊔ Submodule.span R {v}
    rw [← sub_add_cancel (s • b) (r • v)]
    exact Submodule.add_mem_sup hr (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  have : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using this

end Cyclic

section Lat

open Formalism.HermitianLatticesTheory GlobalTheory.Mass

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem genBy_of_genus (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) {M N : Submodule (𝓞 K) V}
    (hM : Submodule.IsLattice K M) (hN : N ∈ genus h M) (hNd : N ≤ Formalism.HermitianLatticesTheory.dual h N) (h0 : discN h N ≠ 0)
    (t : V) (ht : t ∈ Formalism.HermitianLatticesTheory.dual h M) (htM : ∀ y ∈ Formalism.HermitianLatticesTheory.dual h M, ∃ r : 𝓞 K, y - r • t ∈ M) :
    GenBy (Formalism.HermitianLatticesTheory.dual h N) N 1 := by
  have ld := locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨v, hv⟩ := cyclic_of_local hNd (discN h N : 𝓞 K) (by exact_mod_cast h0) (fun x hx => by
      rw [Nat.cast_smul_eq_nsmul]
      exact AddSubgroup.nsmul_index_mem
        (H := N.toAddSubgroup.addSubgroupOf (Formalism.HermitianLatticesTheory.dual h N).toAddSubgroup) ⟨x, hx⟩) (fun P hP => by
    obtain ⟨g, hg, hgL⟩ := hN.2 P hP
    have hle := locBasic_hcompl_le (K := K) P
    have key : ∀ A B : Submodule (𝓞 K) V, gmap g (loc (K := K) P A) = loc (K := K) P B →
        gmap g (locS P.primeCompl A) = locS P.primeCompl B := by
      intro A B e
      rw [← genusCovol_locS_locS hle A, gmap_locS_comm]
      change locS P.primeCompl (gmap g (loc (K := K) P A)) = _
      rw [e]
      exact genusCovol_locS_locS hle B
    obtain ⟨a1, a2, -, -, a5⟩ := isomAct (𝓞 K) K V h g hg M
    have b1 := (ld (gmap g M) (a5.2 hM).fg).1 P hP.isPrime
    have b2 := (ld N hN.1.fg).1 P hP.isPrime
    have k1 := key _ _ hgL
    have k2 := key (Formalism.HermitianLatticesTheory.dual h M) (Formalism.HermitianLatticesTheory.dual h N) (by
      rw [b2.1, ← b2.2, ← hgL, ← a2 P, b1.2, ← b1.1, a1, (isomAct (𝓞 K) K V h g hg (Formalism.HermitianLatticesTheory.dual h M)).2.1 P])
    have up : ∀ (A : Submodule (𝓞 K) V) x, x ∈ A → x ∈ locS P.primeCompl A :=
      fun A x hx => ⟨1, one_mem _, by rwa [one_smul]⟩
    obtain ⟨s₀, hs₀, hv⟩ : g t ∈ locS P.primeCompl (Formalism.HermitianLatticesTheory.dual h N) := k2 ▸ ⟨t, up _ _ ht, rfl⟩
    refine ⟨_, hv, fun b hb => ?_⟩
    obtain ⟨y, ⟨s, hs, hy⟩, hyb⟩ : b ∈ gmap g (locS P.primeCompl (Formalism.HermitianLatticesTheory.dual h M)) := k2 ▸ up _ _ hb
    obtain ⟨r, hr⟩ := htM _ hy
    obtain ⟨s', hs', ha⟩ : ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) (s • y - r • t) ∈ locS P.primeCompl N :=
      k1 ▸ ⟨_, up _ _ hr, rfl⟩
    refine ⟨s₀ * s' * s, mul_mem (mul_mem hs₀ hs') hs, s' * r, ?_⟩
    rw [map_sub, map_smul, map_smul, hyb] at ha
    have := N.smul_mem s₀ ha
    convert this using 1
    change _ = s₀ • s' • (s • b - r • g t)
    module)
  exact ⟨{v}, by simp, by simpa using hv⟩

omit [NumberField K] in
theorem discN_top (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) :
    discN (hRes h ⊤) (latIn ⊤ L) = discN h L := by
  have e : Formalism.HermitianLatticesTheory.dual (hRes h ⊤) (latIn ⊤ L) = latIn ⊤ (Formalism.HermitianLatticesTheory.dual h L) := by
    ext x
    change _ ↔ (x : V) ∈ Formalism.HermitianLatticesTheory.dual h L
    rw [isomAct_mem_dual, isomAct_mem_dual]
    exact ⟨fun a y hy => a ⟨y, trivial⟩ hy, fun a y hy => a y hy⟩
  unfold discN
  rw [e]
  let f : (⊤ : Submodule K V) →+ V := ((⊤ : Submodule K V).subtype : (⊤ : Submodule K V) →+ V)
  change (L.toAddSubgroup.comap f).relIndex ((Formalism.HermitianLatticesTheory.dual h L).toAddSubgroup.comap f) = _
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective (fun y => ⟨⟨y, trivial⟩, rfl⟩)]
  rfl

theorem isIntLat_latIn (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V} (hL : IsIntLat h L)
    (U : Submodule K V) : IsIntLat (hRes h U) (latIn U L) := by
  refine ⟨⟨?_, ?_⟩, fun x hx y hy => hL.2 x hx y hy⟩
  · apply Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype
    exact hL.1.fg.of_le (Submodule.map_comap_le _ _)
  · refine eq_top_iff.mpr fun x _ => ?_
    have hx : (x : V) ∈ Submodule.span K (L : Set V) := by rw [hL.1.span_eq_top]; trivial
    obtain ⟨a, hax⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ hx
    rw [Submodule.span_eq] at hax
    have ha' : algebraMap (𝓞 K) K a ≠ 0 := by simpa using nonZeroDivisors.coe_ne_zero a
    rw [← Submodule.smul_mem_iff _ ha', algebraMap_smul]
    exact Submodule.subset_span hax

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem pd_nondeg (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  constructor <;>
  · intro x hx
    by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this

theorem discN_res_ne_zero [FiniteDimensional K V] (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hs : h.IsSymm) (hp : PD h) {L : Submodule (𝓞 K) V} (hL : IsIntLat h L) (U : Submodule K V) :
    discN (hRes h U) (latIn U L) ≠ 0 :=
  (GlobalTheory.Mass.DiscOrder.main K U (hRes h U) hK ⟨fun x y => hs.eq (x : V) (y : V)⟩
    (pd_nondeg _ fun τ x hx => hp τ (x : V) (fun e => hx (Subtype.ext e))) _ (isIntLat_latIn h hL U)).1

theorem of_equiv (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (T : ℕ)
    (e : (↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) :
    discN h L = T ^ Module.finrank ℚ K ∧
      ∃ t ∈ Formalism.HermitianLatticesTheory.dual h L, ∀ y ∈ Formalism.HermitianLatticesTheory.dual h L, ∃ r : 𝓞 K, y - r • t ∈ L := by
  constructor
  · unfold discN
    rw [GlobalTheory.Mass.DiscOrder.idxN_eq_card, Nat.card_congr e.toEquiv, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  · obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))
    refine ⟨t, t.2, fun y hy => ?_⟩
    obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (e (Submodule.Quotient.mk ⟨y, hy⟩))
    refine ⟨r, ?_⟩
    have : (Submodule.Quotient.mk ⟨y, hy⟩ : ↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) =
        Submodule.Quotient.mk (r • t) := by
      rw [Submodule.Quotient.mk_smul, ht, ← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, hr,
        LinearEquiv.symm_apply_apply]
    have h2 := (Submodule.Quotient.eq _).1 this
    exact h2

end Lat

section Count

theorem encard_fibres_le {α β : Type} (S : Set α) (φ : α → β) (P : Set β) (B : ℝ≥0∞)
    (h : ∀ U ∈ P, ((({p ∈ S | φ p = U}).encard : ℕ∞) : ℝ≥0∞) ≤ B) :
    ((({p ∈ S | φ p ∈ P}).encard : ℕ∞) : ℝ≥0∞) ≤ ((P.encard : ℕ∞) : ℝ≥0∞) * B := by
  have e : {p ∈ S | φ p ∈ P} = ⋃ U ∈ P, {p ∈ S | φ p = U} := by
    ext p
    simp [and_comm]
  rw [e, ← ENNReal.tsum_set_one, ← ENNReal.tsum_set_const]
  refine (ENNReal.tsum_biUnion_le_tsum (fun _ => 1) _ _).trans (ENNReal.tsum_le_tsum fun U => ?_)
  rw [ENNReal.tsum_set_one]
  exact h U U.2

theorem encard_cover_le {α ι : Type} (S A₁ A₂ : Set α) (I : Finset ι) (F : ι → Set α)
    (h : S ⊆ A₁ ∪ A₂ ∪ ⋃ i ∈ I, F i) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ (A₁.encard : ℕ∞) + (A₂.encard : ℕ∞) + ∑ i ∈ I, (((F i).encard : ℕ∞) : ℝ≥0∞) := by
  have h1 : S.encard ≤ A₁.encard + A₂.encard + (⋃ i ∈ I, F i).encard :=
    (Set.encard_le_encard h).trans ((Set.encard_union_le _ _).trans (by
      gcongr; exact Set.encard_union_le _ _))
  have h2 : (((⋃ i ∈ I, F i).encard : ℕ∞) : ℝ≥0∞) ≤ ∑ i ∈ I, (((F i).encard : ℕ∞) : ℝ≥0∞) := by
    simp only [← ENNReal.tsum_set_one]
    exact ENNReal.tsum_biUnion_le (fun _ => 1) I F
  calc ((S.encard : ℕ∞) : ℝ≥0∞) ≤ (A₁.encard : ℕ∞) + (A₂.encard : ℕ∞) + ((⋃ i ∈ I, F i).encard : ℕ∞) := by
        exact_mod_cast h1
    _ ≤ _ := by gcongr

theorem orbSum_le_lin {G α ι : Type} [Group G] [MulAction G α] (X : Set α) (N : α → ℝ≥0∞) (c : ℝ≥0∞)
    (I : Finset ι) (M : ι → α → ℝ≥0∞) (B : ι → ℝ≥0∞) (h : ∀ a ∈ X, N a ≤ c + ∑ i ∈ I, M i a * B i) :
    GlobalTheory.Mass.orbSum G X N ≤ GlobalTheory.Mass.orbMass G X * c + ∑ i ∈ I, GlobalTheory.Mass.orbSum G X (M i) * B i := by
  unfold GlobalTheory.Mass.orbMass GlobalTheory.Mass.orbSum
  simp only [← ENNReal.tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun q => ?_
  refine (mul_le_mul_right (h _ q.2) _).trans (le_of_eq ?_)
  simp only [mul_add, Finset.mul_sum, mul_one, mul_assoc]

end Count

theorem mid_bound (m A c D X Y : ℝ) (g n s k f j x x' : ℕ) (hm : 0 ≤ m) (hA : 0 ≤ A) (hc : 0 ≤ c) (hD : 1 ≤ D)
    (hX : X = (x : ℝ) * x') (hX1 : 1 ≤ X) (hY : Y = X * D ^ 2) (hg : 2 ≤ g) (hn : 1 ≤ n) (hnD : (n : ℝ) ≤ D * X)
    (hs : s ≤ k) :
    m * (A * 16 ^ (s * k * f)) * ((n : ℝ) / D) ^ ((k : ℝ) / 2) * ((n : ℝ) * D) ^ (5 * (s : ℝ) + 5 + 2 * c) *
      (((2 / (g : ℝ)) ^ (2 * s * f) * D * x * x' / n) ^ ((k : ℝ) / 2) * X ^ (2 * (s : ℝ) + 2 * c + 1) *
        Y ^ (3 * (2 * j + 1)) * ((4 * s * f : ℕ) : ℝ) ^ (4 * s * f)) ≤
    m * X ^ ((k : ℝ) / 2) * Y ^ (6 * (j : ℝ) + 9 + 4 * c) * A *
      ((32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * Y ^ 7) ^ s := by
  have n0 : (0 : ℝ) < n := by exact_mod_cast hn
  have g0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have D0 : 0 < D := by linarith
  have X0 : 0 < X := by linarith
  have hXY : X ≤ Y := by rw [hY]; exact le_mul_of_one_le_right X0.le (one_le_pow₀ hD)
  have Y0 : 0 < Y := by linarith
  have e1 : ((n : ℝ) / D) ^ ((k : ℝ) / 2) * ((2 / (g : ℝ)) ^ (2 * s * f) * D * x * x' / n) ^ ((k : ℝ) / 2) =
      (2 / (g : ℝ)) ^ (s * k * f) * X ^ ((k : ℝ) / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have : (n : ℝ) / D * ((2 / (g : ℝ)) ^ (2 * s * f) * D * x * x' / n) = (2 / (g : ℝ)) ^ (2 * s * f) * X := by
      rw [hX]; field_simp
    rw [this, Real.mul_rpow (by positivity) X0.le, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      ← Real.rpow_natCast]
    congr 2
    push_cast
    ring
  have b1 : ((n : ℝ) * D) ^ (5 * (s : ℝ) + 5 + 2 * c) ≤ Y ^ (5 * (s : ℝ) + 5 + 2 * c) :=
    Real.rpow_le_rpow (by positivity) (by rw [hY]; nlinarith) (by positivity)
  have b2 : X ^ (2 * (s : ℝ) + 2 * c + 1) ≤ Y ^ (2 * (s : ℝ) + 2 * c + 1) :=
    Real.rpow_le_rpow X0.le hXY (by positivity)
  have b3 : ((4 * s * f : ℕ) : ℝ) ^ (4 * s * f) ≤ ((4 * k * f : ℕ) : ℝ) ^ (4 * s * f) := by gcongr
  have e2 : Y ^ (5 * (s : ℝ) + 5 + 2 * c) * Y ^ (2 * (s : ℝ) + 2 * c + 1) * Y ^ (3 * (2 * j + 1)) =
      Y ^ (6 * (j : ℝ) + 9 + 4 * c) * (Y ^ 7) ^ s := by
    rw [← pow_mul, ← Real.rpow_natCast Y (3 * _), ← Real.rpow_natCast Y (7 * _), ← Real.rpow_add Y0,
      ← Real.rpow_add Y0, ← Real.rpow_add Y0]
    congr 1
    push_cast
    ring
  have e3 : (16 : ℝ) ^ (s * k * f) * (2 / (g : ℝ)) ^ (s * k * f) = ((32 / (g : ℝ)) ^ (k * f)) ^ s := by
    rw [← mul_pow, ← pow_mul]
    congr 1 <;> ring
  have e4 : ((4 * k * f : ℕ) : ℝ) ^ (4 * s * f) = (((4 * k * f : ℕ) : ℝ) ^ (4 * f)) ^ s := by
    rw [← pow_mul]; congr 1; ring
  calc _ = m * A * 16 ^ (s * k * f) * (((n : ℝ) / D) ^ ((k : ℝ) / 2) *
        ((2 / (g : ℝ)) ^ (2 * s * f) * D * x * x' / n) ^ ((k : ℝ) / 2)) *
        (((n : ℝ) * D) ^ (5 * (s : ℝ) + 5 + 2 * c) * X ^ (2 * (s : ℝ) + 2 * c + 1) * Y ^ (3 * (2 * j + 1))) *
        ((4 * s * f : ℕ) : ℝ) ^ (4 * s * f) := by ring
    _ ≤ m * A * 16 ^ (s * k * f) * ((2 / (g : ℝ)) ^ (s * k * f) * X ^ ((k : ℝ) / 2)) *
        (Y ^ (5 * (s : ℝ) + 5 + 2 * c) * Y ^ (2 * (s : ℝ) + 2 * c + 1) * Y ^ (3 * (2 * j + 1))) *
        ((4 * k * f : ℕ) : ℝ) ^ (4 * s * f) := by rw [e1]; gcongr
    _ = m * X ^ ((k : ℝ) / 2) * A * ((16 : ℝ) ^ (s * k * f) * (2 / (g : ℝ)) ^ (s * k * f)) *
        (Y ^ (5 * (s : ℝ) + 5 + 2 * c) * Y ^ (2 * (s : ℝ) + 2 * c + 1) * Y ^ (3 * (2 * j + 1))) *
        ((4 * k * f : ℕ) : ℝ) ^ (4 * s * f) := by ring
    _ = _ := by rw [e2, e3, e4, mul_pow, mul_pow]; ring

theorem top_bound (c D X Y : ℝ) (g k f j x x' : ℕ) (hc : 0 ≤ c) (hD : 1 ≤ D)
    (hX : X = (x : ℝ) * x') (hX1 : 1 ≤ X) (hY : Y = X * D ^ 2) :
    ((2 / (g : ℝ)) ^ (2 * 0 * f) * D * x * x' / D) ^ ((k : ℝ) / 2) * X ^ (2 * ((0 : ℕ) : ℝ) + 2 * c + 1) *
        Y ^ (3 * (2 * j + 1)) * ((4 * 0 * f : ℕ) : ℝ) ^ (4 * 0 * f) ≤
      X ^ ((k : ℝ) / 2) * Y ^ (6 * (j : ℝ) + 10 + 4 * c) := by
  have D0 : 0 < D := by linarith
  have X0 : 0 < X := by linarith
  have hXY : X ≤ Y := by rw [hY]; exact le_mul_of_one_le_right X0.le (one_le_pow₀ hD)
  have Y0 : 0 < Y := by linarith
  have e : (2 / (g : ℝ)) ^ (2 * 0 * f) * D * x * x' / D = X := by rw [hX]; simp; field_simp
  rw [e]
  simp only [mul_zero, zero_mul, pow_zero, mul_one, Nat.cast_zero, zero_add, mul_assoc]
  gcongr
  calc _ ≤ Y ^ (2 * c + 1) * Y ^ (3 * (2 * j + 1)) := by gcongr
    _ = Y ^ (2 * c + 1 + (3 * (2 * j + 1) : ℕ)) := by rw [Real.rpow_add Y0 (2 * c + 1), Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)

set_option maxHeartbeats 800000 in

theorem main : MinkowskiBound → GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → HasOrtho K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → GlobalTheory.Mass.PD H.B.flip → 3 ≤ (Module.finrank K V) → ∀ (T : ℕ) (L₀ : Submodule (𝓞 K) V) (Mb : ℝ), T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → GlobalTheory.Mass.IsIntLat H.B.flip L₀ → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual H.B.flip L₀) ⧸ L₀.comap (Formalism.HermitianLatticesTheory.dual H.B.flip L₀).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → Mb = (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) → ∀ D₀ : ℝ, D₀ = (T : ℝ) ^ (2 * (Formalism.HermitianLatticesTheory.fDeg K)) → ∀ (g j x x' : ℕ) (Y : ℝ), 2 ≤ g → 1 ≤ x → 1 ≤ x' → Y = (x : ℝ) * x' * D₀ ^ 2 → GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom H.B.flip) (Formalism.HermitianLatticesTheory.genus H.B.flip L₀) (fun L => (((Trip H g L j x x').encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass H.B.flip L₀ * ((x : ℝ) * x') ^ (((Module.finrank K V) : ℝ) / 2) * Y ^ (6 * (j : ℝ) + 10 + 4 * cf K) * (1 + Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * (∑ s ∈ Finset.Ico 1 (Module.finrank K V), ((32 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * Y ^ 7) ^ s) + ((2 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x') ^ (Module.finrank K V))) := by
  intro hMk hMax hSi K V _ _ _ _ _ _ _ _ H hK hO hv hpd hk T L₀ Mb hT hTP hL₀ he hMb D₀ hD₀ g j x x' Y hg hx hx' hY
  have hSC := GlobalTheory.T.mean_primitiveSublattices_genus_definiteLattice hMax hSi K V H hK hO hv hpd hk T L₀ Mb hT hTP hL₀ he hMb D₀ hD₀
  obtain ⟨e⟩ := he
  have hs := flip_isSymm H
  have hnd := pd_nondeg _ hpd
  obtain ⟨hd, t, ht, htM⟩ := of_equiv _ L₀ T e
  rw [(GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex K hK.1).1] at hd
  obtain ⟨hmass, hm0, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V H.B.flip hK hs hpd L₀ hL₀.1
  have hgen := (GlobalTheory.Mass.DiscOrder.main K V H.B.flip hK hs hnd L₀ hL₀).2.2.2.1
  set k := Module.finrank K V with hkdef
  set f := Formalism.HermitianLatticesTheory.fDeg K with hf
  set m := Formalism.HermitianLatticesTheory.mass H.B.flip L₀ with hm
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = T ^ (2 * f) := ⟨_, rfl⟩
  rw [← hD] at hd
  have hDD : D₀ = D := by rw [hD₀, hD]; push_cast; rfl
  have hD1 : 1 ≤ D := by rw [hD]; exact Nat.one_le_pow _ _ hT.pos
  subst hDD
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hc : 0 ≤ cf K := add_nonneg zero_le_one (Real.logb_nonneg one_lt_two (by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)))
  have hMb0 : 0 ≤ Mb := by rw [hMb]; positivity
  have hA : 0 ≤ Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ f := by positivity
  have hX1 : (1 : ℝ) ≤ (x : ℝ) * x' := by exact_mod_cast Nat.mul_pos hx hx'
  have hY1 : (D : ℝ) * ((x : ℝ) * x') ≤ Y := by rw [hY]; nlinarith [mul_nonneg (sub_nonneg.2 hX1) (sub_nonneg.2 hD1')]
  have hY2 : 1 ≤ Y := le_trans (one_le_mul_of_one_le_of_one_le hD1' hX1) hY1
  have Y0 : 0 < Y := by linarith
  set c := cf K with hcdef
  set Z := ((x : ℝ) * x') ^ ((k : ℝ) / 2) with hZ
  have Z0 : 0 ≤ Z := by positivity
  set Pk := ((2 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * D * x * x') ^ k with hPk
  have Pk0 : 0 ≤ Pk := by positivity
  let I : Finset (ℕ × ℕ) := Finset.Ico 1 k ×ˢ Finset.Icc 1 (D * x * x')
  let B : ℕ × ℕ → ℝ := fun i => ((2 / (g : ℝ)) ^ (2 * i.1 * f) * D * x * x' / i.2) ^ ((k : ℝ) / 2) *
    ((x : ℝ) * x') ^ (2 * (i.1 : ℝ) + 2 * c + 1) * Y ^ (3 * (2 * j + 1)) * ((4 * i.1 * f : ℕ) : ℝ) ^ (4 * i.1 * f)
  have h1 := orbSum_le_lin (G := Formalism.HermitianLatticesTheory.isom H.B.flip) (Formalism.HermitianLatticesTheory.genus H.B.flip L₀)
    (fun L => (((Trip H g L j x x').encard : ℕ∞) : ℝ≥0∞))
    (ENNReal.ofReal (Z * Y ^ (6 * (j : ℝ) + 10 + 4 * c) * (1 + Pk))) I
    (fun i L => (((GlobalTheory.Mass.primSp H.B.flip L (k - i.1) i.2).encard : ℕ∞) : ℝ≥0∞))
    (fun i => ENNReal.ofReal (B i)) (by
      intro L hL
      obtain ⟨hLi, hLd⟩ := hgen L hL
      rw [hd] at hLd
      have hG : GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L) L 1 := genBy_of_genus _ hs hL₀.1 hL
        (fun x hx => (Formalism.HermitianLatticesTheory.isomAct_mem_dual _ L x).2 fun y hy => hLi.2 y hy x hx)
        (by rw [hLd]; omega) t ht htM
      have ps := fun s n U => GlobalTheory.T.count_isometry_pairs_with_given_fixed_space hMk K V H hK hpd L g j D hLi hLd hG hg x x' s n U hx hx'
      have pk := GlobalTheory.T.pairs_isometry_no_fixed_vector_count_bound hMk K V H hK hpd L g j D hLi hLd hG hg x x' hx hx'
      rw [← hY] at ps pk
      refine (encard_cover_le _ {p ∈ Trip H g L j x x' | fixSp p.2.2 = ⊤}
        {p ∈ Trip H g L j x x' | fixSp p.2.2 = ⊥} I
        (fun i => {p ∈ Trip H g L j x x' | fixSp p.2.2 ∈ GlobalTheory.Mass.primSp H.B.flip L (k - i.1) i.2}) ?_).trans ?_
      · intro p hp
        by_cases h1 : fixSp p.2.2 = ⊤
        · exact Or.inl (Or.inl ⟨hp, h1⟩)
        by_cases h2 : fixSp p.2.2 = ⊥
        · exact Or.inl (Or.inr ⟨hp, h2⟩)
        have l1 : Module.finrank K (fixSp p.2.2) < k := Submodule.finrank_lt h1
        have l2 : Module.finrank K (fixSp p.2.2) ≠ 0 := fun e => h2 (Submodule.finrank_eq_zero.1 e)
        have l3 := Nat.one_le_iff_ne_zero.2 (discN_res_ne_zero hK _ hs hpd hLi (fixSp p.2.2))
        have l4 := ps (k - Module.finrank K (fixSp p.2.2)) _ (fixSp p.2.2) l3 (by omega) rfl
        refine Or.inr (Set.mem_biUnion (x := (k - Module.finrank K (fixSp p.2.2),
          GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip (fixSp p.2.2)) (GlobalTheory.Mass.latIn (fixSp p.2.2) L))) ?_
          ⟨hp, by simp only; omega, rfl⟩)
        simp only [I, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Ico, Finset.mem_Icc]
        refine ⟨by omega, l3, ?_⟩
        by_contra hn
        rw [if_neg (fun a => hn (by exact_mod_cast a))] at l4
        have : ({q ∈ Trip H g L j x x' | fixSp q.2.2 = fixSp p.2.2}).encard = 0 := by simpa using l4
        exact (Set.eq_empty_iff_forall_notMem.1 (Set.encard_eq_zero.1 this)) p ⟨hp, rfl⟩
      · refine add_le_add ?_ (Finset.sum_le_sum fun i hi => encard_fibres_le _ _ _ _ fun U hU => ?_)
        · have p0 := ps 0 D ⊤ hD1 (by simp) ((discN_top _ _).trans hLd)
          rw [if_pos (by nlinarith)] at p0
          rw [mul_add, mul_one, ENNReal.ofReal_add (by positivity) (by positivity)]
          refine add_le_add (p0.trans (ENNReal.ofReal_le_ofReal
            (top_bound c D _ Y g k f j x x' hc hD1' rfl hX1 hY))) (pk.trans (ENNReal.ofReal_le_ofReal ?_))
          have : Y ^ (c + 3 * (2 * (j : ℝ) + 1)) ≤ Y ^ (6 * (j : ℝ) + 10 + 4 * c) :=
            Real.rpow_le_rpow_of_exponent_le hY2 (by linarith)
          change Z * _ * Pk ≤ _
          gcongr
        · simp only [I, Finset.mem_product, Finset.mem_Ico, Finset.mem_Icc] at hi
          have p1 := ps i.1 i.2 U hi.2.1 (by rw [hU.1]; omega) hU.2
          rw [if_pos (by exact_mod_cast hi.2.2)] at p1
          exact p1)
  refine h1.trans ?_
  rw [← hmass, ← ENNReal.ofReal_mul hm0.le]
  set C : ℕ → ℝ := fun s => ((32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * Y ^ 7) ^ s with hC
  have C0 : ∀ s, 0 ≤ C s := fun s => pow_nonneg (by positivity) _
  set A := Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ f with hAdef
  have h2 : ∑ i ∈ I, GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom H.B.flip) (Formalism.HermitianLatticesTheory.genus H.B.flip L₀)
      (fun L => (((GlobalTheory.Mass.primSp H.B.flip L (k - i.1) i.2).encard : ℕ∞) : ℝ≥0∞)) * ENNReal.ofReal (B i) ≤
      ∑ i ∈ I, ENNReal.ofReal (m * Z * Y ^ (6 * (j : ℝ) + 9 + 4 * c) * A * C i.1) := by
    refine Finset.sum_le_sum fun i hi => ?_
    simp only [I, Finset.mem_product, Finset.mem_Ico, Finset.mem_Icc] at hi
    refine (mul_le_mul_left (hSC i.1 i.2 hi.1.1 hi.1.2 hi.2.1) _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (mid_bound m A c D _ Y g i.2 i.1 k f j x x' hm0.le hA hc hD1' rfl hX1 hY hg
      hi.2.1 (by rw [← mul_assoc]; exact_mod_cast hi.2.2) hi.1.2.le)
  refine (add_le_add_right h2 _).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := C0 i.1; positivity),
    ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun i _ => by have := C0 i.1; positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : ∑ i ∈ I, m * Z * Y ^ (6 * (j : ℝ) + 9 + 4 * c) * A * C i.1 =
      (D * ((x : ℝ) * x')) * (m * Z * Y ^ (6 * (j : ℝ) + 9 + 4 * c) * A * ∑ s ∈ Finset.Ico 1 k, C s) := by
    rw [Finset.sum_product, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [mul_assoc]
  have e2 : Y ^ (6 * (j : ℝ) + 10 + 4 * c) = Y * Y ^ (6 * (j : ℝ) + 9 + 4 * c) := by
    rw [← Real.rpow_one_add' Y0.le (by positivity)]
    congr 1
    ring
  have S0 : 0 ≤ ∑ s ∈ Finset.Ico 1 k, C s := Finset.sum_nonneg fun s _ => C0 s
  have b := mul_le_mul_of_nonneg_right hY1
    (show 0 ≤ m * Z * Y ^ (6 * (j : ℝ) + 9 + 4 * c) * A * ∑ s ∈ Finset.Ico 1 k, C s by positivity)
  rw [e1, e2]
  refine (add_le_add_right b _).trans (le_of_eq ?_)
  ring

end GlobalTheory.DegCnt.PairMean
