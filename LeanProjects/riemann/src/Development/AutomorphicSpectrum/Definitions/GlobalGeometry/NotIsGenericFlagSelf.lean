import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagModel

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem isFlagVBOn_frame {r : ℕ} (b : Fin r → E) (hb : LinearIndependent Ω b) (T : Set (Cpt ξ)) :
    Lat.IsFlagVBOn (fun p => Submodule.span (regAt ξ p) (Set.range b) : Lat ξ E) T b := by
  intro p _
  exact ⟨⊤, trivial, b, fun _ => rfl, fun q _ _ => And.intro hb rfl⟩

theorem not_mem_flagStep {r : ℕ} (b : Fin r → E) (hb : LinearIndependent Ω b) (i : Fin r) :
    b i ∉ flagStep Ω b i := by
  exact hb.notMem_span_image (by simp)

theorem gr_isGenAt {r : ℕ} (L : Lat ξ E) (b b₀ : Fin r → E) (p : Cpt ξ) (hL : L.IsFrameAt b p)
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) (c : Ω)
    (hc : b i - c • b₀ i ∈ flagStep Ω b₀ i) : (L.gr b₀ i).IsGenAt p c := by
  obtain ⟨hb, hLp⟩ := hL
  have hbi : b i ∉ flagStep Ω b i := not_mem_flagStep b hb i
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hbi
    rw [hF]
    simpa using hc
  refine ⟨hc0, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro t ⟨e, he, het⟩
    rw [hLp] at he
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (regAt ξ p)).mp he
    have het' : ∑ k, (d k : Ω) • b k - t • b₀ i ∈ flagStep Ω b₀ i := het
    set S : Submodule Ω E := Submodule.span Ω (b '' {k | k ≠ i}) with hS
    have hFS : flagStep Ω b₀ i ≤ S := by
      rw [← hF]
      refine Submodule.span_mono ?_
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨k, fun hki => ?_, rfl⟩
      subst hki
      exact lt_irrefl (k : ℕ) hk
    have h1 : c • (∑ k, (d k : Ω) • b k - t • b₀ i) ∈ S := S.smul_mem c (hFS het')
    have h2 : c • ∑ k ∈ Finset.univ.erase i, (d k : Ω) • b k ∈ S :=
      S.smul_mem c (Submodule.sum_mem _ fun k hk =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, Finset.ne_of_mem_erase hk, rfl⟩))
    have h3 : t • (b i - c • b₀ i) ∈ S := S.smul_mem t (hFS hc)
    have heq : (c * (d i : Ω) - t) • b i =
        c • (∑ k, (d k : Ω) • b k - t • b₀ i) - c • ∑ k ∈ Finset.univ.erase i, (d k : Ω) • b k -
          t • (b i - c • b₀ i) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      module
    have key : (c * (d i : Ω) - t) • b i ∈ S := by
      rw [heq]
      exact S.sub_mem (S.sub_mem h1 h2) h3
    have hzero : c * (d i : Ω) - t = 0 := by
      by_contra hne
      apply hb.notMem_span_image (s := {k | k ≠ i}) (x := i) (by simp)
      have := S.smul_mem (c * (d i : Ω) - t)⁻¹ key
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    refine Submodule.mem_span_singleton.mpr ⟨d i, ?_⟩
    show (d i : Ω) * c = t
    rw [mul_comm]
    exact sub_eq_zero.mp hzero
  · refine Submodule.span_le.mpr ?_
    rintro _ rfl
    refine Submodule.subset_span ⟨b i, ?_, hc⟩
    rw [hLp]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem exists_gen {r : ℕ} (L : Lat ξ E) (T : Set (Cpt ξ)) (b₀ : Fin r → E) (h : L.IsFlagVBOn T b₀)
    (p : Cpt ξ) (hp : p ∈ T) (i : Fin r) : ∃ c, (L.gr b₀ i).IsGenAt p c := by
  obtain ⟨U, hpU, b, hF, hfr⟩ := h p hp
  have hL := hfr p hp hpU
  have hmem : b i ∈ flagStep Ω b₀ ((i : ℕ) + 1) := by
    rw [← hF]
    exact Submodule.subset_span ⟨i, Nat.lt_add_one _, rfl⟩
  have hsub : b₀ '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1} ⊆
      insert (b₀ i) (b₀ '' {k : Fin r | (k : ℕ) < i}) := by
    rintro _ ⟨k, hk, rfl⟩
    rcases (Nat.lt_add_one_iff.mp hk).lt_or_eq with h' | h'
    · exact Set.mem_insert_of_mem _ ⟨k, h', rfl⟩
    · rw [Fin.ext h']
      exact Set.mem_insert _ _
  have hmem' : b i ∈ Submodule.span Ω (insert (b₀ i) (b₀ '' {k : Fin r | (k : ℕ) < i})) :=
    Submodule.span_mono hsub hmem
  rw [Submodule.span_insert] at hmem'
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem'
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  refine ⟨a, gr_isGenAt L b b₀ p hL hF i a ?_⟩
  rw [← hyz, add_sub_cancel_left]
  exact hz

theorem zpow_ratio (Λ : Lat ξ Ω) (p : Cpt ξ) (s t : Ω) (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) (n : ℤ) :
    (t / s) ^ n ∈ regAt ξ p := by
  obtain ⟨hs0, hsp⟩ := hs
  obtain ⟨ht0, htp⟩ := ht
  have h1 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hsp, htp]
    exact Submodule.mem_span_singleton_self t
  have h2 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← htp, hsp]
    exact Submodule.mem_span_singleton_self s
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨a', ha'⟩ := Submodule.mem_span_singleton.mp h2
  have hts : t / s = a := by
    rw [div_eq_iff hs0]
    exact ha.symm
  have hst : s / t = a' := by
    rw [div_eq_iff ht0]
    exact ha'.symm
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, hts]
    exact pow_mem a.2 m
  · rw [zpow_negSucc, ← inv_pow, inv_div, hst]
    exact pow_mem a'.2 _

theorem tens_isGenAt {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs i).1, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro t ⟨s', hs', rfl⟩
    have hr : ∏ i, (s' i / s i) ^ a i ∈ regAt ξ p :=
      prod_mem fun i _ => zpow_ratio (Λ i) p (s i) (s' i) (hs i) (hs' i) (a i)
    refine Submodule.mem_span_singleton.mpr ⟨⟨_, hr⟩, ?_⟩
    show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_zpow, div_mul_cancel₀ _ (hs i).1]
  · exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨s, hs, rfl⟩)

theorem grTens_exists_gen {S : Type} [Fintype S] {r : S → ℕ} (L : S → Lat ξ E) (b₀ : ∀ σ, Fin (r σ) → E)
    (a : (Σ σ, Fin (r σ)) → ℤ) (T : Set (Cpt ξ)) (h : ∀ σ, (L σ).IsFlagVBOn T (b₀ σ)) (p : Cpt ξ) (hp : p ∈ T) :
    ∃ c, (Lat.grTens L b₀ a).IsGenAt p c := by
  have hq : ∀ q : Σ σ, Fin (r σ), ∃ c, ((L q.1).gr (b₀ q.1) q.2).IsGenAt p c :=
    fun q => exists_gen (L q.1) T (b₀ q.1) (h q.1) p hp q.2
  choose s hs using hq
  exact ⟨_, tens_isGenAt _ a p s hs⟩

def jPlane (Ω : Type) [Field Ω] : (Fin 2 → Ω) →+ (Fin 2 → RatFunc Ω) :=
  ((algebraMap Ω (RatFunc Ω)).toAddMonoidHom).compLeft (Fin 2)

theorem isGenericFlag_plane :
    IsGenericFlag (Ω := Ω) (Ω' := RatFunc Ω) (jPlane Ω) (S := Unit) (r := fun _ => 2) (fun _ => ⊤)
      (fun _ => ![![1, RatFunc.X], ![0, 1]]) 1 := by
  have hj : ∀ (v : Fin 2 → Ω) (m : Fin 2), jPlane Ω v m = algebraMap Ω (RatFunc Ω) (v m) :=
    fun _ _ => rfl
  have hU : ∀ (ι : Type) (hι : Unique ι) (x : ι → RatFunc Ω), x default = RatFunc.X →
      AlgebraicIndependent Ω x := by
    intro ι hι x hx
    rw [algebraicIndependent_unique_type_iff, hx]
    exact RatFunc.transcendental_X
  have key : ∀ K : IntermediateField Ω (RatFunc Ω), RatFunc.X ∈ K →
      Module.finrank K (RatFunc Ω) = 1 := by
    intro K hK
    have hK' : K = ⊤ := by
      rw [eq_top_iff, ← RatFunc.adjoin_X]
      exact IntermediateField.adjoin_simple_le_iff.mpr hK
    subst hK'
    exact IntermediateField.finrank_top
  refine ⟨fun _ => ⇑(Pi.basisFun Ω (Fin 2)), fun _ => !![1, 0; RatFunc.X, 1],
    fun _ => ⟨(Pi.basisFun Ω (Fin 2)).linearIndependent, (Pi.basisFun Ω (Fin 2)).span_eq⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.one_pos, ?_⟩
  · intro a e
    ext m
    simp [hj, map_mul]
  · intro _
    convert (Pi.basisFun (RatFunc Ω) (Fin 2)).linearIndependent using 1
    all_goals first
      | rfl
      | (ext k m
         fin_cases k <;> fin_cases m <;> simp [hj])
  · intro _
    refine LinearIndependent.pair_iff.mpr fun s t h => ?_
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    subst h0
    simpa using h1
  · intro _ k
    fin_cases k <;> simp
  · intro _ l k h
    fin_cases l <;> fin_cases k <;> simp at h ⊢
  · intro _ i
    congr 1
    ext k m
    fin_cases k <;> fin_cases m <;> simp [hj, Fin.sum_univ_two, Finset.sum_apply]
  · refine hU _ ?_ _ ?_
    · refine ⟨⟨⟨(), ⟨(1, 0), by decide⟩⟩⟩, ?_⟩
      rintro ⟨⟨⟩, ⟨⟨l, k⟩, h⟩⟩
      fin_cases l <;> fin_cases k <;> first | rfl | exact absurd h (by decide)
    · rfl
  · exact key _ (IntermediateField.subset_adjoin _ _ ⟨⟨(), (1, 0)⟩, by simp⟩)

theorem not_isGenericFlag_self {E' : Type} [AddCommGroup E'] [Module Ω E'] (j : E →+ E') (V : Unit → Submodule Ω E)
    (b₀ : Unit → Fin 2 → E') (d : ℕ) : ¬ IsGenericFlag (Ω' := Ω) j (r := fun _ => 2) V b₀ d := by
  rintro ⟨c, u, -, -, -, -, -, -, -, hai, -, -⟩
  exact hai.transcendental ⟨(), ⟨(1, 0), by decide⟩⟩ (isAlgebraic_algebraMap (R := Ω) (A := Ω) _)

end GlobalTheory.CompanionTheory.Ar.FlagModel
