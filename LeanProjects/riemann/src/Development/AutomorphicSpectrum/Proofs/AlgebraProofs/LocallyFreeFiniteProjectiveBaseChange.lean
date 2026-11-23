import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj

open GlobalTheory.CompanionTheory.Ar.Num TensorProduct

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {R : Subalgebra o Ω}
  {E : Type*} [AddCommGroup E] [Module Ω E]

theorem exists_pow_cover {k : ℕ} (f c : Fin k → R) (h : ∑ l, c l * f l = 1) (n : ℕ) :
    ∃ d : Fin k → R, ∑ l, d l * f l ^ n = 1 := by
  have h1 : Ideal.span (Set.range f) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← h]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have h2 := Ideal.span_pow_eq_top _ h1 n
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at h2
  exact h2

theorem exists_charts {r : ℕ} {L : Submodule R E} (h : LocFree R r L.toAddSubgroup) :
    ∃ (k : ℕ) (f c : Fin k → R) (B : Fin k → Module.Basis (Fin r) Ω E), ∑ l, c l * f l = 1 ∧
      (∀ l q, ∃ n : ℕ, (f l : Ω) ^ n • B l q ∈ L) ∧
      ∀ l q, ∀ e ∈ L, ∃ n : ℕ, (f l : Ω) ^ n * (B l).repr e q ∈ R := by
  classical
  obtain ⟨-, k, f, c, hf, hc, hs, hb⟩ := h
  choose b hli hsp hiff using hb
  refine ⟨k, fun l => ⟨f l, hf l⟩, fun l => ⟨c l, hc l⟩,
    fun l => Module.Basis.mk (hli l) (hsp l).ge, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simpa using hs
  · intro l q
    rw [Module.Basis.mk_apply]
    refine (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases hq : q' = q
      · subst hq; simp
      · simp [hq]
    · simp [Pi.single_apply]
  · intro l q e he
    obtain ⟨a, ha, rfl⟩ := (hiff l e).1 ⟨0, by simpa using he⟩
    obtain ⟨n, hn⟩ := ha q
    refine ⟨n, ?_⟩
    have : (Module.Basis.mk (hli l) (hsp l).ge).repr (∑ q, a q • b l q) q = a q := by
      have h2 : (∑ q, a q • b l q) = ∑ q, a q • (Module.Basis.mk (hli l) (hsp l).ge) q := by
        simp [Module.Basis.mk_apply]
      rw [h2, Module.Basis.repr_sum_self]
    rw [this]
    exact hn

theorem pow_smul_mem {L : Submodule R E} (f : R) {n m : ℕ} (hnm : n ≤ m) {e : E}
    (h : (f : Ω) ^ n • e ∈ L) : (f : Ω) ^ m • e ∈ L := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hnm
  have := L.smul_mem (f ^ j) h
  rw [pow_add, mul_smul]
  simpa [Subalgebra.smul_def] using this

theorem pow_mul_mem (f : R) {n m : ℕ} (hnm : n ≤ m) {a : Ω}
    (h : (f : Ω) ^ n * a ∈ R) : (f : Ω) ^ m * a ∈ R := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hnm
  rw [pow_add, mul_assoc]
  exact R.mul_mem (R.pow_mem f.2 j) h

theorem expand {k r : ℕ} (f d : Fin k → R) (B : Fin k → Module.Basis (Fin r) Ω E) (M N : ℕ)
    (hd : ∑ l, d l * f l ^ (M + N) = 1) (e : E) :
    ∑ i : Fin k × Fin r, ((d i.1 : Ω) * ((f i.1 : Ω) ^ M * (B i.1).repr e i.2)) •
      ((f i.1 : Ω) ^ N • B i.1 i.2) = e := by
  have hd' : ∑ l, (d l : Ω) * (f l : Ω) ^ (M + N) = 1 := by
    simpa using congrArg Subtype.val hd
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [← one_smul Ω e, ← hd', Finset.sum_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← (B l).sum_repr e, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  ring

theorem exists_dualBasis {r : ℕ} {L : Submodule R E} (h : LocFree R r L.toAddSubgroup) :
    ∃ (k : ℕ) (φ : Fin k × Fin r → Module.Dual Ω E) (v : Fin k × Fin r → L),
      (∀ i, ∀ e ∈ L, φ i e ∈ R) ∧ ∀ e, ∑ i, φ i e • (v i : E) = e := by
  classical
  obtain ⟨k, f, c, B, hs, h1, h2⟩ := exists_charts h
  choose n hn using h1
  obtain ⟨N, hN⟩ : ∃ N, ∀ l q, n l q ≤ N := by
    obtain ⟨N, hN⟩ := (Set.finite_range fun i : Fin k × Fin r => n i.1 i.2).bddAbove
    exact ⟨N, fun l q => hN ⟨(l, q), rfl⟩⟩
  let v : Fin k × Fin r → L := fun i =>
    ⟨(f i.1 : Ω) ^ N • B i.1 i.2, pow_smul_mem _ (hN _ _) (hn _ _)⟩

  have hspan : ∀ e ∈ L, e ∈ Submodule.span R (Set.range fun i => (v i : E)) := by
    intro e he
    choose m hm using fun l q => h2 l q e he
    obtain ⟨M, hM⟩ := (Set.finite_range fun i : Fin k × Fin r => m i.1 i.2).bddAbove
    obtain ⟨d, hd⟩ := exists_pow_cover f c hs (M + N)
    rw [← expand f d B M N hd e]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hR : (d i.1 : Ω) * ((f i.1 : Ω) ^ M * (B i.1).repr e i.2) ∈ R :=
      R.mul_mem (d i.1).2 (pow_mul_mem _ (hM ⟨i, rfl⟩) (hm _ _))
    exact Submodule.smul_mem _ (⟨_, hR⟩ : R) (Submodule.subset_span ⟨i, rfl⟩)
  choose m hm using fun (i j : Fin k × Fin r) => h2 i.1 i.2 (v j) (v j).2
  obtain ⟨M, hM⟩ := (Set.finite_range fun i : (Fin k × Fin r) × (Fin k × Fin r) =>
    m i.1 i.2).bddAbove
  obtain ⟨d, hd⟩ := exists_pow_cover f c hs (M + N)
  refine ⟨k, fun i => ((d i.1 : Ω) * (f i.1 : Ω) ^ M) • (B i.1).coord i.2, v, ?_, ?_⟩
  · intro i e he
    have he' := hspan e he
    clear he
    induction he' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      have := R.mul_mem (d i.1).2 (pow_mul_mem _ (hM ⟨(i, j), rfl⟩) (hm i j))
      simpa [mul_assoc] using this
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact R.add_mem hx hy
    | smul a x _ hx =>
      rw [Subalgebra.smul_def, map_smul]
      exact R.mul_mem a.2 hx
  · intro e
    simpa [mul_assoc, v] using expand f d B M N hd e

section DualBasis

variable {ι : Type*} [Fintype ι] {L : Submodule R E} (φ : ι → Module.Dual Ω E) (v : ι → L)
  (hφ : ∀ i, ∀ e ∈ L, φ i e ∈ R) (hv : ∀ e, ∑ i, φ i e • (v i : E) = e)

include hφ hv

theorem sum_eq (x : L) : ∑ i, (⟨φ i x, hφ i x x.2⟩ : R) • v i = x := by
  apply Subtype.ext
  simpa [Subalgebra.smul_def] using hv x

theorem finite_projective : Module.Finite R L ∧ Module.Projective R L := by
  classical
  let s : L →ₗ[R] (ι → R) :=
    { toFun := fun x i => ⟨φ i x, hφ i x x.2⟩
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp [Subalgebra.smul_def] }
  let p : (ι → R) →ₗ[R] L := Fintype.linearCombination R v
  have hps : p ∘ₗ s = LinearMap.id := by
    ext1 x
    exact sum_eq φ v hφ hv x
  exact ⟨Module.Finite.of_surjective p fun x => ⟨s x, LinearMap.congr_fun hps x⟩,
    Module.Projective.of_split s p hps⟩

theorem isBaseChange : IsBaseChange Ω L.subtype := by
  let g : E →ₗ[Ω] Ω ⊗[R] L := ∑ i, (φ i).smulRight ((1 : Ω) ⊗ₜ[R] v i)
  have hg : ∀ e, g e = ∑ i, φ i e • ((1 : Ω) ⊗ₜ[R] v i) := by
    intro e
    simp [g]
  refine IsBaseChange.of_equiv (LinearEquiv.ofLinear (L.subtype.liftBaseChange Ω) g ?_ ?_) ?_
  · ext1 e
    simp [hg, hv]
  · ext x
    have : g x = (1 : Ω) ⊗ₜ[R] x := by
      rw [hg]
      conv_rhs => rw [← sum_eq φ v hφ hv x, tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tmul_smul]
      rfl
    simpa using this
  · intro x
    simp

end DualBasis

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type}
    [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), LocFree R r L.toAddSubgroup →
      Module.Finite R L ∧ Module.Projective R L ∧ Module.finrank Ω E = r ∧
        IsBaseChange Ω L.subtype := by
  intro o Ω _ _ _ R E _ _ r L h
  obtain ⟨k, φ, v, hφ, hv⟩ := exists_dualBasis h
  refine ⟨(finite_projective φ v hφ hv).1, (finite_projective φ v hφ hv).2, ?_,
    isBaseChange φ v hφ hv⟩
  obtain ⟨k, f, c, B, hs, -⟩ := exists_charts h
  rcases k with _ | k
  · simp at hs
  · simpa using Module.finrank_eq_card_basis (B 0)

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj
