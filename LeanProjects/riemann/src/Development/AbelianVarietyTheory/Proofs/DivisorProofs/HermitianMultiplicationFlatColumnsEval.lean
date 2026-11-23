import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsMemFiltrationLatti

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort.ColEval

theorem word_succ {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) {t : ℕ} (u : Fin (t + 1) → Fin N → K) :
    word mul u = mul (u 0) * word mul (fun i => u i.succ) := by
  simp [word, List.ofFn_succ]

theorem mul_eq_sum {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (v : Fin N → K) :
    mul v = ∑ k, v k • mul (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_smul]
  congr 1
  ext j
  simp [Pi.single_apply]

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A]
  [IsScalarTower (𝓞 F) F A] {S : Sys F A} {E A' : Type} [Field E] [Algebra F E] [AddCommGroup A'] [Module E A']
  {s : Fin S.D → Fin S.N → E} {δ : ℕ}

theorem mul_single_ι (Φ : S.Flat E A' s δ) (k : Fin S.N) (y : A) :
    Φ.mul (Pi.single k 1) (Φ.ι y) = Φ.ι (S.mul (Pi.single k 1) y) := by
  rw [← Φ.mul_ι]
  congr 2
  ext j
  by_cases h : j = k
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem word_ι_expand (Φ : S.Flat E A' s δ) : ∀ (t : ℕ) (U : Fin t → Fin S.N → E) (z : A),
    word Φ.mul U (Φ.ι z) =
      ∑ e : Fin t → Fin S.N, (∏ q, U q (e q)) • Φ.ι (word S.mul (fun q => Pi.single (e q) (1 : F)) z)
  | 0, U, z => by simp [word]
  | t + 1, U, z => by
    rw [word_succ, Module.End.mul_apply, word_ι_expand Φ t, map_sum]
    rw [← (Fin.consEquiv fun _ : Fin (t + 1) => Fin S.N).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, word_succ,
      Module.End.mul_apply, map_smul, mul_eq_sum Φ.mul (U 0), LinearMap.sum_apply, LinearMap.smul_apply,
      mul_single_ι, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun e _ => ?_
    rw [mul_comm]

end GlobalTheory.HSShort.ColEval

namespace GlobalTheory.HSShort.ColEval

theorem columns_eval : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∃ c' : Fin d → A' →ₗ[E] E, (∀ x ∈ Submodule.span E (Φ.ι '' S.V S.T), ∑ i, c' i x • Φ.ι (b i) = x) ∧ ∀ (κ : S.Col) (u : Fin (S.D + 1) × Fin S.N → E), word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x) ∈ Submodule.span E (Φ.ι '' S.V S.T) ∧ ∀ i, aeval u (coordP S.mul (c i) κ.β (κ.x : A)) = c' i (word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x)) := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d b c hc
  set W := Submodule.span E (Φ.ι '' (S.V S.T : Set A)) with hW
  have hli : LinearIndependent E (fun i => Φ.ι (b i)) := Φ.indep d b b.linearIndependent
  have hιV : ∀ (y : A) (hy : y ∈ S.V S.T), Φ.ι y = ∑ i, algebraMap F E (b.repr ⟨y, hy⟩ i) • Φ.ι (b i) := by
    intro y hy
    conv_lhs => rw [show y = ((⟨y, hy⟩ : S.V S.T) : A) from rfl, ← b.sum_repr ⟨y, hy⟩]
    rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, LinearMap.map_smulₛₗ]
  have hWspan : W = Submodule.span E (Set.range fun i => Φ.ι (b i)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [hιV y hy]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨b i, (b i).2, rfl⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((Finsupp.linearEquivFunOnFinite E E (Fin d)).toLinearMap ∘ₗ (hli.repr ∘ₗ Submodule.inclusion (le_of_eq hWspan)))
  have h1 : ∀ x ∈ W, ∑ i, g x i • Φ.ι (b i) = x := by
    intro x hx
    have hx' : x ∈ Submodule.span E (Set.range fun i => Φ.ι (b i)) := hWspan ▸ hx
    have e1 := LinearMap.congr_fun hg ⟨x, hx⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe] at e1
    rw [e1, show Submodule.inclusion (le_of_eq hWspan) ⟨x, hx⟩ = ⟨x, hx'⟩ from rfl]
    have e2 := hli.linearCombination_repr ⟨x, hx'⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e2
    simpa using e2
  have h2 : ∀ x ∈ W, ∀ a : Fin d → E, ∑ i, a i • Φ.ι (b i) = x → ∀ i, g x i = a i := by
    intro x hx a ha
    have h0 : ∑ i, (g x i - a i) • Φ.ι (b i) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h1 x hx, ha, sub_self]
    intro i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)
  have h3 : ∀ (y : A) (hy : y ∈ S.V S.T) i, g (Φ.ι y) i = algebraMap F E (c i y) := by
    intro y hy i
    rw [h2 _ (Submodule.subset_span ⟨y, hy, rfl⟩) _ (hιV y hy).symm i]
    congr 1
    exact (hc i ⟨y, hy⟩).symm
  refine ⟨fun i => LinearMap.proj i ∘ₗ g, fun x hx => h1 x hx, fun κ u => ?_⟩
  have hmem : ∀ e : Fin κ.t → Fin S.N, word S.mul (fun q => Pi.single (e q) (1 : F)) (κ.x : A) ∈ S.V S.T := by
    intro e
    have := (GlobalTheory.HSShort.wordMem F A S hS κ.j κ.t (by rw [κ.add])).1 (fun q => Pi.single (e q) (1 : F)) κ.x κ.x.2
    rwa [κ.add] at this
  rw [word_ι_expand Φ κ.t]
  refine ⟨Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hmem e, rfl⟩), fun i => ?_⟩
  simp only [coordP, map_sum, map_mul, aeval_C, map_prod, aeval_X, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.map_smul, LinearMap.coe_proj, Function.eval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [h3 _ (hmem e) i, mul_comm]

end GlobalTheory.HSShort.ColEval
