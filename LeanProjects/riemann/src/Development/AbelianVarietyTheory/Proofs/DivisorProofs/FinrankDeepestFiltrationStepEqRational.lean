import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsMemFiltrationLattiStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort.DeepStep

theorem ofFn_prod_induct {M : Type} [Monoid M] (p : M → ℕ → Prop) (h1 : p 1 0)
    (hmul : ∀ a b k l, p a k → p b l → p (a * b) (k + l)) :
    ∀ (n : ℕ) (g : Fin n → M) (k : Fin n → ℕ), (∀ i, p (g i) (k i)) → p (List.ofFn g).prod (∑ i, k i) := by
  intro n
  induction n with
  | zero => intro g k _; simpa using h1
  | succ n ih =>
    intro g k hg
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact hmul _ _ _ _ (hg 0) (ih _ _ fun i => hg i.succ)

theorem pow_induct {M : Type} [Monoid M] (p : M → ℕ → Prop) (h1 : p 1 0)
    (hmul : ∀ a b k l, p a k → p b l → p (a * b) (k + l)) (a : M) (ha : p a 1) : ∀ n, p (a ^ n) n := by
  intro n
  induction n with
  | zero => simpa using h1
  | succ n ih => rw [pow_succ]; exact hmul _ _ _ _ ih ha

section Inter

variable {F E A A' : Type} [Field F] [Field E] [Algebra F E] [AddCommGroup A] [Module F A] [AddCommGroup A'] [Module E A']
  (ι : A →ₛₗ[algebraMap F E] A')

theorem ofFn_prod_comm : ∀ (n : ℕ) (g' : Fin n → Module.End E A') (g : Fin n → Module.End F A),
    (∀ i x, g' i (ι x) = ι (g i x)) → ∀ x, (List.ofFn g').prod (ι x) = ι ((List.ofFn g).prod x) := by
  intro n
  induction n with
  | zero => intro g' g _ x; simp
  | succ n ih =>
    intro g' g hg x
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply,
      ih _ _ (fun i => hg i.succ), hg 0]

theorem pow_comm (f' : Module.End E A') (f : Module.End F A) (h : ∀ x, f' (ι x) = ι (f x)) :
    ∀ (n : ℕ) x, (f' ^ n) (ι x) = ι ((f ^ n) x) := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, h, ih]

theorem mem_span_image (Y : Set A) : ∀ y ∈ Submodule.span F Y, ι y ∈ Submodule.span E (ι '' Y) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

end Inter

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A]

def Up (S : Sys F A) (f : Module.End F A) (k : ℕ) : Prop := ∀ j, j + k ≤ S.T → ∀ x ∈ S.V j, f x ∈ S.V (j + k)

theorem up_one (S : Sys F A) : Up S 1 0 := fun j _ x hx => by simpa using hx

theorem up_mul (S : Sys F A) : ∀ a b k l, Up S a k → Up S b l → Up S (a * b) (k + l) := by
  intro a b k l ha hb j hj x hx
  have h1 := hb j (by omega) x hx
  have h2 := ha (j + l) (by omega) _ h1
  rw [Module.End.mul_apply]
  have e : j + (k + l) = j + l + k := by omega
  rw [e]; exact h2

theorem up_mul_gen (S : Sys F A) (hS : S.Hyp) (u : Fin S.N → F) : Up S (S.mul u) 1 := by
  intro j hj x hx
  have := (GlobalTheory.T.productOfVectorMultiplications_mem_filtration_lattice F A S hS j 1 hj).1 (fun _ => u) x hx
  simpa [word] using this

theorem up_pw (S : Sys F A) (hS : S.Hyp) (s : Fin S.D → Fin S.N → F) (α : Fin S.D →₀ ℕ) :
    Up S (pw S.mul s α) α.degree := by
  rw [Finsupp.degree_eq_sum]
  exact ofFn_prod_induct (Up S) (up_one S) (up_mul S) S.D _ _
    fun i => pow_induct (Up S) (up_one S) (up_mul S) _ (up_mul_gen S hS (s i)) (α i)

end GlobalTheory.HSShort.DeepStep

open GlobalTheory.HSShort.DeepStep in

theorem GlobalTheory.HSShort.deepStep_finrank : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → F) (δ : ℕ) (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ), FiniteDimensional E (Φ.U (S.T - S.D)) ∧ Module.finrank E (Φ.U (S.T - S.D)) = S.deepRank s ∧ S.deepRank s ≤ Module.finrank F (S.V S.T) := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ
  set P : Submodule F A := ⨆ α : MonoDeg (Fin S.D) (S.T - S.D), (S.V S.D).map (pw S.mul s α.1) with hP
  have hle := hS.le_T
  have hPT : P ≤ S.V S.T := iSup_le fun α => by
    rintro _ ⟨x, hx, rfl⟩
    have h := up_pw S hS s α.1 S.D (by rw [α.2]; omega) x hx
    have e : S.D + α.1.degree = S.T := by rw [α.2]; omega
    rw [e] at h
    exact h
  haveI : FiniteDimensional F (S.V S.T) := by
    obtain ⟨r, b, -⟩ := hS.shortT
    exact Module.Finite.of_basis b
  haveI : FiniteDimensional F P := Submodule.finiteDimensional_of_le hPT
  have hdeep : S.deepRank s = Module.finrank F P := rfl
  let b := Module.finBasis F P
  let v : Fin (Module.finrank F P) → A := fun i => (b i : A)
  have hv : Submodule.span F (Set.range v) = P := by
    have : Set.range v = (P.subtype) '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hli : LinearIndependent E (fun i => Φ.ι (v i)) := by
    refine Φ.indep _ (fun i => (⟨v i, hPT (b i).2⟩ : S.V S.T)) ?_
    refine LinearIndependent.of_comp (S.V S.T).subtype ?_
    exact b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  have hcomm : ∀ (α : Fin S.D →₀ ℕ) (x : A),
      pw Φ.mul (fun i k => algebraMap F E (s i k)) α (Φ.ι x) = Φ.ι (pw S.mul s α x) := fun α x =>
    ofFn_prod_comm Φ.ι _ _ _ (fun i y => pow_comm Φ.ι _ _ (fun z => Φ.mul_ι (s i) z) (α i) y) x
  have hU : Φ.U (S.T - S.D) = Submodule.span E (Set.range fun i => Φ.ι (v i)) := by
    rw [Φ.div]
    apply le_antisymm
    · refine iSup_le fun α => ?_
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, hcomm]
      have h1 : pw S.mul s α.1 x ∈ P := Submodule.mem_iSup_of_mem α ⟨x, hx, rfl⟩
      rw [← hv] at h1
      have h2 := mem_span_image Φ.ι _ _ h1
      rwa [← Set.range_comp] at h2
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hvi : v i ∈ P := (b i).2
      exact Submodule.iSup_induction (fun α : MonoDeg (Fin S.D) (S.T - S.D) => (S.V S.D).map (pw S.mul s α.1))
        (motive := fun y => Φ.ι y ∈ ⨆ α : MonoDeg (Fin S.D) (S.T - S.D),
          (Submodule.span E (Φ.ι '' S.V S.D)).map (pw Φ.mul (fun i k => algebraMap F E (s i k)) α.1)) hvi
        (fun α y hy => by
          obtain ⟨x, hx, rfl⟩ := hy
          rw [← hcomm]
          exact Submodule.mem_iSup_of_mem α (Submodule.mem_map_of_mem (Submodule.subset_span ⟨x, hx, rfl⟩)))
        (by simp only [map_zero]; exact zero_mem _)
        (fun y z hy hz => by simp only [map_add]; exact add_mem hy hz)
  refine ⟨?_, ?_, ?_⟩
  · rw [hU]; exact FiniteDimensional.span_of_finite E (Set.finite_range _)
  · rw [hU, finrank_span_eq_card hli, Fintype.card_fin, hdeep]
  · rw [hdeep]; exact Submodule.finrank_mono hPT
