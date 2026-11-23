import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestDecompProved
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.StructureSheafH2BaseChange

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G

section CMap

variable {K L σ : Type} [CommRing K] [CommRing L] (f : K →+ L)

theorem cmap_add (y z : MvPolynomial σ K) : cmap f (y + z) = cmap f y + cmap f z := by
  ext m; simp only [coeff_add, coeff_cmap, map_add]

theorem cmap_zero : cmap f (0 : MvPolynomial σ K) = 0 := by
  ext m; simp only [coeff_cmap, coeff_zero, map_zero]

theorem cmap_neg (y : MvPolynomial σ K) : cmap f (-y) = -cmap f y := by
  ext m; simp only [coeff_cmap, coeff_neg, map_neg]

theorem cmap_monomial (n : σ →₀ ℕ) (c : K) : cmap f (monomial n c) = monomial n (f c) := by
  classical
  ext m
  rw [coeff_cmap, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

def cmapHom : MvPolynomial σ K →+ MvPolynomial σ L where
  toFun := cmap f
  map_zero' := cmap_zero f
  map_add' := cmap_add f

theorem X_mul_monomial' (v : σ) (n : σ →₀ ℕ) (c : K) :
    (X v : MvPolynomial σ K) * monomial n c = monomial (Finsupp.single v 1 + n) c := by
  rw [X, monomial_mul, one_mul]

theorem cmap_X_pderiv (v w : σ) (y : MvPolynomial σ K) :
    cmap f (X v * pderiv w y) = X v * pderiv w (cmap f y) := by
  classical
  induction y using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [pderiv_monomial, cmap_monomial, pderiv_monomial, X_mul_monomial', X_mul_monomial', cmap_monomial]
    congr 1
    rw [mul_comm c, mul_comm (f c)]
    have e1 : ((n w : ℕ) : K) * c = (n w) • c := (nsmul_eq_mul _ _).symm
    have e2 : ((n w : ℕ) : L) * f c = (n w) • f c := (nsmul_eq_mul _ _).symm
    rw [e1, e2, map_nsmul]
  | add p q hp hq =>
    rw [map_add, mul_add, cmap_add, hp, hq, cmap_add, map_add, mul_add]

end CMap

section Fun

variable {O : Type} [CommRing O] [IsDomain O] {p : ℕ} [Fact p.Prime] (f : KK O →+ ℚ_[p])

theorem cmap_glAct {N r : ℕ} (LL : ChainLetters N) (j : ℕ) (c d : Fin r) (y : MvPolynomial (Fin N × Fin r) (KK O)) :
    cmap f (glAct (KK O) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d y) =
      Formalism.GM.M.glAct p (gmL LL) j c d (cmap f y) := by
  unfold Formalism.MainNotions.G.glAct Formalism.GM.M.glAct
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  show cmapHom f _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show cmap f _ = _
  by_cases hi : (i : ℕ) < j
  · have hi' : i ∈ {i : Fin N | (i : ℕ) < j} := hi
    rw [if_pos hi', if_pos hi]
    by_cases hv : LL.vec i = true
    · have hv' : (gmL LL).vec i = true := hv
      have hv'' : (⟨LL.vec⟩ : Letters (Fin N)).vec i = true := hv
      rw [if_pos hv'', if_pos hv']
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply]
      exact cmap_X_pderiv f _ _ y
    · have hv' : ¬ (gmL LL).vec i = true := hv
      have hv'' : ¬ (⟨LL.vec⟩ : Letters (Fin N)).vec i = true := hv
      rw [if_neg hv'', if_neg hv']
      simp only [LinearMap.neg_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply]
      rw [cmap_neg]
      exact congrArg Neg.neg (cmap_X_pderiv f _ _ y)
  · have hi' : i ∉ {i : Fin N | (i : ℕ) < j} := hi
    rw [if_neg hi', if_neg hi]
    simp only [LinearMap.zero_apply]
    exact cmap_zero f

theorem cmap_support_subset {σ : Type} (y : MvPolynomial σ (KK O)) : (cmap f y).support ⊆ y.support := by
  intro m hm
  rw [mem_support_iff] at hm ⊢
  intro h0
  apply hm
  rw [coeff_cmap, h0, map_zero]

theorem sk_ycond_stable {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) (Mt : WithTop ℤ) (c d : Fin r) :
    ∀ x ∈ Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt,
      glAct (KK O) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d x ∈ Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt := by
  unfold Formalism.MainNotions.G.YCond
  intro x hx
  have : sSup {S : Submodule (KK O) (MvPolynomial (Fin N × Fin r) (KK O)) |
      S ≤ restrictSupport (KK O) {m : Fin N × Fin r →₀ ℕ | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧
        chStable (KK O) LL j S} ≤
      (sSup {S : Submodule (KK O) (MvPolynomial (Fin N × Fin r) (KK O)) |
      S ≤ restrictSupport (KK O) {m : Fin N × Fin r →₀ ℕ | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧
        chStable (KK O) LL j S}).comap (glAct (KK O) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d) :=
    sSup_le fun S hS x hx => le_sSup hS (hS.2 c d x hx)
  exact this hx

theorem sk_ycond_supp {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) (Mt : WithTop ℤ) :
    Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt ≤
      restrictSupport (KK O) {m : Fin N × Fin r →₀ ℕ | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} :=
  sSup_le fun _ hS => hS.1

theorem cmap_mem_restrictSupport {σ : Type} {s : Set (σ →₀ ℕ)} (y : MvPolynomial σ (KK O))
    (hy : y ∈ restrictSupport (KK O) s) : cmap f y ∈ restrictSupport ℚ_[p] s := by
  rw [mem_restrictSupport_iff] at hy ⊢
  exact (Finset.coe_subset.2 (cmap_support_subset f y)).trans hy

theorem cmap_ycond (ι : ℚ_[p] →+* KK O) (_hf : ∀ (a : ℚ_[p]) (x : KK O), f (ι a * x) = a * f x)
    {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) (Mt : WithTop ℤ)
    (y : MvPolynomial (Fin N × Fin r) (KK O)) (hy : y ∈ Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt) :
    cmap f y ∈ Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt := by
  set S' : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    Submodule.span ℚ_[p] (cmap f '' (Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt : Set _)) with hS'
  have h1 : S' ≤ restrictSupport ℚ_[p] {m | ((Formalism.GM.M.wt (gmL LL) j 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    rw [hS', Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact cmap_mem_restrictSupport f z (sk_ycond_supp LL j Mt hz)
  have h2 : Formalism.GM.M.GlStable p (gmL LL) j S' := by
    intro c d x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      rw [← cmap_glAct]
      exact Submodule.subset_span ⟨_, sk_ycond_stable LL j Mt c d z hz, rfl⟩
    | zero => rw [map_zero]; exact S'.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact S'.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact S'.smul_mem a hx
  have h3 : S' ≤ Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt := by
    unfold Formalism.GM.M.YCond
    exact le_sSup ⟨h1, h2⟩
  exact h3 (Submodule.subset_span ⟨y, hy, rfl⟩)

end Fun

theorem restFunY_proved : RestFunY := by
  intro O _ _ p _ ι N r _ LL q J M f hf y hy
  obtain ⟨hP, hC⟩ := hy
  refine ⟨cmap_mem_restrictSupport f y hP, ?_⟩
  have hC' : y ∈ ⨅ k, Formalism.MainNotions.G.YCond (KK O) (r := r) LL (J k) (M k) := hC
  show cmap f y ∈ ⨅ k, Formalism.GM.M.YCond p (r := r) (gmL LL) (J k) (M k)
  rw [Submodule.mem_iInf] at hC' ⊢
  exact fun k => cmap_ycond f ι hf LL (J k) (M k) y (hC' k)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
