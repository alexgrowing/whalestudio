import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivAt0CompMem

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open scoped ContDiff

namespace GlobalTheory.Glob.JetChainLin

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem prod_pow_eq {σ M : Type} [CommMonoid M] (F : σ → M) (e : σ →₀ ℕ) {n : ℕ} (f : Fin n → σ)
    (hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset σ)) :
    (e.prod fun k n => F k ^ n) = ∏ i, F (f i) := by
  classical
  have h1 : ((Finsupp.toMultiset e).map F).prod = e.prod fun k n => F k ^ n := by
    rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index]
    · intro _; simp
    · intro _ _ _; rw [pow_add]
  rw [← h1, hm, Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn]
  rfl

theorem monomial_eq_prod {σ : Type} (e : σ →₀ ℕ) {n : ℕ} (f : Fin n → σ)
    (hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset σ)) :
    (MvPolynomial.monomial e (1 : ℂ)) = ∏ i, MvPolynomial.X (f i) := by
  rw [MvPolynomial.monomial_eq, prod_pow_eq (fun k => (MvPolynomial.X k : MvPolynomial σ ℂ)) e f hm]
  simp

theorem derivAt0_eq (G : VCx ι a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) (e : DVar ι a b →₀ ℕ) {n : ℕ}
    (f : Fin n → DVar ι a b) (hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset (DVar ι a b))) :
    iteratedFDeriv ℂ n G 0 (fun i => coordX (f i)) = derivAt0 G e := by
  classical
  have hG' : ContDiff ℂ ∞ G := contDiff_infty.2 hG
  have hc : (Finsupp.toMultiset e).card = n := by rw [hm]; simp
  have p : ((List.ofFn f).map coordX).Perm ((Finsupp.toMultiset e).toList.map coordX) := by
    refine List.Perm.map _ ?_
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, hm]
  have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.cml_perm p n (iteratedFDeriv ℂ _ G 0)
    (fun v σ => ReciprocityTheory.L2DbarEstimates.Y.zd_iteratedFDeriv_comp_perm isOpen_univ hG'.contDiffOn _ 0 trivial σ v)
    (by simp) (by simp [hc])
  have h3 : ∀ (n n' : ℕ) (h : n = n') (v : Fin n → VCx ι a b) (w : Fin n' → VCx ι a b), (∀ i, v i = w (i.cast h)) →
      iteratedFDeriv ℂ n G 0 v = iteratedFDeriv ℂ n' G 0 w := by
    intro n n' h v w hvw
    subst h
    exact congrArg _ (funext hvw)
  unfold derivAt0
  refine Eq.trans (congrArg _ (funext fun i => ?_)) (h2.trans (h3 _ _ hc.symm _ _ fun i => ?_))
  · simp
  · simp

theorem jetC_eq (cD : ι → ℂ) (G : VCx ι a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) (e : DVar ι a b →₀ ℕ) {n : ℕ}
    (f : Fin n → DVar ι a b) (hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset (DVar ι a b))) :
    jetC cD G e = (∏ i, cD (f i).1) * iteratedFDeriv ℂ n G 0 (fun i => coordX (f i)) := by
  rw [derivAt0_eq G hG e f hm, jetC, prod_pow_eq (fun k : DVar ι a b => cD k.1) e f hm]

theorem constr_prod_X (cD : ι → ℂ) (G : VCx ι a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) {n : ℕ}
    (f : Fin n → DVar ι a b) :
    (MvPolynomial.basisMonomials (DVar ι a b) ℂ).constr ℂ (jetC cD G) (∏ i, MvPolynomial.X (f i)) =
      (∏ i, cD (f i).1) * iteratedFDeriv ℂ n G 0 (fun i => coordX (f i)) := by
  classical
  have hm : Finsupp.toMultiset (Multiset.toFinsupp (↑(List.ofFn f) : Multiset (DVar ι a b))) =
      (↑(List.ofFn f) : Multiset (DVar ι a b)) := Multiset.toFinsupp_toMultiset _
  rw [← monomial_eq_prod _ f hm, ← jetC_eq cD G hG _ f hm]
  have := (MvPolynomial.basisMonomials (DVar ι a b) ℂ).constr_basis ℂ (jetC cD G)
    (Multiset.toFinsupp (↑(List.ofFn f) : Multiset (DVar ι a b)))
  rwa [MvPolynomial.coe_basisMonomials] at this

noncomputable def subst (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) :
    VCx ι a b →ₗ[ℂ] VCx ι a b where
  toFun z := fun τ i j => ∑ k : Fin b, ∑ l : Fin a, h τ i k * z τ k l * g τ l j
  map_add' z w := by
    funext τ i j
    simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c z := by
    funext τ i j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring

omit [Fintype ι] in
theorem subst_coordX (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) (k : DVar ι a b) :
    subst g h (coordX k) =
      ∑ p : Fin b × Fin a, (h k.1 p.1 k.2.1 * g k.1 k.2.2 p.2) • coordX (k.1, p.1, p.2) := by
  classical
  obtain ⟨t, k, l⟩ := k
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change ∑ k' : Fin b, ∑ l' : Fin a, h τ i k' * coordX (t, k, l) τ k' l' * g τ l' j = _
  by_cases hτ : τ = t
  · subst hτ
    rw [Finset.sum_eq_single (i, j), Finset.sum_eq_single k, Finset.sum_eq_single l]
    · simp [coordX]
    · intro l' _ hl; simp [coordX, hl]
    · simp
    · intro k' _ hk; simp [coordX, hk]
    · simp
    · rintro ⟨i', j'⟩ _ hne
      have : ¬ (i = i' ∧ j = j') := by
        rintro ⟨rfl, rfl⟩
        exact hne rfl
      simp [coordX, this]
    · simp
  · simp [coordX, hτ]

theorem jetC_comp_subst : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (cD : ι → ℂ) (G : VCx ι a b → ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ), (∀ k : ℕ, ContDiff ℂ k G) → ∀ m : DVar ι a b →₀ ℕ, jetC cD (fun z : VCx ι a b => G (fun τ i j => ∑ k : Fin b, ∑ l : Fin a, h τ i k * z τ k l * g τ l j)) m = (MvPolynomial.basisMonomials (DVar ι a b) ℂ).constr ℂ (jetC cD G) (MvPolynomial.aeval (fun k : DVar ι a b => ∑ i : Fin b, ∑ j : Fin a, (MvPolynomial.C (h k.1 i k.2.1 * g k.1 k.2.2 j) * MvPolynomial.X (k.1, i, j) : MvPolynomial (DVar ι a b) ℂ)) (MvPolynomial.monomial m (1 : ℂ))) := by
  intro ι _ a b cD G g h hG m
  classical
  let T : VCx ι a b →L[ℂ] VCx ι a b := LinearMap.toContinuousLinearMap (subst g h)
  have h1 : (fun z : VCx ι a b => G (fun τ i j => ∑ k : Fin b, ∑ l : Fin a, h τ i k * z τ k l * g τ l j)) =
      G ∘ T := rfl
  have hm : Finsupp.toMultiset m = (↑(List.ofFn (Finsupp.toMultiset m).toList.get) : Multiset (DVar ι a b)) := by
    rw [List.ofFn_get, Multiset.coe_toList]
  generalize (Finsupp.toMultiset m).toList.get = f at hm
  rw [h1, jetC_eq cD (G ∘ T) (fun k => (hG k).comp T.contDiff) m f hm, monomial_eq_prod m f hm,
    T.iteratedFDeriv_comp_right (hG _) 0 le_rfl, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    map_prod]
  have h2 : (fun i => T (coordX (f i))) = fun i =>
      ∑ p : Fin b × Fin a, (h (f i).1 p.1 (f i).2.1 * g (f i).1 (f i).2.2 p.2) • coordX ((f i).1, p.1, p.2) :=
    funext fun i => subst_coordX g h (f i)
  rw [h2, ContinuousMultilinearMap.map_sum, Finset.mul_sum]
  simp only [MvPolynomial.aeval_X, ← Fintype.sum_prod_type']
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, ← MvPolynomial.smul_eq_C_mul, map_smul,
    constr_prod_X cD G hG (fun i => ((f i).1, (r i).1, (r i).2)), ContinuousMultilinearMap.map_smul_univ]
  simp only [smul_eq_mul]
  ring

end GlobalTheory.Glob.JetChainLin
