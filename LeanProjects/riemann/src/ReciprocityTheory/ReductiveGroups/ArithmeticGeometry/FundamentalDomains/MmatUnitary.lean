import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PerpSpanRight

namespace ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (p : ℕ) (f g : Fin n → Fin r → ℂ)

def eps (k : Fin n) : ℂ := if (k : ℕ) < p then 1 else -1

def Mmat : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => (if a = b then 1 else 0) +
    ∑ k, (eps p k * (g k - f k) a) * ∑ m, τ (G b m) * conj (f k m)

theorem eps_sq (k : Fin n) : eps p k * eps p k = 1 := by
  unfold eps
  split_ifs <;> norm_num

theorem Mmat_mulVec (v : Fin r → ℂ) :
    Mmat τ G p f g *ᵥ v = v + ∑ k, (eps p k * hermC τ G v (f k)) • (g k - f k) := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Mmat, Matrix.of_apply, add_mul, Finset.sum_add_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, hermC, Pi.sub_apply]
  congr 1
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m _ => ?_
  ring

private lemma hermC_add_left' (u u' v : Fin r → ℂ) :
    hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := by
  unfold hermC
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma hermC_add_right_fundamental_domains' (u v v' : Fin r → ℂ) :
    hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  unfold hermC
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

private lemma hermC_sum_smul_left {m : ℕ} (c : Fin m → ℂ) (q : Fin m → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ k, c k • q k) v = ∑ k, c k * hermC τ G (q k) v := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ k, ∑ b, c k * q k a * τ (G a b) * conj (v b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, c k * q k a * τ (G a b) * conj (v b) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

private lemma hermC_sum_smul_right {m : ℕ} (u : Fin r → ℂ) (d : Fin m → ℂ) (q : Fin m → Fin r → ℂ) :
    hermC τ G u (∑ l, d l • q l) = ∑ l, conj (d l) * hermC τ G u (q l) := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ l, ∑ b, u a * τ (G a b) * (conj (d l) * conj (q l b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, u a * τ (G a b) * (conj (d l) * conj (q l b)) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

theorem expand (q : Fin n → Fin r → ℂ) (x y : Fin r → ℂ) (c d : Fin n → ℂ)
    (hx : ∀ l, hermC τ G x (q l) = 0) (hy : ∀ k, hermC τ G (q k) y = 0) :
    hermC τ G (x + ∑ k, c k • q k) (y + ∑ l, d l • q l) =
      hermC τ G x y + ∑ k, ∑ l, c k * conj (d l) * hermC τ G (q k) (q l) := by
  rw [hermC_add_left', hermC_add_right_fundamental_domains', hermC_add_right_fundamental_domains']
  simp only [hermC_sum_smul_right, hermC_sum_smul_left, hx, hy, mul_zero, Finset.sum_const_zero, add_zero,
    Finset.mul_sum]
  rw [zero_add, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

variable (hG : ∀ a b, cc (G a b) = G b a)
  (hf : ∀ k l, hermC τ G (f k) (f l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
include hG hf

theorem hf_eps (k l : Fin n) : hermC τ G (f k) (f l) = if k = l then eps p k else 0 := by
  rw [hf]
  rfl

theorem Mmat_f (l : Fin n) : Mmat τ G p f g *ᵥ f l = g l := by
  rw [Mmat_mulVec]
  simp only [hf_eps τ G p f hG hf, mul_ite, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, eps_sq, one_smul]
  abel

theorem Mmat_fix (v : Fin r → ℂ) (hv : ∀ k, hermC τ G v (f k) = 0) : Mmat τ G p f g *ᵥ v = v := by
  rw [Mmat_mulVec]
  simp [hv]

theorem Mmat_comb (β : Fin n → ℂ) : Mmat τ G p f g *ᵥ (∑ c, β c • f c) = ∑ c, β c • g c := by
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, Mmat_f τ G p f g hG hf]

private lemma hermC_eq_conj_hermC_swap (u v : Fin r → ℂ) : hermC τ G u v = conj (hermC τ G v u) := by
  unfold hermC
  simp only [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hG i j]
  simp only [cc, IsCMField.complexEmbedding_complexConj]
  ring

theorem Mmat_unitary (hgf : ∀ k, g k ∈ Submodule.span ℂ (Set.range f))
    (hg : ∀ k l, hermC τ G (g k) (g l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
    (v w : Fin r → ℂ) :
    hermC τ G (Mmat τ G p f g *ᵥ v) (Mmat τ G p f g *ᵥ w) = hermC τ G v w := by
  have hconj : ∀ u u', hermC τ G u u' = conj (hermC τ G u' u) := hermC_eq_conj_hermC_swap τ G p f hG hf
  have hdec : ∀ u : Fin r → ℂ, ∃ (x : Fin r → ℂ) (cu : Fin n → ℂ),
      u = x + ∑ k, cu k • f k ∧ ∀ l, hermC τ G x (f l) = 0 := by
    intro u
    refine ⟨u + ∑ k, (-(eps p k * hermC τ G u (f k))) • f k, fun k => eps p k * hermC τ G u (f k), ?_,
      fun l => ?_⟩
    · simp only [neg_smul, Finset.sum_neg_distrib]
      abel
    · rw [hermC_add_left', hermC_sum_smul_left]
      simp only [hf_eps τ G p f hG hf, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      linear_combination (-hermC τ G u (f l)) * eps_sq p l
  have hperp : ∀ x : Fin r → ℂ, (∀ l, hermC τ G x (f l) = 0) → ∀ k, hermC τ G x (g k) = 0 := by
    intro x hx k
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).mp (hgf k)
    rw [← ha, hermC_sum_smul_right]
    simp [hx]
  obtain ⟨xv, cv, hv, hxv⟩ := hdec v
  obtain ⟨xw, cw, hw, hxw⟩ := hdec w
  have hMv : Mmat τ G p f g *ᵥ v = xv + ∑ k, cv k • g k := by
    rw [hv, Matrix.mulVec_add, Mmat_fix τ G p f g hG hf xv hxv, Mmat_comb τ G p f g hG hf]
  have hMw : Mmat τ G p f g *ᵥ w = xw + ∑ k, cw k • g k := by
    rw [hw, Matrix.mulVec_add, Mmat_fix τ G p f g hG hf xw hxw, Mmat_comb τ G p f g hG hf]
  rw [hMv, hMw, hv, hw]
  rw [expand τ G g xv xw cv cw (hperp xv hxv) (fun k => by rw [hconj, hperp xw hxw k, map_zero]),
    expand τ G f xv xw cv cw hxv (fun k => by rw [hconj, hxw k, map_zero])]
  simp only [hg, hf]

theorem Mmat_span (hgf : ∀ k, g k ∈ Submodule.span ℂ (Set.range f)) (v : Fin r → ℂ)
    (hv : v ∈ Submodule.span ℂ (Set.range f)) :
    Mmat τ G p f g *ᵥ v ∈ Submodule.span ℂ (Set.range f) := by
  rw [Mmat_mulVec]
  exact Submodule.add_mem _ hv (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Submodule.sub_mem _ (hgf k) (Submodule.subset_span ⟨k, rfl⟩)))

end

end ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices
