import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.PolForm

def expv {ι : Type} {n : ℕ} (c : Fin n → ι) : ι →₀ ℕ := ∑ a, Finsupp.single (c a) 1

theorem prod_X_eq {ι : Type} {n : ℕ} (c : Fin n → ι) :
    (∏ a, X (c a) : MvPolynomial ι ℝ) = monomial (expv c) 1 := by
  rw [expv, monomial_sum_one]; rfl

theorem expv_apply {ι : Type} [DecidableEq ι] {n : ℕ} (c : Fin n → ι) (i : ι) :
    expv c i = Fintype.card {a // c a = i} := by
  rw [expv, Finsupp.finset_sum_apply, Fintype.card_subtype]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_boole]
  simp

theorem weight_expv {ι : Type} {n : ℕ} (c : Fin n → ι) : Finsupp.weight 1 (expv c) = n := by
  simp [expv, map_sum, Finsupp.weight_apply, Finsupp.sum_single_index]

theorem exists_perm_of_expv_eq {ι : Type} {n : ℕ} {c c' : Fin n → ι} (h : expv c = expv c') :
    ∃ e : Equiv.Perm (Fin n), ∀ a, c' a = c (e a) := by
  classical
  have hc : ∀ i, Fintype.card {a // c' a = i} = Fintype.card {a // c a = i} := fun i => by
    have := congrArg (fun s => s i) h
    simp only [expv_apply] at this
    convert this.symm
  let E : ∀ i, {a // c' a = i} ≃ {a // c a = i} := fun i => Fintype.equivOfCardEq (hc i)
  refine ⟨(Equiv.sigmaFiberEquiv c').symm.trans ((Equiv.sigmaCongrRight E).trans (Equiv.sigmaFiberEquiv c)),
    fun a => ?_⟩
  show c' a = c (E (c' a) ⟨a, rfl⟩).1
  exact (E (c' a) ⟨a, rfl⟩).2.symm

end GlobalTheory.MixHt.PolForm

namespace GlobalTheory.MixHt

open PolForm in

theorem exists_linear_of_multiadditive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (d : ℕ) (F : (Fin (d + 1) → HermLB p) → ℝ), (∀ L M, (∀ a, (L a).Isometric (M a)) → F L = F M) → (∀ L (e : Equiv.Perm (Fin (d + 1))), F (fun a => L (e a)) = F L) → (∀ (A B : HermLB p) (L : Fin d → HermLB p), F (Fin.cons (A.tens B) L) = F (Fin.cons A L) + F (Fin.cons B L)) → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, (∀ n : Fin (d + 1) → ι → ℤ, Φ (∏ a, lin fun i => (n a i : ℝ)) = F fun a => comb L (n a)) ∧ ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d + 1 → P.IsHomogeneous e → Φ P = 0 := by
  intro k _ X p d F hiso hsymm hadd ι _ L
  classical
  let rep : HermLB.IsomClass p → HermLB p := fun x => Quotient.out (s := HermLB.isometrySetoid p) x
  have hrepcls : ∀ x, (rep x).icls = x := fun x => Quotient.out_eq (s := HermLB.isometrySetoid p) x
  let G' : (Fin (d + 1) → HermLB.IsomClass p) → ℝ := fun v => F fun a => rep (v a)
  have hG : ∀ M : Fin (d + 1) → HermLB p, G' (fun a => (M a).icls) = F M :=
    fun M => hiso _ _ fun a => HermLB.icls_eq_iff.1 (hrepcls _)
  have hGs : ∀ v (e : Equiv.Perm (Fin (d + 1))), G' (fun a => v (e a)) = G' v :=
    fun v e => hsymm (fun a => rep (v a)) e
  have hG0 : ∀ (x y : HermLB.IsomClass p) (w : Fin d → HermLB.IsomClass p),
      G' (Fin.cons (x + y) w) = G' (Fin.cons x w) + G' (Fin.cons y w) := by
    intro x y w
    have hc : ∀ z, (fun a => rep ((Fin.cons z w : Fin (d + 1) → HermLB.IsomClass p) a)) =
        Fin.cons (rep z) (fun a => rep (w a)) := fun z => by
      funext a; exact Fin.cases rfl (fun _ => rfl) a
    show F (fun a => rep ((Fin.cons (x + y) w : Fin (d + 1) → HermLB.IsomClass p) a)) =
      F (fun a => rep ((Fin.cons x w : Fin (d + 1) → HermLB.IsomClass p) a)) +
        F (fun a => rep ((Fin.cons y w : Fin (d + 1) → HermLB.IsomClass p) a))
    rw [hc, hc, hc, ← hadd]
    refine hiso _ _ fun a => Fin.cases ?_ (fun b => ?_) a
    · simp only [Fin.cons_zero]
      exact HermLB.icls_eq_iff.1 (by rw [HermLB.icls_tens, hrepcls, hrepcls, hrepcls])
    · simp only [Fin.cons_succ]; exact HermLB.Isometric.refl _
  have h0 : ∀ (q : Fin (d + 1) → HermLB.IsomClass p) (x y : HermLB.IsomClass p),
      G' (Function.update q 0 (x + y)) = G' (Function.update q 0 x) + G' (Function.update q 0 y) := by
    intro q x y
    rw [← Fin.cons_self_tail q, Fin.update_cons_zero, Fin.update_cons_zero, Fin.update_cons_zero]
    exact hG0 x y _
  have hGi : ∀ (m : Fin (d + 1) → HermLB.IsomClass p) (i : Fin (d + 1)) (x y : HermLB.IsomClass p),
      G' (Function.update m i (x + y)) = G' (Function.update m i x) + G' (Function.update m i y) := by
    intro m i x y
    have key : ∀ z, G' (Function.update m i z) = G' (Function.update (m ∘ Equiv.swap 0 i) 0 z) := fun z => by
      rw [← hGs (Function.update m i z) (Equiv.swap 0 i)]
      show G' (Function.update m i z ∘ Equiv.swap 0 i) = _
      rw [Function.update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_right]
    rw [key, key, key]
    exact h0 _ x y
  let Mlt : MultilinearMap ℤ (fun _ : Fin (d + 1) => HermLB.IsomClass p) ℝ :=
    { toFun := G'
      map_update_add' := by
        intro inst m i x y
        obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
        exact hGi m i x y
      map_update_smul' := by
        intro inst m i c x
        obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
        exact map_zsmul (AddMonoidHom.mk' (fun z => G' (Function.update m i z)) (hGi m i)) c x }
  let g : ι → HermLB.IsomClass p := fun i => (L i).icls
  let f : (Fin (d + 1) → ι) → ℝ := fun c => G' fun a => g (c a)
  have hf : ∀ c (e : Equiv.Perm (Fin (d + 1))), f (fun a => c (e a)) = f c := fun c e => hGs (fun a => g (c a)) e
  have hF : ∀ n : Fin (d + 1) → ι → ℤ, F (fun a => comb L (n a)) =
      ∑ c : Fin (d + 1) → ι, (∏ a, (n a (c a) : ℝ)) * f c := by
    intro n
    rw [← hG]
    simp only [icls_comb]
    have e1 := Mlt.map_sum (fun a i => n a i • g i)
    have e2 : ∀ c : Fin (d + 1) → ι, Mlt (fun a => n a (c a) • g (c a)) = (∏ a, (n a (c a) : ℝ)) * f c := by
      intro c
      rw [Mlt.map_smul_univ (fun a => n a (c a)) (fun a => g (c a)), zsmul_eq_mul, Int.cast_prod]
      rfl
    simp only [e2] at e1
    exact e1
  let φ : (ι →₀ ℕ) → ℝ := fun s => if h : ∃ c : Fin (d + 1) → ι, expv c = s then f h.choose else 0
  have hφ : ∀ c, φ (expv c) = f c := by
    intro c
    have h : ∃ c' : Fin (d + 1) → ι, expv c' = expv c := ⟨c, rfl⟩
    simp only [φ, dif_pos h]
    obtain ⟨e, he⟩ := exists_perm_of_expv_eq h.choose_spec
    rw [← hf h.choose e]
    exact congrArg f (funext fun a => (he a).symm)
  let Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ := (basisMonomials ι ℝ).constr ℝ φ
  have hΦ : ∀ s, Φ (monomial s 1) = φ s := by
    intro s
    have := (basisMonomials ι ℝ).constr_basis ℝ φ s
    rwa [coe_basisMonomials] at this
  refine ⟨Φ, fun n => ?_, fun P e he hP => ?_⟩
  · rw [hF]
    simp only [lin]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod, prod_X_eq, C_mul', map_smul, hΦ, hφ, smul_eq_mul]
  · rw [P.as_sum, map_sum]
    refine Finset.sum_eq_zero fun s hs => ?_
    have hm : monomial s (coeff s P) = coeff s P • monomial s (1 : ℝ) := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, hΦ, smul_eq_mul]
    refine mul_eq_zero_of_right _ (dif_neg ?_)
    rintro ⟨c, rfl⟩
    have := hP (mem_support_iff.1 hs)
    rw [weight_expv] at this
    exact he this.symm

end GlobalTheory.MixHt
