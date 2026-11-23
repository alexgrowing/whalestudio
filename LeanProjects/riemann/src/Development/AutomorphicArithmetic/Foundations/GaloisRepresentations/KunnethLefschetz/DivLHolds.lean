import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.FrobTraceOf
import Development.EtaleCohomology.EtaleTrace.LPdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

private theorem pbc {l : ℕ} [Fact l.Prime] {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (n : ℤ) (x : V l X n) :
    pb l (f ≫ g) n x = pb l f n (pb l g n x) := by
  rw [LateralTheory.EtaleTrace.pb_comp]; rfl

private theorem powV_pull {l : ℕ} [Fact l.Prime] (R : Ring l) {Y X : Scheme.{0}} (f : Y ⟶ X) (hu : IsUnit (l : Γ(X, ⊤)))
    (x : V l X 2) (j : ℕ) : pb l f _ (powV l x j) = powV l (pb l f 2 x) j := by
  induction j with
  | zero => exact R.one_nat f hu
  | succ j ih =>
    change pb l f _ (cupV l X _ (powV l x j) x) = cupV l Y _ (powV l (pb l f 2 x) j) (pb l f 2 x)
    rw [R.nat, ih]

private theorem pull_onto {l : ℕ} [Fact l.Prime] (R : Ring l) {E W X : Scheme.{0}} (i : E ⟶ W) (s : W ⟶ X)
    (hu : IsUnit (l : Γ(W, ⊤))) (e : V l W 2) (hP : PBQ l (i ≫ s) (pb l i 2 e)) (n : ℤ) (b : V l E n) :
    ∃ m, pb l i n m = b := by
  have hle : (⊤ : Submodule ℚ_[l] (V l E n)) ≤ LinearMap.range (pb l i n) := by
    rw [← hP.span n, Submodule.span_le]
    rintro z ⟨j, a, h, u, rfl⟩
    refine ⟨cupV l W h (pb l s a u) (powV l e j), ?_⟩
    rw [R.nat, pbc, powV_pull R i hu]
  exact hle (Submodule.mem_top (x := b))

private theorem unit_eq {l : ℕ} [Fact l.Prime] (R : Ring l) {E W X : Scheme.{0}} (i : E ⟶ W) (s : W ⟶ X)
    (uX : IsUnit (l : Γ(X, ⊤))) (uE : IsUnit (l : Γ(E, ⊤))) (e ε : V l W 2) (u0 a v : _)
    (he : e = cupV l W (zero_add 2) (pb l s 0 u0) ε)
    (hP : PBQ l (i ≫ s) (pb l i 2 e))
    (hav : pb l i 2 ε = pb l (i ≫ s) 2 a + cupV l E (zero_add 2) (pb l (i ≫ s) 0 v) (pb l i 2 e)) :
    cupV l X (add_zero 0) v u0 = oneV l X := by
  set ξ := pb l i 2 e with hξdef
  have h0 : ξ = cupV l E (zero_add 2) (pb l (i ≫ s) 0 u0) (pb l i 2 ε) := by
    rw [hξdef, he, R.nat, pbc]
  have h1 : ξ = pb l (i ≫ s) 2 (cupV l X (zero_add 2) u0 a)
      + cupV l E (zero_add 2) (pb l (i ≫ s) 0 (cupV l X (add_zero 0) u0 v)) ξ := by
    conv_lhs => rw [h0, hav]
    rw [map_add, ← R.nat,
      ← R.assoc E 0 0 2 0 2 2 (add_zero 0) (zero_add 2) (zero_add 2) (zero_add 2), ← R.nat]
  have h2 : cupV l E (zero_add 2) (pb l (i ≫ s) 0 (oneV l X)) ξ = ξ := by
    rw [R.one_nat _ uX, R.one_mul E uE]
  have h3 : pb l (i ≫ s) 2 (cupV l X (zero_add 2) u0 a)
      + cupV l E (zero_add 2) (pb l (i ≫ s) 0 (cupV l X (add_zero 0) u0 v - oneV l X)) ξ = 0 := by
    rw [map_sub, map_sub, LinearMap.sub_apply, h2, ← add_sub_assoc, ← h1, sub_self]
  have h4 := hP.indep _ _ h3
  rw [sub_eq_zero] at h4
  rw [R.comm X 0 0 0 (add_zero 0) (add_zero 0) v u0, h4]
  simp

theorem divL_holds : DivL := by
  intro l _ k _ _ hl R G W E X px i s c hpair hprop U hoff e he0 hP n w h z hz
  have hk : IsUnit (l : k) := isUnit_iff_ne_zero.2 hl
  have uX := LPdCut.unit_of px hk
  have uW := LPdCut.unit_of (s ≫ px) hk
  have uE := LPdCut.unit_of (i ≫ s ≫ px) hk
  have h02 : (0 : ℤ) + 2 * ((1 : ℕ) : ℤ) = 2 := by norm_num
  have hnw : n + 2 * ((1 : ℕ) : ℤ) = w := by push_cast; omega
  have hn2 : n + 2 = w := by omega
  obtain ⟨ε, hε⟩ : ∃ ε, G.g hpair h02 (oneV l E) = ε := ⟨_, rfl⟩
  obtain ⟨ε0, hε0⟩ := G.onto hpair h02 U hoff hprop e he0
  obtain ⟨u0, rfl⟩ := hP.zero ε0
  have he : e = cupV l W (zero_add 2) (pb l s 0 u0) ε := by
    rw [← hε, ← G.proj hpair (add_zero 0) h02 h02 (zero_add 2), R.mul_one E uE, ← pbc, hε0]
  obtain ⟨a, v, hav⟩ := hP.two (pb l i 2 ε)
  have hunit := unit_eq R i s uX uE e ε u0 a v he hP hav
  have hε' : cupV l W (add_zero 2) e (pb l s 0 v) = ε := by
    rw [R.comm W 2 0 2 (add_zero 2) (zero_add 2), he,
      ← R.assoc W 0 0 2 0 2 2 (add_zero 0) (zero_add 2) (zero_add 2) (zero_add 2), ← R.nat, hunit,
      R.one_nat _ uX, R.one_mul W uW]
    simp
  obtain ⟨b, hb⟩ := G.onto hpair hnw U hoff hprop z hz
  obtain ⟨m', rfl⟩ := pull_onto R i s uW e hP n b
  have hz' : z = cupV l W hn2 m' ε := by
    rw [← hb, ← hε, ← G.proj hpair (add_zero n) hnw h02 hn2, R.mul_one E uE]
  refine ⟨cupV l W (zero_add n) (pb l s 0 v) m', ?_⟩
  rw [hz', ← R.assoc W 2 0 n 2 n w (add_zero 2) h (zero_add n) h, hε',
    R.comm W n 2 w hn2 h, Int.negOnePow_even _ ⟨n, by ring⟩, one_smul]

end UpperTheory.Gal.KunnethLefschetz
