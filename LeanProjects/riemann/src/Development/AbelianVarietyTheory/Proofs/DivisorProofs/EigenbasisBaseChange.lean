import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Matrix

namespace GlobalTheory.EigBasisExtend

theorem eig_rows_map {k K O : Type} [Field k] [Field K] (i : k →+* K) {m n : ℕ} {P : Matrix (Fin m) (Fin n) k}
    (hP : ∀ c, c ᵥ* P = 0 → c = 0) (A : O → Matrix (Fin n) (Fin n) k) (χ : O → k)
    (h : ∀ c, (∀ a, c ᵥ* A a = χ a • c) → ∃ d, d ᵥ* P = c) (c : Fin n → K)
    (hc : ∀ a, c ᵥ* (A a).map i = i (χ a) • c) : ∃ d, d ᵥ* P.map i = c := by
  obtain ⟨g, hg⟩ := (Matrix.vecMulLinear P).exists_leftInverse_of_injective (LinearMap.ker_eq_bot'.2 hP)
  have h1 : P * LinearMap.toMatrixRight' g = 1 := by
    apply Matrix.toLinearMapRight'.injective
    rw [Matrix.toLinearMapRight'_mul, Matrix.toLinearMapRight'_one]
    change Matrix.toLinearMapRight' (LinearMap.toMatrixRight' g) ∘ₗ Matrix.vecMulLinear P = _
    simpa using hg
  set Q := LinearMap.toMatrixRight' g
  let := i.toAlgebra
  have key : ∀ (l : K →ₗ[k] k) {p q : ℕ} (M : Matrix (Fin p) (Fin q) k) (v : Fin p → K),
      (fun j => l ((v ᵥ* M.map i) j)) = (fun j => l (v j)) ᵥ* M := fun l p q M v => by
    funext j
    simp only [Matrix.vecMul, dotProduct, map_sum, Matrix.map_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [_root_.mul_comm (v s), _root_.mul_comm (l _), ← smul_eq_mul (M s j), ← map_smul, Algebra.smul_def]
    rfl
  refine ⟨c ᵥ* Q.map i, funext fun j => sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff k _).1 fun l => ?_)⟩
  obtain ⟨d, hd⟩ := h (fun j => l (c j)) fun a => by
    rw [← key, hc]
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← smul_eq_mul (χ a), ← map_smul, Algebra.smul_def]
    rfl
  have e := congrFun (key l P (c ᵥ* Q.map i)) j
  rw [key, ← hd, Matrix.vecMul_vecMul d, h1, Matrix.vecMul_one, hd] at e
  rw [map_sub, e, sub_self]

theorem isEigVec_iff {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (act : OAct O G) (χ : O →+* R) {n : ℕ} {e : Fin n → (epsR R ⟶ G)} (he : IsLieBasis e)
    {A : O → Matrix (Fin n) (Fin n) R} (hA : ∀ a j, IsLieComb (A a j) e (e j ≫ act.act a))
    {c : Fin n → R} {w : epsR R ⟶ G} (hw : IsLieComb c e w) :
    EigenvectorLieDegree.IsEigVec act χ w ↔ ∀ a, c ᵥ* A a = χ a • c := by
  let b := Serre.Lie.basis act he
  have hb : (fun j => (b j).hom) = e := funext (Serre.Lie.hom_basis he)
  clear_value b
  subst hb
  obtain rfl := (Serre.Lie.isLieComb_iff c b w).1 hw
  have hA' : ∀ a j, a • b j = ∑ s, A a j s • b s := fun a j =>
    Serre.Lie.ext ((Serre.Lie.isLieComb_iff _ b _).1 (hA a j))
  have h1 : ∀ a, a • ∑ j, c j • b j = ∑ s, (c ᵥ* A a) s • b s := fun a => by
    simp only [Finset.smul_sum, smul_comm a, hA', Matrix.vecMul, dotProduct, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have h2 : ∀ a, χ a • ∑ j, c j • b j = ∑ s, (χ a • c) s • b s := fun a => by
    simp only [Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul]
  refine (and_iff_right (Serre.Lie.isTangent _)).trans (Serre.Lie.mem_eig_iff_left.symm.trans ?_)
  rw [Serre.Lie.mem_eig_iff]
  refine forall_congr' fun a => ?_
  rw [h1, h2, ← b.equivFun_symm_apply, ← b.equivFun_symm_apply, EmbeddingLike.apply_eq_iff_eq]

theorem isEigBasis_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (t : SAB H (Sp k)) (t' : SAB H (Sp k')) (n : SABMap t' t (spMap i)) (m : ℕ) (x : Fin m → (epsR k ⟶ t.G)) (x' : Fin m → (epsR k' ⟶ t'.G)) (χ : 𝓞 E →+* k), (∀ a, IsVecOver i n.φ (x a) (x' a)) → EigenvectorLieDegree.IsEigBasis t.act χ x → EigenvectorLieDegree.IsEigBasis t'.act (i.comp χ) x' := by
  intro E _ _ _ H k k' _ _ _ _ i t t' n m x x' χ hx' hx
  have hi := Indep.of_eigBasis hx
  have := t.semi.smooth
  obtain ⟨N, e, he⟩ := Chart.exists_isLieBasis t.G t.semi.smooth
  choose e' h _ using fun j => existsUnique_isVecOver n.cart.1 (e j)
  have he' := Chart.isLieBasis_baseChange i n.cart he h
  choose P hP _ using fun s => he.2 _ (hi.1 s)
  have hP' : ∀ s, IsLieComb ((Matrix.of P).map i s) e' (x' s) := fun s =>
    (lieComb_baseChange _ _ i t.G t'.G n.φ n.cart N e (x s) (P s) e' (x' s) h (hP s)).1 (hx' s)
  choose A hA _ using fun a j => he.2 (e j ≫ t.act.act a) (Serre.Lie.isTangent (a • Serre.Lie.mk t.act (e j) (he.1 j)))
  have hA' : ∀ a j, IsLieComb ((Matrix.of (A a)).map i j) e' (e' j ≫ t'.act.act a) := fun a j =>
    (lieComb_baseChange _ _ i t.G t'.G n.φ n.cart N e _ (A a j) e' _ h (hA a j)).1 (by
      have := h j
      simp only [IsVecOver] at this ⊢
      rw [Over.comp_left, Category.assoc, n.act a, ← Category.assoc, this, Category.assoc, Over.comp_left])
  have hinj := hi.vecMul_eq_zero (P := Matrix.of P) he.1 hP
  have E1 := fun c w => isEigVec_iff t.act χ he (A := fun a => Matrix.of (A a)) hA (c := c) (w := w)
  have E2 := fun c w => isEigVec_iff t'.act (i.comp χ) he' (A := fun a => (Matrix.of (A a)).map i) hA' (c := c) (w := w)
  have tx : ∀ s, IsTangent (x' s) := fun s => (hx' s).isTangent n.cart (hi.1 s)
  refine ⟨fun s => (E2 _ _ (hP' s)).2 fun a => ?_, fun w hw => ?_⟩
  · have := (E1 _ _ (hP s)).1 (hx.1 s) a
    funext j
    have := congrArg i (congrFun this j)
    simpa [Matrix.vecMul, dotProduct] using this
  · obtain ⟨c, hc, -⟩ := he'.2 w hw.1
    obtain ⟨d, hd⟩ := eig_rows_map i hinj (fun a => Matrix.of (A a)) χ (fun c hc => by
      obtain ⟨w, hw⟩ := ((LieComb.lieComb_algebra k t.G N e he.1).1 c).exists
      obtain ⟨d, hd, -⟩ := hx.2 w ((E1 _ _ hw).2 hc)
      exact ⟨d, (Indep.of_basis he).2 _ _ w ((comb_comb (P := Matrix.of P) he.1 hP _ _).1 hd) hw⟩) c
      ((E2 _ _ hc).1 hw)
    refine ⟨d, (comb_comb he'.1 hP' _ _).2 (hd ▸ hc), fun d' hd' => ?_⟩
    refine sub_eq_zero.1 (vecMul_map_eq_zero i hinj _ ?_)
    rw [Matrix.sub_vecMul, hd, (Indep.of_basis he').2 _ _ w ((comb_comb he'.1 hP' _ _).1 hd') hc, sub_self]

end GlobalTheory.EigBasisExtend
