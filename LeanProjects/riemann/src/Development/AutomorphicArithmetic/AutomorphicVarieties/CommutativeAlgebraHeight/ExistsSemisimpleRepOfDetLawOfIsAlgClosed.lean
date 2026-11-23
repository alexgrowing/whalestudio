import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFaithfulSs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFactor
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DMatrix

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem det_bd {α : Type*} [Fintype α] [DecidableEq α] {m : α → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {R : Type*} [CommRing R]
    (d : ∀ i, Matrix (m i) (m i) R) : (Matrix.blockDiagonal' d).det = ∏ k, (d k).det := by
  classical
  let _ : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  rw [(Matrix.blockTriangular_blockDiagonal' d).det_fintype]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  have : (Matrix.blockDiagonal' d).toSquareBlock Sigma.fst k =
      (d k).submatrix (Equiv.sigmaSubtype k) (Equiv.sigmaSubtype k) := by
    ext ⟨⟨i, a⟩, hi⟩ ⟨⟨j, b⟩, hj⟩
    dsimp only at hi hj
    subst hi hj
    simp [Matrix.toSquareBlock_def, Equiv.sigmaSubtype]
  rw [this, Matrix.det_submatrix_equiv_self]

private theorem pull_pull {n : ℕ} {A E E' E'' : Type} [CommRing A] [Ring E] [Algebra A E] [Ring E'] [Algebra A E']
    [Ring E''] [Algebra A E''] (D : Det n A E) (f : E' →ₐ[A] E) (g : E'' →ₐ[A] E') :
    (D.pull f).pull g = D.pull (f.comp g) := by
  refine Det.ext' fun S _ _ x => ?_
  change D.D S (Algebra.TensorProduct.map (AlgHom.id S S) f (Algebra.TensorProduct.map (AlgHom.id S S) g x)) =
    D.D S (Algebra.TensorProduct.map (AlgHom.id S S) (f.comp g) x)
  congr 1
  induction x with
  | zero => simp
  | tmul s y => simp
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem pull_id {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) :
    D.pull (AlgHom.id A E) = D := by
  refine Det.ext' fun S _ _ x => ?_
  change D.D S (Algebra.TensorProduct.map (AlgHom.id S S) (AlgHom.id A E) x) = D.D S x
  simp

private theorem ofRep_comp {n : ℕ} {A E E' ι : Type} [CommRing A] [Ring E] [Algebra A E] [Ring E'] [Algebra A E']
    [Fintype ι] [DecidableEq ι] (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) (g : E' →ₐ[A] E) :
    Det.ofRep h (r.comp g) = (Det.ofRep h r).pull g := by
  refine Det.ext' fun S _ _ x => ?_
  change (Det.repS (r.comp g) S x).det = (Det.repS r S (Algebra.TensorProduct.map (AlgHom.id S S) g x)).det
  congr 1
  induction x with
  | zero => simp
  | tmul s y => simp [Det.repS_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem ofRep_fin {n : ℕ} {A E ι : Type} [CommRing A] [Ring E] [Algebra A E]
    [Fintype ι] [DecidableEq ι] (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) :
    ∃ r' : E →ₐ[A] Matrix (Fin n) (Fin n) A, Det.ofRep (Fintype.card_fin n) r' = Det.ofRep h r := by
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq h
  refine ⟨(Matrix.reindexAlgEquiv A A e).toAlgHom.comp r, Det.ext' fun S _ _ x => ?_⟩
  change (Det.repS ((Matrix.reindexAlgEquiv A A e).toAlgHom.comp r) S x).det = (Det.repS r S x).det
  rw [← Matrix.det_submatrix_equiv_self e.symm (Det.repS r S x)]
  congr 1
  induction x with
  | zero => simp
  | tmul s y => ext a b; simp [Det.repS_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]; rfl

private def bdRep {k ι κ : Type} [CommRing k] [Fintype κ] [DecidableEq κ] (m : ι → Type) [∀ i, Fintype (m i)]
    [∀ i, DecidableEq (m i)] (p : κ → ι) :
    (∀ i, Matrix (m i) (m i) k) →ₐ[k] Matrix (Σ j, m (p j)) (Σ j, m (p j)) k where
  toFun x := Matrix.blockDiagonal' fun j => x (p j)
  map_one' := Matrix.blockDiagonal'_one
  map_mul' x y := Matrix.blockDiagonal'_mul (fun j => x (p j)) (fun j => y (p j))
  map_zero' := Matrix.blockDiagonal'_zero
  map_add' x y := Matrix.blockDiagonal'_add (fun j => x (p j)) (fun j => y (p j))
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [← Matrix.blockDiagonal'_one, ← Matrix.blockDiagonal'_smul]
    rfl

private theorem bdRep_repS {k ι κ : Type} [CommRing k] [Fintype κ] [DecidableEq κ] (m : ι → Type)
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (p : κ → ι) (S : Type) [CommRing S] [Algebra k S]
    (y : S ⊗[k] (∀ i, Matrix (m i) (m i) k)) :
    Det.repS (bdRep m p) S y = Matrix.blockDiagonal' fun j => Det.repS (AlgHom.id k _) S
      (Algebra.TensorProduct.map (AlgHom.id S S) (Pi.evalAlgHom k (fun i => Matrix (m i) (m i) k) (p j)) y) := by
  induction y with
  | zero => simp; exact Matrix.blockDiagonal'_zero.symm
  | tmul s x =>
    ext ⟨a, a'⟩ ⟨b, b'⟩
    by_cases hab : a = b
    · subst hab
      simp [Det.repS_tmul, bdRep]
    · simp [Det.repS_tmul, bdRep, Matrix.blockDiagonal'_apply_ne _ _ _ hab]
  | add a b ha hb =>
    simp only [map_add, ha, hb]
    rw [← Matrix.blockDiagonal'_add]
    rfl

private theorem pi_case {n N : ℕ} {k : Type} [Field k] (d : Fin N → ℕ)
    (D : Det n k (∀ i, Matrix (Fin (d i + 1)) (Fin (d i + 1)) k)) :
    ∃ r : (∀ i, Matrix (Fin (d i + 1)) (Fin (d i + 1)) k) →ₐ[k] Matrix (Fin n) (Fin n) k,
      Det.ofRep (Fintype.card_fin n) r = D := by
  obtain ⟨m, Ds, hm, hD⟩ := d_prod (fun i => Matrix (Fin (d i + 1)) (Fin (d i + 1)) k) D
  choose μ hμ hDs using fun i => d_matrix (Ds i)
  have hc : Fintype.card (Σ j : (Σ i, Fin (μ i)), Fin (d j.1 + 1)) = n := by
    rw [← hm, Fintype.card_sigma, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hμ i]
  obtain ⟨r, hr⟩ := ofRep_fin hc (bdRep (k := k) (fun i => Fin (d i + 1)) (fun j : (Σ i, Fin (μ i)) => j.1))
  refine ⟨r, hr.trans (Det.ext' fun S _ _ y => ?_)⟩
  rw [hD]
  change (Det.repS (bdRep (k := k) (fun i => Fin (d i + 1)) (fun j : (Σ i, Fin (μ i)) => j.1)) S y).det = _
  rw [bdRep_repS, det_bd, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  refine Eq.trans ?_ (hDs i S _).symm
  exact Fin.prod_const (M := S) (μ i) (Det.repS (AlgHom.id k _) S (Algebra.TensorProduct.map (AlgHom.id S S)
    (Pi.evalAlgHom k (fun i => Matrix (Fin (d i + 1)) (Fin (d i + 1)) k) i) y)).det

theorem UpperTheory.V.CA.exists_semisimple_rep_of_detLaw_of_isAlgClosed :
    ∀ {n : ℕ} {k E : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E] (D : Det n k E), ∃ r : E →ₐ[k] Matrix (Fin n) (Fin n) k, IsSemisimpleRing r.range ∧ Det.ofRep (Fintype.card_fin n) r = D := by
  intro n k E _ _ _ _ D
  let f : E →ₐ[k] D.ker.ringCon.Quotient := RingCon.mkₐ k D.ker.ringCon
  have hf : Function.Surjective f := fun y => Quotient.inductionOn' y fun x => ⟨x, rfl⟩
  have hk : ∀ x, f x = 0 ↔ x ∈ D.ker := fun x => by
    rw [TwoSidedIdeal.mem_iff, ← RingCon.eq]
    rfl
  obtain ⟨D', hD', -⟩ := d_factor D f hf fun x => (hk x).1
  have hker : D'.ker = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨x, rfl⟩ := hf y
    have := (d_pull D' f).2.1 x hy
    rw [hD'] at this
    exact (TwoSidedIdeal.mem_bot _).2 ((hk x).2 this)
  obtain ⟨hfin, hss⟩ := d_faithful_ss D' hker
  obtain ⟨N, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k D.ker.ringCon.Quotient
  obtain ⟨d', rfl⟩ : ∃ d' : Fin N → ℕ, d = fun i => d' i + 1 :=
    ⟨fun i => d i - 1, funext fun i => by have := (hd i).out; dsimp only; omega⟩
  obtain ⟨r, hr⟩ := pi_case d' (D'.pull e.symm.toAlgHom)
  refine ⟨(r.comp e.toAlgHom).comp f, ?_, ?_⟩
  · have hrange : ((r.comp e.toAlgHom).comp f).range = (r.comp e.toAlgHom).range := by
      rw [AlgHom.range_comp, (AlgHom.range_eq_top f).2 hf, Algebra.map_top]
    rw [hrange]
    exact RingHom.isSemisimpleRing_of_surjective (r.comp e.toAlgHom).rangeRestrict.toRingHom
      (AlgHom.rangeRestrict_surjective _)
  · rw [ofRep_comp, ofRep_comp, hr, pull_pull D']
    have : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id k _ := by
      ext x; simp
    rw [this, pull_id, hD']
