import Formalism.HarderNarasimhan.StatementPl
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep

open Module NumberField Matrix

noncomputable section

namespace Formalism.HN

namespace HeightGram

section Basic

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

theorem realize_apply0 (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (v : InfinitePlace K) (i : ι) :
    (Formalism.HermitianLatticesTheory.realize b X x) (v, i, 0) = (Formalism.HermitianLatticesTheory.fcoord b X v x i).re := by
  first
  | rfl
  | simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw]

theorem realize_apply1 (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (v : InfinitePlace K) (i : ι) :
    (Formalism.HermitianLatticesTheory.realize b X x) (v, i, 1) = (Formalism.HermitianLatticesTheory.fcoord b X v x i).im := by
  first
  | rfl
  | simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw]

theorem realize_injective (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) : Function.Injective (Formalism.HermitianLatticesTheory.realize b X) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hf : ∀ i, Formalism.HermitianLatticesTheory.fcoord b X v x i = 0 := by
    intro i
    apply Complex.ext
    · rw [← realize_apply0, hx]; simp
    · rw [← realize_apply1, hx]; simp
  have hvec : Formalism.HermitianLatticesTheory.vecAt b v x = 0 := by
    have h1 : (X v)⁻¹ *ᵥ Formalism.HermitianLatticesTheory.vecAt b v x = 0 := funext hf
    have h2 := congrArg (fun w => X v *ᵥ w) h1
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
    rwa [Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec] at h2
  have hrep : b.repr x = 0 := by
    ext i
    have := congrFun hvec i
    simp only [Formalism.HermitianLatticesTheory.vecAt, Pi.zero_apply] at this
    simpa using this
  simpa using hrep

theorem fcoord_smul (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x : V) : Formalism.HermitianLatticesTheory.fcoord b X v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.fcoord b X v x := by
  have h : Formalism.HermitianLatticesTheory.vecAt b v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v x := by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  simp only [Formalism.HermitianLatticesTheory.fcoord, h, Matrix.mulVec_smul]

theorem inner_realize (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x y : V) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) =
      ∑ v, (Formalism.HermitianLatticesTheory.majAt b X v x y).re := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fintype.sum_prod_type,
    Fin.sum_univ_two, Formalism.HermitianLatticesTheory.majAt, Complex.re_sum, realize_apply0, realize_apply1]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem majAt_smul (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a a' : K) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (a • x) (a' • y) =
      star (v.embedding a) * v.embedding a' * Formalism.HermitianLatticesTheory.majAt b X v x y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fcoord_smul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Basic

section LinAlg

variable {n : Type} [Fintype n] [DecidableEq n]

def realif (G : Matrix n n ℂ) : Matrix (Fin 2 × n) (Fin 2 × n) ℝ :=
  Matrix.of fun p q => if p.1 = 0 then (if q.1 = 0 then (G p.2 q.2).re else -(G p.2 q.2).im)
    else (if q.1 = 0 then (G p.2 q.2).im else (G p.2 q.2).re)

theorem det_realif (G : Matrix n n ℂ) : (realif G).det = Complex.normSq G.det := by
  let e : Fin 2 × n ≃ n ⊕ n :=
    { toFun := fun p => if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
      invFun := fun s => Sum.elim (fun i => ((0 : Fin 2), i)) (fun i => ((1 : Fin 2), i)) s
      left_inv := by
        rintro ⟨k, i⟩
        fin_cases k <;> rfl
      right_inv := by
        rintro (i | i) <;> rfl }
  let Gre : Matrix n n ℂ := G.map fun z => ((z.re : ℝ) : ℂ)
  let Gim : Matrix n n ℂ := G.map fun z => ((z.im : ℝ) : ℂ)
  let R : Matrix (n ⊕ n) (n ⊕ n) ℂ := ((realif G).map Complex.ofRealHom).submatrix e.symm e.symm
  have hR : R = Matrix.fromBlocks Gre (-Gim) Gim Gre := by
    ext (i | i) (j | j) <;> simp [R, e, Gre, Gim, realif]
  let U : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
    Matrix.fromBlocks 1 1 ((-Complex.I) • (1 : Matrix n n ℂ)) (Complex.I • (1 : Matrix n n ℂ))
  let D : Matrix (n ⊕ n) (n ⊕ n) ℂ := Matrix.fromBlocks G 0 0 (G.map star)
  have hRU : R * U = U * D := by
    rw [hR]
    simp only [U, D, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
      Matrix.zero_mul, Matrix.mul_smul, Matrix.smul_mul, add_zero, zero_add]
    congr 1 <;> ext i j <;> apply Complex.ext <;> simp [Gre, Gim]
  have hU : U.det ≠ 0 := by
    simp only [U, Matrix.det_fromBlocks_one₁₁, Matrix.mul_one]
    rw [neg_smul, sub_neg_eq_add, ← add_smul, Matrix.det_smul, Matrix.det_one, mul_one]
    refine pow_ne_zero _ ?_
    rw [← two_mul]
    exact mul_ne_zero two_ne_zero Complex.I_ne_zero
  have hdet : R.det = D.det := by
    have h := congrArg Matrix.det hRU
    rw [Matrix.det_mul, Matrix.det_mul] at h
    exact mul_right_cancel₀ hU (h.trans (mul_comm _ _))
  have hD : D.det = G.det * star G.det := by
    have hc : G.map star = Gᴴᵀ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    simp only [D, Matrix.det_fromBlocks_zero₂₁, hc, Matrix.det_transpose, Matrix.det_conjTranspose]
  have hR' : R.det = ((realif G).det : ℂ) := by
    simp only [R, Matrix.det_submatrix_equiv_self]
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  apply Complex.ofReal_injective
  rw [← hR', hdet, hD, Complex.star_def, Complex.mul_conj]

end LinAlg

section Fact

variable {P S : Type} [Fintype P] [DecidableEq P] [Fintype S] [DecidableEq S] {j : ℕ}

def gmat (lam : P → S → ℂ) (G : P → Matrix (Fin j) (Fin j) ℂ) :
    Matrix (S × Fin j) (S × Fin j) ℝ :=
  Matrix.of fun p q => ∑ v, (star (lam v p.1) * lam v q.1 * G v p.2 q.2).re

def amat (lam : P → S → ℂ) (eS : S ≃ P × Fin 2) : Matrix (P × Fin 2) (P × Fin 2) ℝ :=
  Matrix.of fun x q => if x.2 = 0 then (lam x.1 (eS.symm q)).re else (lam x.1 (eS.symm q)).im

def bmat (G : P → Matrix (Fin j) (Fin j) ℂ) :
    Matrix ((P × Fin 2) × Fin j) ((P × Fin 2) × Fin j) ℝ :=
  Matrix.of fun x y => if x.1.1 = y.1.1 then realif (G x.1.1) (x.1.2, x.2) (y.1.2, y.2) else 0

theorem det_bmat (G : P → Matrix (Fin j) (Fin j) ℂ) :
    (bmat G).det = ∏ v, Complex.normSq (G v).det := by
  let f : (P × Fin 2) × Fin j ≃ (Fin 2 × Fin j) × P :=
    { toFun := fun x => ((x.1.2, x.2), x.1.1)
      invFun := fun y => ((y.2, y.1.1), y.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : (bmat G).submatrix f.symm f.symm = Matrix.blockDiagonal fun v => realif (G v) := by
    ext ⟨⟨s, k⟩, v⟩ ⟨⟨t, k'⟩, w⟩
    simp only [Matrix.submatrix_apply, Matrix.blockDiagonal_apply, bmat, Matrix.of_apply, f,
      Equiv.coe_fn_symm_mk]
    <;> split_ifs <;> simp_all
  rw [← Matrix.det_submatrix_equiv_self f.symm (bmat G), h, Matrix.det_blockDiagonal]
  simp only [det_realif]

theorem gmat_eq (lam : P → S → ℂ) (G : P → Matrix (Fin j) (Fin j) ℂ) (eS : S ≃ P × Fin 2) :
    (gmat lam G).submatrix (Equiv.prodCongr eS.symm (Equiv.refl (Fin j)))
        (Equiv.prodCongr eS.symm (Equiv.refl (Fin j))) =
      (kroneckerMap (· * ·) (amat lam eS) (1 : Matrix (Fin j) (Fin j) ℝ))ᵀ * bmat G *
        kroneckerMap (· * ·) (amat lam eS) (1 : Matrix (Fin j) (Fin j) ℝ) := by
  ext ⟨p, k⟩ ⟨q, k'⟩
  simp only [Matrix.submatrix_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, gmat,
    Matrix.of_apply]
  conv_rhs =>
    simp [amat, bmat, realif, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, ite_add_ite, Finset.sum_mul, Finset.mul_sum]
  first
  | (refine Finset.sum_congr rfl fun v _ => ?_
     simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
     ring)
  | (simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
     refine Finset.sum_congr rfl fun v _ => ?_
     ring)

end Fact

section DetG

variable {P S : Type} [Fintype P] [DecidableEq P] [Fintype S] [DecidableEq S] {j : ℕ}

theorem det_gmat (lam : P → S → ℂ) (G : P → Matrix (Fin j) (Fin j) ℂ) (eS : S ≃ P × Fin 2) :
    (gmat lam G).det = (amat lam eS).det ^ (2 * j) * ∏ v, Complex.normSq (G v).det := by
  have h := congrArg Matrix.det (gmat_eq lam G eS)
  simp only [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one, det_bmat, Fintype.card_fin] at h
  rw [h]
  ring

end DetG

section NT

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]

theorem isEmpty_real : IsEmpty {w : InfinitePlace K // w.IsReal} := ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2⟩

attribute [local instance] isEmpty_real

def idxE : mixedEmbedding.index K ≃ InfinitePlace K × Fin 2 :=
  (Equiv.emptySum _ _).trans
    (Equiv.prodCongr (Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w) (Equiv.refl _))

def lamK (v : InfinitePlace K) (m : Free.ChooseBasisIndex ℤ (𝓞 K)) : ℂ :=
  v.embedding (integralBasis K m)

open scoped Classical in
open MeasureTheory ZSpan in
theorem abs_det_amat (eS : Free.ChooseBasisIndex ℤ (𝓞 K) ≃ InfinitePlace K × Fin 2) :
    |(amat (lamK K) eS).det| = (2⁻¹) ^ InfinitePlace.nrComplexPlaces K * √|(discr K : ℝ)| := by
  classical
  let e' : mixedEmbedding.index K ≃ Free.ChooseBasisIndex ℤ (𝓞 K) := (idxE K).trans eS.symm
  let A' := (mixedEmbedding.stdBasis K).toMatrix ((mixedEmbedding.latticeBasis K).reindex e'.symm)
  have hvol : volume (fundamentalDomain (mixedEmbedding.latticeBasis K)) = (‖A'.det‖₊ : ENNReal) := by
    rw [← fundamentalDomain_reindex _ e'.symm, ← norm_toNNReal, measure_fundamentalDomain
      ((mixedEmbedding.latticeBasis K).reindex e'.symm) volume (mixedEmbedding.stdBasis K),
      mixedEmbedding.volume_fundamentalDomain_stdBasis, mul_one]
    rfl
  have hA : amat (lamK K) eS = A'.submatrix (idxE K).symm (idxE K).symm := by
    ext ⟨v, r⟩ q
    have hq : e' ((idxE K).symm q) = eS.symm q := by simp [e']
    simp only [amat, of_apply, submatrix_apply, A', Basis.toMatrix_apply, Basis.reindex_apply,
      Equiv.symm_symm, hq, mixedEmbedding.latticeBasis_apply]
    fin_cases r
    · simp [idxE, lamK, mixedEmbedding.mixedEmbedding_apply_isComplex]
    · simp [idxE, lamK, mixedEmbedding.mixedEmbedding_apply_isComplex]
  have h1 := mixedEmbedding.volume_fundamentalDomain_latticeBasis K
  rw [hvol] at h1
  have h2 := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal, ENNReal.coe_toReal, Real.coe_sqrt, coe_nnnorm, coe_nnnorm,
    Int.norm_eq_abs, Real.norm_eq_abs] at h2
  rw [hA, det_submatrix_equiv_self]
  convert h2 using 3

end NT

section Main

variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem zl_span_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (ρ : V →+ E) {ι' : Type} [Fintype ι'] (e : ι' → V) :
    zl ρ (Submodule.span (𝓞 K) (Set.range e)) =
      Submodule.span ℤ (Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
        ρ (integralBasis K p.1 • e p.2)) := by
  have hω : ∀ p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι',
      integralBasis K p.1 • e p.2 = (RingOfIntegers.basis K p.1) • e p.2 := fun p => by
    rw [integralBasis_apply, algebraMap_smul]
  have hspan : (Submodule.span (𝓞 K) (Set.range e)).restrictScalars ℤ =
      Submodule.span ℤ (Set.range fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
        integralBasis K p.1 • e p.2) := by
    rw [← Submodule.span_smul_of_span_eq_top (RingOfIntegers.basis K).span_eq (Set.range e),
      Set.range_smul_range]
    congr 1
    ext x
    simp only [Set.mem_range, hω]
  have hz : zl ρ (Submodule.span (𝓞 K) (Set.range e)) =
      ((Submodule.span (𝓞 K) (Set.range e)).restrictScalars ℤ).map ρ.toIntLinearMap := by
    ext x
    first
    | exact Iff.rfl
    | simp [zl]
  rw [hz, hspan, Submodule.map_span, ← Set.range_comp]
  rfl

theorem linIndep_int {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (ρ : V →+ E) (hρ : Function.Injective ρ) {ι' : Type} [Fintype ι']
    (e : ι' → V) (he : LinearIndependent K e) :
    LinearIndependent ℤ (fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
        ρ (integralBasis K p.1 • e p.2)) := by
  have hω : LinearIndependent ℤ (integralBasis K) := by
    first
    | exact (integralBasis K).linearIndependent.restrict_scalars (by intro a b h; simpa using h)
    | exact (integralBasis K).linearIndependent.restrict_scalars'
  have he' : LinearIndependent ℤ (fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × ι' =>
      integralBasis K p.1 • e p.2) :=
    linearIndependent_smul hω he
  exact he'.map' ρ.toIntLinearMap (LinearMap.ker_eq_bot.2 hρ)

theorem zl_mono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (ρ : V →+ E) {N L : Submodule (𝓞 K) V} (h : N ≤ L) :
    zl ρ N ≤ zl ρ L := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hx
  exact AddSubgroup.mem_map.2 ⟨y, h hy, rfl⟩

theorem rkK_span {j : ℕ} (e : Fin j → V) (he : LinearIndependent K e) :
    rkK (Submodule.span (𝓞 K) (Set.range e)) = j := by
  unfold rkK
  rw [Submodule.span_span_of_tower, finrank_span_eq_card he, Fintype.card_fin]

end Main

theorem factor_one (f j : ℕ) {D : ℝ} (hD : 0 < D) :
    (2 : ℝ) ^ (f * j) * D ^ (-(j : ℝ) / 2) * (((2 : ℝ)⁻¹) ^ f * √D) ^ j = 1 := by
  have h1 : (√D) ^ j = D ^ ((j : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hD.le]
    congr 1
    ring
  have h2 : D ^ (-(j : ℝ) / 2) * D ^ ((j : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hD, neg_div, neg_add_cancel, Real.rpow_zero]
  rw [mul_pow, h1, ← pow_mul, inv_pow]
  have h3 : (2 : ℝ) ^ (f * j) ≠ 0 := by positivity
  calc _ = ((2 : ℝ) ^ (f * j) * ((2 : ℝ) ^ (f * j))⁻¹) * (D ^ (-(j : ℝ) / 2) * D ^ ((j : ℝ) / 2)) := by
        ring
    _ = 1 := by rw [mul_inv_cancel₀ h3, h2, one_mul]

open scoped ComplexOrder in
theorem norm_det_gramPl {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) {j : ℕ} (e : Fin j → V) :
    ‖(gramPl b X v e).det‖ = (gramPl b X v e).det.re := by
  have hpsd : (gramPl b X v e).PosSemidef := by
    let B : Matrix ι (Fin j) ℂ := Matrix.of fun i a => Formalism.HermitianLatticesTheory.fcoord b X v (e a) i
    have hB : gramPl b X v e = Bᴴ * B := by
      ext a c
      simp [B, gramPl, Formalism.HermitianLatticesTheory.majAt, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hB]
    exact Matrix.posSemidef_conjTranspose_mul_self B
  have h0 := hpsd.det_nonneg
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.1 h0
  have hz : (gramPl b X v e).det = ((gramPl b X v e).det.re : ℂ) :=
    Complex.ext (by simp) (by simp [← him])
  conv_lhs => rw [hz]
  rw [Complex.norm_real, Real.norm_of_nonneg hre]

end HeightGram

open HeightGram in
theorem htGram_of (h1 : PlLat) : HtGram := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX j e he
  classical
  set N := Submodule.span (𝓞 K) (Set.range e) with hNdef
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range e)
  have hρ := realize_injective b X hX
  have hrkN : rkK N = j := rkK_span e he
  have hmain : ht b X N = ∏ v, (gramPl b X v e).det.re := by
    obtain ⟨⟨_, hdisc⟩, _, _⟩ := h1 K V ι b X hX N hNfg
    haveI := hdisc
    have hli := linIndep_int (Formalism.HermitianLatticesTheory.realize b X) hρ e he
    have hsp := zl_span_eq (K := K) (Formalism.HermitianLatticesTheory.realize b X) e
    let bN : Basis _ ℤ (zl (Formalism.HermitianLatticesTheory.realize b X) N) :=
      (Basis.span hli).map (LinearEquiv.ofEq _ _ hsp.symm)
    have hbN : ∀ p, (bN p : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) =
        Formalism.HermitianLatticesTheory.realize b X (integralBasis K p.1 • e p.2) := by
      intro p; simp [bN, Basis.span_apply]
    have hcov := Formalism.F.covolEqGram _ (zl (Formalism.HermitianLatticesTheory.realize b X) N) _ bN
    have hgram : Matrix.gram ℝ (fun p => (bN p : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
        gmat (lamK K) (fun v => gramPl b X v e) := by
      ext p q
      simp only [Matrix.gram_apply, hbN, inner_realize, gmat, Matrix.of_apply, majAt_smul, gramPl,
        lamK]
    have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 K)) =
        Fintype.card (InfinitePlace K × Fin 2) := by
      rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank,
        IsTotallyComplex.finrank, Fintype.card_prod, Fintype.card_fin,
        InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, mul_comm]
    let eS := Fintype.equivOfCardEq hcard
    have hdet := det_gmat (lamK K) (fun v => gramPl b X v e) eS
    rw [← hgram] at hdet
    have hsq : (Matrix.gram ℝ (fun p => (bN p : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))).det =
        (|(amat (lamK K) eS).det| ^ j * ∏ v, ‖(gramPl b X v e).det‖) ^ 2 := by
      rw [hdet, mul_pow, ← Finset.prod_pow]
      congr 1
      · rw [← pow_mul, mul_comm j 2, pow_mul, pow_mul, sq_abs]
      · exact Finset.prod_congr rfl fun v _ => Complex.normSq_eq_norm_sq _
    have hcov2 : Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) N) =
        |(amat (lamK K) eS).det| ^ j * ∏ v, ‖(gramPl b X v e).det‖ := by
      rw [hcov, hsq, Real.sqrt_sq (by positivity)]
    have hnPl : nPl K = InfinitePlace.nrComplexPlaces K := by
      unfold nPl
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    have hD : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
    unfold ht
    rw [hcov2, abs_det_amat K eS, hrkN, hnPl]
    simp only [norm_det_gramPl]
    rw [← mul_assoc, factor_one _ _ hD, one_mul]
  refine ⟨hmain, ?_⟩
  intro L hLfg hNL hrkL
  obtain ⟨⟨_, hdiscN⟩, hrkNZ, _⟩ := h1 K V ι b X hX N hNfg
  obtain ⟨⟨_, hdiscL⟩, hrkLZ, _⟩ := h1 K V ι b X hX L hLfg
  haveI := hdiscL
  have hle := zl_mono (Formalism.HermitianLatticesTheory.realize b X) hNL
  have hrkeq : Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) N) = Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) L) := by
    have h3 : rk (Formalism.HermitianLatticesTheory.realize b X) N = rk (Formalism.HermitianLatticesTheory.realize b X) L := by
      rw [hrkNZ, hrkLZ, hrkN, hrkL]
    exact h3
  have hcov := Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol _ _ hle hrkeq
  have hidx : (zl (Formalism.HermitianLatticesTheory.realize b X) N).toAddSubgroup.relIndex
      (zl (Formalism.HermitianLatticesTheory.realize b X) L).toAddSubgroup = N.toAddSubgroup.relIndex L.toAddSubgroup := by
    simp only [zl, AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hρ
  unfold ht
  rw [hrkN, hrkL, hcov, hidx]
  ring

theorem height_gram_determinant : HtGram := htGram_of place_lattice_structure

end Formalism.HN
