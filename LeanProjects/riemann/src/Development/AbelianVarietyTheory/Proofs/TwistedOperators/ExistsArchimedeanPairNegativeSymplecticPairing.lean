import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAtEvIPiInfEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical TensorProduct

namespace GlobalTheory.WrongSignPair

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_tmul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (e : E) :
    piInf τ (a ⊗ₜ[F] e) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 e := rfl

private theorem star_extensionEmbedding_eq (h : IsCMExt F E σ) {w : InfinitePlace F} (x : w.Completion) :
    star (InfinitePlace.Completion.extensionEmbedding w x) = InfinitePlace.Completion.extensionEmbedding w x := by
  have h' := h
  obtain ⟨hF, -⟩ := h'
  have hw : w.IsReal := hF.isReal w
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
  exact Complex.conj_ofReal _

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  have hconj := h
  obtain ⟨-, -, -, hconj⟩ := hconj
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have hz : cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [cA]
    rw [hz, piInf_tmul, piInf_tmul, star_mul', star_extensionEmbedding_eq h, hconj]
  | add x y hx hy => simp only [map_add, hx, hy, star_add]

private theorem trace_pi_real_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) :
    Algebra.trace ℝ (ι → ℝ) f = ∑ i, f i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun ℝ ι), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  simp

theorem trace_evI [IsTotallyReal F] (a : AF F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) =
      ∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re := by
  have hreal : ∀ v : InfinitePlace F, v.IsReal := IsTotallyReal.isReal
  haveI : IsEmpty {v : InfinitePlace F // v.IsComplex} :=
    ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.2 v.2) (hreal v.1)⟩
  rw [Algebra.trace_prod_apply]
  have h2 : (evI F a).2 = 0 := Subsingleton.elim _ _
  rw [h2, map_zero, add_zero, trace_pi_real_eq_sum]
  rw [← Fintype.sum_equiv (Equiv.subtypeUnivEquiv hreal) (fun v => (evI F a).1 v)
    (fun w => (InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re) (fun v => ?_)]
  simp only [evI, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  show _ = (InfinitePlace.Completion.extensionEmbedding v.1 (a.1 v.1)).re
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply v.2, Complex.ofReal_re]

theorem trace_evI_trace (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : AE F E) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) z)) =
      ∑ w : InfinitePlace F, 2 * (piInf (τ w) z).re := by
  have hF : IsTotallyReal F := by
    have h' := h
    obtain ⟨hF, -⟩ := h'
    exact hF
  rw [trace_evI]
  refine Finset.sum_congr rfl fun w _ => ?_
  set t := Algebra.trace (AF F) (AE F E) z with ht
  have key : piInf (τ w) (algebraMap (AF F) (AE F E) t) = piInf (τ w) z + star (piInf (τ w) z) := by
    rw [ht, ← GlobalTheory.GaussMean.OneVec.add_sigR (AF F) h z, map_add, ← piInf_cA h]
    congr 2
  have hal : piInf (τ w) (algebraMap (AF F) (AE F E) t) =
      InfinitePlace.Completion.extensionEmbedding w (t.1 w) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, piInf_tmul, map_one,
      mul_one]
  rw [hal] at key
  rw [key, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

private theorem piInf_inclR_twisted_operators {w : InfinitePlace F} (τ : EmbOver E w) (e : E) :
    piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  have h1 : inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e := rfl
  have h2 : (1 : AF F).1 w = 1 := rfl
  rw [h1, piInf_tmul, h2, map_one, one_mul]

theorem piInf_hTens (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {n d : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) (u u' : Matrix (Fin n) (Fin d) (AE F E)) :
    piInf τ (GlobalTheory.WeilM.hTens (cA σ) (incM F J) (incM F K) u u') =
      ∑ i, ∑ j, ∑ k, ∑ l, u.map (piInf τ) i j * J.map τ.1 i k * K.map τ.1 j l * star (u'.map (piInf τ) k l) := by
  simp only [GlobalTheory.WeilM.hTens, incM, Matrix.map_apply, map_sum, map_mul, piInf_cA h, piInf_inclR_twisted_operators]

theorem sum_rank_one {n d : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (x x' : Fin n → ℂ)
    (y y' : Fin d → ℂ) :
    ∑ i, ∑ j, ∑ k, ∑ l, vecMulVec x y i j * G i k * H j l * star (((-Complex.I) • vecMulVec x' y') k l) =
      (x ⬝ᵥ G *ᵥ star x') * (y ⬝ᵥ (Complex.I • H) *ᵥ star y') := by
  have hI : star (-Complex.I) = Complex.I := by
    rw [star_neg]
    exact (congrArg Neg.neg Complex.conj_I).trans (neg_neg _)
  simp only [dotProduct, mulVec, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul, star_mul', hI,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem star_dotProduct_mulVec_star_comm {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : ∀ i j, star (G j i) = G i j)
    (u v : Fin n → ℂ) : star (u ⬝ᵥ G *ᵥ star v) = v ⬝ᵥ G *ᵥ star u := by
  simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
  first
  | (rw [Finset.sum_comm]
     refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
     rw [hG]; ring)
  | (refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
     rw [hG]; ring)

private theorem dotProduct_mulVec_star_invariant {n : ℕ} {G θ : Matrix (Fin n) (Fin n) ℂ} (hθ : θᵀ * G * θ.map star = G)
    (u v : Fin n → ℂ) : (θ *ᵥ u) ⬝ᵥ G *ᵥ star (θ *ᵥ v) = u ⬝ᵥ G *ᵥ star v := by
  have hs : star (θ *ᵥ v) = θ.map star *ᵥ star v := by
    ext i
    simp [mulVec, dotProduct, star_sum, star_mul']
  rw [hs, ← Matrix.vecMul_transpose θ u, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [hθ]

theorem majorant_im {n : ℕ} {G θ : Matrix (Fin n) (Fin n) ℂ} (hG : ∀ i j, star (G j i) = G i j) (h : IsCartan G θ)
    (x : Fin n → ℂ) : ((θ *ᵥ x) ⬝ᵥ G *ᵥ star x).im = 0 := by
  obtain ⟨h1, h2, -⟩ := h
  have e1 : (θ *ᵥ x) ⬝ᵥ G *ᵥ star x = x ⬝ᵥ G *ᵥ star (θ *ᵥ x) := by
    conv_lhs => rw [← dotProduct_mulVec_star_invariant h2 (θ *ᵥ x) x, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [← star_dotProduct_mulVec_star_comm hG (θ *ᵥ x) x] at e1
  exact Complex.conj_eq_iff_im.mp e1.symm

private theorem mul_vecMulVec_mul_transpose' {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin d) (Fin d) ℂ)
    (x : Fin n → ℂ) (y : Fin d → ℂ) : A * vecMulVec x y * Cᵀ = vecMulVec (A *ᵥ x) (C *ᵥ y) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  first
  | (rw [Finset.sum_comm]
     exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)
  | exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private theorem re_pos_im_zero_of_isCartan {n : ℕ} {G θ : Matrix (Fin n) (Fin n) ℂ} (hG : ∀ i j, star (G j i) = G i j)
    (h : IsCartan G θ) {x : Fin n → ℂ} (hx : x ≠ 0) :
    0 < (x ⬝ᵥ G *ᵥ star (θ *ᵥ x)).re ∧ (x ⬝ᵥ G *ᵥ star (θ *ᵥ x)).im = 0 := by
  have hi := majorant_im hG h x
  have hp := h.2.2 x hx
  rw [← star_dotProduct_mulVec_star_comm hG (θ *ᵥ x) x, Complex.star_def, Complex.conj_re, Complex.conj_im, hi, neg_zero]
  exact ⟨hp, rfl⟩

theorem exists_neg_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → 0 < n → 0 < d →
    ∀ (ε' : InfinitePlace F → ℤˣ) (w : InfinitePlace F), ε' w = -1 →
    ∃ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u ∧ At (evI F) u' ∧
      (∀ w', u'.map (piInf (B.emb w')) =
        (((ε' w' : ℤ) : ℂ) * Complex.I) • (X.θ w' * u.map (piInf (B.emb w')) * (W.θ w')ᵀ)) ∧
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (GlobalTheory.WeilM.symp (cA σ) (-1) (incM F X.J) (incM F W.J) u u')) < 0 := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW hn hd ε' w hw
  have h : IsCMExt F E σ := hB.cm
  have hconj : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x) := by
    have h' := h
    obtain ⟨-, -, -, hconj⟩ := h'
    exact hconj
  have lift : ∀ c : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ, ∃ z : Matrix (Fin n) (Fin d) (AE F E),
      At (evI F) z ∧ ∀ w', z.map (piInf (B.emb w')) = c w' := by
    intro c
    have hz := fun i j => GlobalTheory.ThK.exists_at_evI_piInf_eq F E σ h B.emb (fun w' => c w' i j)
    choose z hz1 hz2 using hz
    refine ⟨z, ?_, ?_⟩
    · intro a ha
      ext i j
      exact hz1 i j a ha
    · intro w'
      ext i j
      exact hz2 i j w'
  let x : Fin n → ℂ := Pi.single ⟨0, hn⟩ 1
  let y : Fin d → ℂ := Pi.single ⟨0, hd⟩ 1
  have hx : x ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hn⟩
    simp [x] at this
  have hy : y ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hd⟩
    simp [y] at this
  obtain ⟨u, hu1, hu2⟩ := lift (fun w' => if w' = w then vecMulVec x y else 0)
  obtain ⟨u', hu'1, hu'2⟩ := lift (fun w' => (((ε' w' : ℤ) : ℂ) * Complex.I) •
    (X.θ w' * (if w' = w then vecMulVec x y else 0) * (W.θ w')ᵀ))
  have hu : ∀ w', u.map (piInf (B.emb w')) = if w' = w then vecMulVec x y else 0 := fun w' => hu2 w'
  have hu' : ∀ w', u'.map (piInf (B.emb w')) = (((ε' w' : ℤ) : ℂ) * Complex.I) •
      (X.θ w' * (if w' = w then vecMulVec x y else 0) * (W.θ w')ᵀ) := fun w' => hu'2 w'
  refine ⟨u, u', hu1, hu'1, fun w' => by rw [hu' w', hu w'], ?_⟩
  have hJ : ∀ i j, star ((X.J.map (B.emb w).1) j i) = (X.J.map (B.emb w).1) i j := by
    intro i j
    simp only [Matrix.map_apply]
    rw [← hconj, hX.herm]
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hK : ∀ i j, star ((Complex.I • W.J.map (B.emb w).1) j i) = (Complex.I • W.J.map (B.emb w).1) i j := by
    intro i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [star_mul', hI, ← hconj, hW.skew, map_neg]
    ring
  obtain ⟨hPr, hPi⟩ := re_pos_im_zero_of_isCartan hJ (hX.cartan w) hx
  obtain ⟨hQr, hQi⟩ := re_pos_im_zero_of_isCartan hK (hW.cartan w) hy
  have hs : (((ε' w : ℤ) : ℂ) * Complex.I) = -Complex.I := by
    rw [hw]
    simp
  have hmain : piInf (B.emb w) (GlobalTheory.WeilM.hTens (cA σ) (incM F X.J) (incM F W.J) u u') =
      (x ⬝ᵥ (X.J.map (B.emb w).1) *ᵥ star (X.θ w *ᵥ x)) *
        (y ⬝ᵥ (Complex.I • W.J.map (B.emb w).1) *ᵥ star (W.θ w *ᵥ y)) := by
    rw [piInf_hTens h, hu w, hu' w, if_pos rfl, hs, mul_vecMulVec_mul_transpose', sum_rank_one]
  have hzero : ∀ w', w' ≠ w → piInf (B.emb w') (GlobalTheory.WeilM.hTens (cA σ) (incM F X.J) (incM F W.J) u u') = 0 := by
    intro w' hne
    rw [piInf_hTens h, hu w', if_neg hne]
    simp
  simp only [GlobalTheory.WeilM.symp]
  rw [trace_evI_trace h B.emb, Finset.sum_eq_single w]
  · rw [map_mul, map_neg, map_one, neg_one_mul, hmain, Complex.neg_re, Complex.mul_re, hPi, zero_mul, sub_zero]
    nlinarith [mul_pos hPr hQr]
  · intro w' _ hne
    rw [map_mul, hzero w' hne, mul_zero, Complex.zero_re, mul_zero]
  · intro hw'
    exact absurd (Finset.mem_univ w) hw'

end GlobalTheory.WrongSignPair
