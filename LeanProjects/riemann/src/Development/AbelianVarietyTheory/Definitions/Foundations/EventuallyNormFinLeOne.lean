import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion

noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

section Generic

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def htOf (N : Matrix n n A → ℝ≥0) (g : GL n A) : ℝ≥0 :=
  max 1 (max (N (g : Matrix n n A)) (N ((g⁻¹ : GL n A) : Matrix n n A)))

theorem one_le_htOf (N : Matrix n n A → ℝ≥0) (g : GL n A) : 1 ≤ htOf N g := le_max_left _ _

theorem le_htOf (N : Matrix n n A → ℝ≥0) (g : GL n A) : N (g : Matrix n n A) ≤ htOf N g := le_max_of_le_right (le_max_left _ _)

theorem inv_le_htOf (N : Matrix n n A → ℝ≥0) (g : GL n A) :
    N ((g⁻¹ : GL n A) : Matrix n n A) ≤ htOf N g := le_max_of_le_right (le_max_right _ _)

theorem htOf_inv (N : Matrix n n A → ℝ≥0) (g : GL n A) : htOf N g⁻¹ = htOf N g := by
  simp only [htOf, inv_inv]
  rw [max_comm (N _)]

theorem htOf_eq_one {N : Matrix n n A → ℝ≥0} {g : GL n A} :
    htOf N g = 1 ↔ N (g : Matrix n n A) ≤ 1 ∧ N ((g⁻¹ : GL n A) : Matrix n n A) ≤ 1 := by
  simp only [htOf, max_eq_left_iff, max_le_iff]

theorem htOf_mul_le {N : Matrix n n A → ℝ≥0} (hN : ∀ a b, N (a * b) ≤ N a * N b) (g h : GL n A) :
    htOf N (g * h) ≤ htOf N g * htOf N h := by
  show max 1 (max (N ((g * h : GL n A) : Matrix n n A)) (N (((g * h)⁻¹ : GL n A) : Matrix n n A))) ≤ _
  refine max_le (one_le_mul_of_one_le_of_one_le (one_le_htOf N g) (one_le_htOf N h)) (max_le ?_ ?_)
  · rw [Units.val_mul]
    exact (hN _ _).trans (mul_le_mul' (le_htOf N g) (le_htOf N h))
  · rw [mul_inv_rev, Units.val_mul, mul_comm (htOf N g)]
    exact (hN _ _).trans (mul_le_mul' (inv_le_htOf N h) (inv_le_htOf N g))

end Generic

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

section Finite

variable (v : HeightOneSpectrum (𝓞 F))

abbrev FvBar : Type := AlgebraicClosure (Fv F v)

def absBar (x : FvBar F v) : ℝ≥0 := ⟨spectralNorm (Fv F v) (FvBar F v) x, spectralNorm_nonneg x⟩

theorem absBar_mul (x y : FvBar F v) : absBar F v (x * y) = absBar F v x * absBar F v y := by
  let : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  have h := spectralAlgNorm_mul (K := Fv F v) (L := FvBar F v) x y
  exact NNReal.eq h

theorem absBar_add_le (x y : FvBar F v) : absBar F v (x + y) ≤ max (absBar F v x) (absBar F v y) := by
  rw [← NNReal.coe_le_coe, NNReal.coe_max]
  exact isNonarchimedean_spectralNorm x y

theorem absBar_algebraMap (a : Fv F v) : absBar F v (algebraMap (Fv F v) (FvBar F v) a) = ‖a‖₊ := NNReal.eq (spectralNorm_extends a)

theorem absBar_neg (x : FvBar F v) : absBar F v (-x) = absBar F v x := NNReal.eq (spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic x))

theorem absBar_eq_zero {x : FvBar F v} : absBar F v x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    have hpos := spectralNorm_zero_lt hx (Algebra.IsAlgebraic.isAlgebraic (R := Fv F v) x)
    rw [← NNReal.coe_eq_zero] at h
    exact hpos.ne' h
  · rintro rfl
    exact NNReal.eq spectralNorm_zero

def valBar : Valuation (FvBar F v) ℝ≥0 where
  toFun := absBar F v
  map_zero' := (absBar_eq_zero F v).2 rfl
  map_one' := by simpa using absBar_algebraMap F v 1
  map_mul' := absBar_mul F v
  map_add_le_max' := absBar_add_le F v

theorem absBar_le_one_of_monic {x : FvBar F v} (p : Polynomial ℤ) (hp : p.Monic)
    (hx : p.eval₂ (Int.castRingHom _) x = 0) : absBar F v x ≤ 1 := by
  have hint : ∀ m : ℤ, absBar F v (m : FvBar F v) ≤ 1 := fun m => by
    rw [← map_intCast (algebraMap (Fv F v) (FvBar F v)), absBar_algebraMap]
    exact IsUltrametricDist.nnnorm_intCast_le_one _ m
  have hv : ∀ y : FvBar F v, valBar F v y = absBar F v y := fun _ => rfl
  by_contra hlt
  push Not at hlt
  have hsum := hx
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul] at hsum
  simp only [eq_intCast] at hsum
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at hsum
    simp at hsum
  · have hxN : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, ((p.coeff i : ℤ) : FvBar F v) * x ^ i :=
      eq_neg_of_add_eq_zero_right hsum
    have key : absBar F v (x ^ p.natDegree) ≤ absBar F v x ^ (p.natDegree - 1) := by
      rw [hxN, ← hv, Valuation.map_neg]
      refine Valuation.map_sum_le _ fun i hi => ?_
      rw [Valuation.map_mul, Valuation.map_pow, hv, hv]
      have hi' : i ≤ p.natDegree - 1 := Nat.le_pred_of_lt (Finset.mem_range.1 hi)
      calc absBar F v _ * absBar F v x ^ i ≤ 1 * absBar F v x ^ (p.natDegree - 1) :=
            mul_le_mul' (hint _) (pow_le_pow_right₀ hlt.le hi')
        _ = _ := one_mul _
    rw [← hv, Valuation.map_pow, hv] at key
    exact absurd key (not_le.2 (pow_lt_pow_right₀ hlt (Nat.sub_lt hpos one_pos)))

def finEmb (τ : E →ₐ[F] FvBar F v) : Fv F v ⊗[F] E →ₐ[Fv F v] FvBar F v :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) τ fun _ _ => Commute.all _ _

@[simp] theorem finEmb_tmul (τ : E →ₐ[F] FvBar F v) (a : Fv F v) (x : E) :
    finEmb F v τ (a ⊗ₜ[F] x) = algebraMap (Fv F v) (FvBar F v) a * τ x := rfl

def absFin (y : Fv F v ⊗[F] E) : ℝ≥0 :=
  Finset.univ.sup fun τ : E →ₐ[F] FvBar F v => absBar F v (finEmb F v τ y)

theorem le_absFin (τ : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) : absBar F v (finEmb F v τ y) ≤ absFin F v y := Finset.le_sup (f := fun τ : E →ₐ[F] FvBar F v => absBar F v (finEmb F v τ y)) (Finset.mem_univ τ)

theorem absFin_le_iff {y : Fv F v ⊗[F] E} {c : ℝ≥0} :
    absFin F v y ≤ c ↔ ∀ τ : E →ₐ[F] FvBar F v, absBar F v (finEmb F v τ y) ≤ c := by
  simp [absFin, Finset.sup_le_iff]

theorem absFin_mul_le (x y : Fv F v ⊗[F] E) : absFin F v (x * y) ≤ absFin F v x * absFin F v y := (absFin_le_iff F v).2 fun τ => by
  rw [map_mul, absBar_mul]
  exact mul_le_mul' (le_absFin F v τ x) (le_absFin F v τ y)

theorem absFin_add_le (x y : Fv F v ⊗[F] E) : absFin F v (x + y) ≤ max (absFin F v x) (absFin F v y) := (absFin_le_iff F v).2 fun τ => by
  rw [map_add]
  exact (absBar_add_le F v _ _).trans (max_le_max (le_absFin F v τ x) (le_absFin F v τ y))

@[simp] theorem absFin_zero : absFin F v (0 : Fv F v ⊗[F] E) = 0 := le_antisymm ((absFin_le_iff F v).2 fun τ => by
  rw [map_zero, (absBar_eq_zero F v).2 rfl]) (zero_le)

theorem absFin_neg (y : Fv F v ⊗[F] E) : absFin F v (-y) = absFin F v y := by
  simp only [absFin, map_neg, absBar_neg]

theorem absFin_sum_le {ι : Type} (s : Finset ι) (f : ι → Fv F v ⊗[F] E) {c : ℝ≥0}
    (h : ∀ i ∈ s, absFin F v (f i) ≤ c) : absFin F v (∑ i ∈ s, f i) ≤ c := Finset.sum_induction f (fun z => absFin F v z ≤ c)
  (fun a b ha hb => (absFin_add_le F v a b).trans (max_le ha hb)) (by rw [absFin_zero]; exact zero_le) h

theorem absFin_tmul_one (a : Fv F v) : absFin F v (a ⊗ₜ[F] (1 : E)) = ‖a‖₊ := by
  have : Nonempty (E →ₐ[F] FvBar F v) := ⟨IsAlgClosed.lift⟩
  simp only [absFin, finEmb_tmul, map_one, mul_one, absBar_algebraMap]
  exact Finset.sup_const Finset.univ_nonempty _

@[simp] theorem absFin_one : absFin F v (1 : Fv F v ⊗[F] E) = 1 := by
  rw [Algebra.TensorProduct.one_def, absFin_tmul_one, nnnorm_one]

theorem absFin_tmul_le (a : Fv F v) (x : 𝓞 E) : absFin F v (a ⊗ₜ[F] (x : E)) ≤ ‖a‖₊ := (absFin_le_iff F v).2 fun τ => by
  have hx2 : IsIntegral ℤ (x : E) := x.2
  obtain ⟨p, hp, hpx⟩ := hx2
  have h0 := congrArg (τ : E →+* FvBar F v) hpx
  rw [Polynomial.hom_eval₂, map_zero, RingHom.ext_int ((τ : E →+* FvBar F v).comp _) (Int.castRingHom _)] at h0
  rw [finEmb_tmul, absBar_mul, absBar_algebraMap]
  exact mul_le_of_le_one_right zero_le (absBar_le_one_of_monic F v p hp h0)

def normFin {m n : Type} [Fintype m] [Fintype n] (y : Matrix m n (Fv F v ⊗[F] E)) : ℝ≥0 :=
  Finset.univ.sup fun p : m × n => absFin F v (y p.1 p.2)

theorem normFin_le_iff {m n : Type} [Fintype m] [Fintype n] {y : Matrix m n (Fv F v ⊗[F] E)} {c : ℝ≥0} :
    normFin F v y ≤ c ↔ ∀ i j, absFin F v (y i j) ≤ c := by
  simp [normFin, Finset.sup_le_iff]

theorem absFin_le_normFin {m n : Type} [Fintype m] [Fintype n] (y : Matrix m n (Fv F v ⊗[F] E)) (i : m) (j : n) :
    absFin F v (y i j) ≤ normFin F v y := (normFin_le_iff F v).1 le_rfl i j

theorem normFin_mul_le {m n p : Type} [Fintype m] [Fintype n] [Fintype p] (x : Matrix m n (Fv F v ⊗[F] E))
    (y : Matrix n p (Fv F v ⊗[F] E)) : normFin F v (x * y) ≤ normFin F v x * normFin F v y := (normFin_le_iff F v).2 fun i k => by
  rw [Matrix.mul_apply]
  exact absFin_sum_le F v _ _ fun j _ => (absFin_mul_le F v _ _).trans
    (mul_le_mul' (absFin_le_normFin F v x i j) (absFin_le_normFin F v y j k))

theorem normFin_one_le {n : Type} [Fintype n] [DecidableEq n] :
    normFin F v (1 : Matrix n n (Fv F v ⊗[F] E)) ≤ 1 := (normFin_le_iff F v).2 fun i j => by
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

def htFin {n : Type} [Fintype n] [DecidableEq n] (g : GL n (Fv F v ⊗[F] E)) : ℝ≥0 := htOf (normFin F v) g

end Finite

section Infinite

variable {F} (E) in

abbrev EmbOver (w : InfinitePlace F) : Type := {τ : E →+* ℂ // τ.comp (algebraMap F E) = w.embedding}

variable (w : InfinitePlace F)

instance nonempty_embOver : Nonempty (EmbOver E w) := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  let τ : E →ₐ[F] ℂ := IsAlgClosed.lift
  exact ⟨⟨τ, RingHom.ext τ.commutes⟩⟩

variable {F w}

def infEmb (τ : EmbOver E w) : w.Completion ⊗[F] E →+* ℂ :=
  letI : Algebra F ℂ := w.embedding.toAlgebra
  (Algebra.TensorProduct.productMap
    ({ InfinitePlace.Completion.extensionEmbedding w with
        commutes' := fun a => InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm a) } :
      w.Completion →ₐ[F] ℂ)
    ({ τ.1 with commutes' := fun a => RingHom.congr_fun τ.2 a } : E →ₐ[F] ℂ)).toRingHom

omit [NumberField F] [NumberField E] in
@[simp] theorem infEmb_tmul (τ : EmbOver E w) (a : w.Completion) (x : E) :
    infEmb τ (a ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding w a * τ.1 x := rfl

def opNorm {n : Type} [Fintype n] [DecidableEq n] (y : Matrix n n ℂ) : ℝ≥0 :=
  ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y‖₊

theorem opNorm_mul_le {n : Type} [Fintype n] [DecidableEq n] (x y : Matrix n n ℂ) :
    opNorm (x * y) ≤ opNorm x * opNorm y := by
  unfold opNorm
  rw [map_mul]
  exact nnnorm_mul_le _ _

theorem opNorm_one_le {n : Type} [Fintype n] [DecidableEq n] : opNorm (1 : Matrix n n ℂ) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  exact ContinuousLinearMap.opNNNorm_le_bound _ 1 fun x => by simp

variable (F w)

open Classical in

def normInf {n : Type} [Fintype n] [DecidableEq n] (y : Matrix n n (w.Completion ⊗[F] E)) : ℝ≥0 :=
  Finset.univ.sup fun τ : EmbOver E w => opNorm (y.map (infEmb τ))

theorem normInf_le_iff {n : Type} [Fintype n] [DecidableEq n] {y : Matrix n n (w.Completion ⊗[F] E)} {c : ℝ≥0} :
    normInf F w y ≤ c ↔ ∀ τ : EmbOver E w, opNorm (y.map (infEmb τ)) ≤ c := by
  simp [normInf, Finset.sup_le_iff]

theorem normInf_mul_le {n : Type} [Fintype n] [DecidableEq n] (x y : Matrix n n (w.Completion ⊗[F] E)) :
    normInf F w (x * y) ≤ normInf F w x * normInf F w y := (normInf_le_iff F w).2 fun τ => by
  rw [Matrix.map_mul]
  exact (opNorm_mul_le _ _).trans (mul_le_mul' ((normInf_le_iff F w).1 le_rfl τ) ((normInf_le_iff F w).1 le_rfl τ))

theorem normInf_one_le {n : Type} [Fintype n] [DecidableEq n] :
    normInf F w (1 : Matrix n n (w.Completion ⊗[F] E)) ≤ 1 := (normInf_le_iff F w).2 fun τ => by
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  exact opNorm_one_le

theorem opNorm_map_conj_le {n : Type} [Fintype n] [DecidableEq n] (y : Matrix n n ℂ) :
    opNorm (y.map (starRingEnd ℂ)) ≤ opNorm y := by
  unfold opNorm
  refine ContinuousLinearMap.opNNNorm_le_bound _ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y‖₊ fun x => ?_
  let xs : EuclideanSpace ℂ n := WithLp.toLp 2 fun i => starRingEnd ℂ (x i)
  have hcomp : ∀ i, (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (y.map (starRingEnd ℂ)) x) i =
      starRingEnd ℂ ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y xs) i) := fun i => by
    simp [xs, Matrix.mulVec, dotProduct, map_sum]
  have h1 : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (y.map (starRingEnd ℂ)) x‖₊ =
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y xs‖₊ := by
    rw [EuclideanSpace.nnnorm_eq, EuclideanSpace.nnnorm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcomp i]
    congr 1
    exact Subtype.ext (Complex.norm_conj _)
  have h2 : ‖xs‖₊ = ‖x‖₊ := by
    rw [EuclideanSpace.nnnorm_eq, EuclideanSpace.nnnorm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact Subtype.ext (Complex.norm_conj _)
  rw [h1, ← h2]
  exact ContinuousLinearMap.le_opNNNorm _ _

variable {F w} in

theorem infEmb_eq_or_conj {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (τ τ' : EmbOver E w) :
    infEmb τ' = infEmb τ ∨ infEmb τ' = (starRingEnd ℂ).comp (infEmb τ) := by
  obtain ⟨hF, hE, h2, hc⟩ := h
  have hw : w.IsReal := hF.isReal w
  have hext : ∀ a : w.Completion, starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w a) =
      InfinitePlace.Completion.extensionEmbedding w a := fun a => by
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
    exact Complex.conj_ofReal _
  have hwe : (starRingEnd ℂ).comp w.embedding = w.embedding :=
    (ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hw))
  let : Algebra F ℂ := w.embedding.toAlgebra
  let toA : EmbOver E w → (E →ₐ[F] ℂ) := fun t => { t.1 with commutes' := fun a => RingHom.congr_fun t.2 a }
  have toA_inj : ∀ s t : EmbOver E w, toA s = toA t → s = t := fun s t e =>
    Subtype.ext (RingHom.ext fun x => by simpa [toA] using DFunLike.congr_fun e x)
  let ρ : EmbOver E w := ⟨(starRingEnd ℂ).comp τ.1, by rw [RingHom.comp_assoc, τ.2, hwe]⟩
  have hρ : ρ ≠ τ := by
    intro e
    have hr : ComplexEmbedding.IsReal τ.1 := ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
      have := RingHom.congr_fun (congrArg Subtype.val e) x
      simpa [ComplexEmbedding.conjugate_coe_eq, ρ] using this)
    exact (InfinitePlace.isComplex_mk_iff.1 (hE.isComplex (InfinitePlace.mk τ.1))) hr
  have key : τ' = τ ∨ τ' = ρ := by
    by_contra hne
    push Not at hne
    have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
    have hcard : Nat.card (E →ₐ[F] ℂ) ≤ 2 := by
      rw [← Field.finSepDegree_eq_of_isAlgClosed F E ℂ, ← h2]
      exact Field.finSepDegree_le_finrank F E
    have hne0 : Nat.card (E →ₐ[F] ℂ) ≠ 0 := by
      rw [← Field.finSepDegree_eq_of_isAlgClosed F E ℂ]
      exact NeZero.ne _
    have : Finite (E →ₐ[F] ℂ) := Nat.finite_of_card_ne_zero hne0
    let := Fintype.ofFinite (E →ₐ[F] ℂ)
    classical
    have h3 : ({toA τ', toA τ, toA ρ} : Finset (E →ₐ[F] ℂ)).card = 3 :=
      Finset.card_eq_three.2 ⟨_, _, _, fun e => hne.1 (toA_inj _ _ e), fun e => hne.2 (toA_inj _ _ e),
        fun e => hρ (toA_inj _ _ e).symm, rfl⟩
    have := Finset.card_le_univ ({toA τ', toA τ, toA ρ} : Finset (E →ₐ[F] ℂ))
    rw [h3, ← Nat.card_eq_fintype_card] at this
    omega
  rcases key with e | e
  · left
    rw [e]
  · right
    apply RingHom.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      rw [e, infEmb_tmul]
      simp only [RingHom.comp_apply]
      rw [infEmb_tmul, map_mul, hext]
      try rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {F w} in

theorem normInf_eq_opNorm {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (τ : EmbOver E w) {n : Type} [Fintype n] [DecidableEq n]
    (y : Matrix n n (w.Completion ⊗[F] E)) : normInf F w y = opNorm (y.map (infEmb τ)) := by
  refine le_antisymm ((normInf_le_iff F w).2 fun τ' => ?_) ((normInf_le_iff F w).1 le_rfl τ)
  rcases infEmb_eq_or_conj h τ τ' with e | e
  · rw [e]
  · rw [e, RingHom.coe_comp, ← Matrix.map_map]
    exact opNorm_map_conj_le _

def htInf {n : Type} [Fintype n] [DecidableEq n] (g : GL n (w.Completion ⊗[F] E)) : ℝ≥0 := htOf (normInf F w) g

end Infinite

section Global

def evFin (v : HeightOneSpectrum (𝓞 F)) : AF F →ₐ[F] Fv F v := (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v).comp (sndA F)

def evInf (w : InfinitePlace F) : AF F →ₐ[F] w.Completion := (GlobalTheory.AutFunCompare.evW w).comp (fstA F)

variable (E) in

def compFin (v : HeightOneSpectrum (𝓞 F)) : AF F ⊗[F] E →+* Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E)).toRingHom

variable (E) in

def compInf (w : InfinitePlace F) : AF F ⊗[F] E →+* w.Completion ⊗[F] E :=
  (Algebra.TensorProduct.map (evInf F w) (AlgHom.id F E)).toRingHom

theorem eventually_absFin_le_one (z : AF F ⊗[F] E) :
    ∀ᶠ v in Filter.cofinite, absFin F v (compFin F E v z) ≤ 1 := by
  induction z using TensorProduct.induction_on with
  | zero => exact Filter.Eventually.of_forall fun v => by rw [map_zero, absFin_zero]; exact zero_le
  | add x y hx hy =>
    exact (hx.and hy).mono fun v h => by
      rw [map_add]
      exact (absFin_add_le F v _ _).trans (max_le h.1 h.2)
  | tmul a x =>
    have hxa : IsAlgebraic ℤ x := by
      first
        | exact Algebra.IsAlgebraic.isAlgebraic x
        | exact (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
    obtain ⟨m, hm, hint⟩ := hxa.exists_integral_multiple
    have hmF : (m : F) ≠ 0 := Int.cast_ne_zero.2 hm
    have hxe : (m : F)⁻¹ • (m • x) = x := by
      rw [← Int.cast_smul_eq_zsmul F m x, smul_smul, inv_mul_cancel₀ hmF, one_smul]
    refine (sndA F ((m : F)⁻¹ • a)).2.mono fun v hv => ?_
    have e1 : compFin F E v (a ⊗ₜ[F] x) = evFin F v ((m : F)⁻¹ • a) ⊗ₜ[F] (m • x) := by
      have e0 : compFin F E v (a ⊗ₜ[F] x) = evFin F v a ⊗ₜ[F] x := rfl
      rw [e0, map_smul, TensorProduct.smul_tmul, hxe]
    rw [e1]
    refine (absFin_tmul_le F v _ (⟨m • x, hint⟩ : 𝓞 E)).trans ?_
    have hv' : Valued.v (evFin F v ((m : F)⁻¹ • a)) ≤ 1 := hv
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
    exact Valued.toNormedField.norm_le_one_iff.2 hv'

variable {n : Type} [Fintype n] [DecidableEq n]

theorem eventually_normFin_le_one (y : Matrix n n (AF F ⊗[F] E)) :
    ∀ᶠ v in Filter.cofinite, normFin F v (y.map (compFin F E v)) ≤ 1 := (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
    eventually_absFin_le_one F (y i j)).mono fun v hv => (normFin_le_iff F v).2 fun i j => by
  simpa using hv i j

theorem finite_mulSupport_htFin (g : GL n (AF F ⊗[F] E)) :
    (Function.mulSupport fun v => htFin F v (bc (compFin F E v) g)).Finite := by
  have h1 := eventually_normFin_le_one F (E := E) (g : Matrix n n (AF F ⊗[F] E))
  have h2 := eventually_normFin_le_one F (E := E) ((g⁻¹ : GL n (AF F ⊗[F] E)) : Matrix n n (AF F ⊗[F] E))
  refine Filter.eventually_cofinite.1 ((h1.and h2).mono fun v hv => ?_)
  show htOf (normFin F v) _ = 1
  exact htOf_eq_one.2 ⟨hv.1, hv.2⟩

def heightGL (g : GL n (AF F ⊗[F] E)) : ℝ≥0 :=
  (∏ w, htInf F w (bc (compInf F E w) g)) * ∏ᶠ v, htFin F v (bc (compFin F E v) g)

theorem one_le_heightGL (g : GL n (AF F ⊗[F] E)) : 1 ≤ heightGL F g := one_le_mul_of_one_le_of_one_le (Finset.one_le_prod' fun w _ => one_le_htOf _ _)
  (one_le_finprod' fun v => one_le_htOf _ _)

theorem heightGL_inv (g : GL n (AF F ⊗[F] E)) : heightGL F g⁻¹ = heightGL F g := by
  simp only [heightGL, htInf, htFin, map_inv, htOf_inv]

theorem heightGL_eq_one_iff {g : GL n (AF F ⊗[F] E)} : heightGL F g = 1 ↔
    (∀ w, htInf F w (bc (compInf F E w) g) = 1) ∧ ∀ v, htFin F v (bc (compFin F E v) g) = 1 := by
  have hfin := finite_mulSupport_htFin F g
  have hA : ∀ w ∈ (Finset.univ : Finset (InfinitePlace F)), 1 ≤ htInf F w (bc (compInf F E w) g) :=
    fun w _ => one_le_htOf _ _
  have hB : ∀ v ∈ hfin.toFinset, 1 ≤ htFin F v (bc (compFin F E v) g) := fun v _ => one_le_htOf _ _
  rw [heightGL, finprod_eq_prod _ hfin, mul_eq_one_iff_of_one_le (Finset.one_le_prod' hA) (Finset.one_le_prod' hB),
    Finset.prod_eq_one_iff_of_one_le' hA, Finset.prod_eq_one_iff_of_one_le' hB]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun w => h1 w (Finset.mem_univ _), fun v => ?_⟩
    by_contra hv
    exact hv (h2 v (hfin.mem_toFinset.2 hv))
  · rintro ⟨h1, h2⟩
    exact ⟨fun w _ => h1 w, fun v _ => h2 v⟩

@[simp] theorem heightGL_one : heightGL F (1 : GL n (AF F ⊗[F] E)) = 1 := by
  refine (heightGL_eq_one_iff F).2 ⟨fun w => ?_, fun v => ?_⟩
  · rw [map_one]
    show htOf (normInf F w) 1 = 1
    exact htOf_eq_one.2 ⟨by rw [Units.val_one]; exact normInf_one_le F w,
      by rw [inv_one, Units.val_one]; exact normInf_one_le F w⟩
  · rw [map_one]
    show htOf (normFin F v) 1 = 1
    exact htOf_eq_one.2 ⟨by rw [Units.val_one]; exact normFin_one_le F v,
      by rw [inv_one, Units.val_one]; exact normFin_one_le F v⟩

theorem heightGL_mul_le (g h : GL n (AF F ⊗[F] E)) : heightGL F (g * h) ≤ heightGL F g * heightGL F h := by
  have hN : ∀ w, htInf F w (bc (compInf F E w) (g * h)) ≤
      htInf F w (bc (compInf F E w) g) * htInf F w (bc (compInf F E w) h) := fun w => by
    rw [map_mul]
    exact htOf_mul_le (normInf_mul_le F w) _ _
  have hM : ∀ v, htFin F v (bc (compFin F E v) (g * h)) ≤
      htFin F v (bc (compFin F E v) g) * htFin F v (bc (compFin F E v) h) := fun v => by
    rw [map_mul]
    exact htOf_mul_le (normFin_mul_le F v) _ _
  have fg := finite_mulSupport_htFin F (g * h)
  have fg1 := finite_mulSupport_htFin F g
  have fh1 := finite_mulSupport_htFin F h
  have e1 : (∏ w, htInf F w (bc (compInf F E w) (g * h))) ≤
      (∏ w, htInf F w (bc (compInf F E w) g)) * ∏ w, htInf F w (bc (compInf F E w) h) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod' fun w _ => hN w
  have e2 : (∏ᶠ v, htFin F v (bc (compFin F E v) (g * h))) ≤
      (∏ᶠ v, htFin F v (bc (compFin F E v) g)) * ∏ᶠ v, htFin F v (bc (compFin F E v) h) := by
    rw [← finprod_mul_distrib fg1 fh1]
    exact finprod_le_finprod fg (fun _ => zero_le) ((fg1.union fh1).subset (Function.mulSupport_mul _ _)) hM
  unfold heightGL
  calc _ ≤ _ := mul_le_mul' e1 e2
    _ = _ := mul_mul_mul_comm _ _ _ _

theorem heightGL_mul_of_eq_one {k : GL n (AF F ⊗[F] E)} (hk : heightGL F k = 1) (g : GL n (AF F ⊗[F] E)) :
    heightGL F (g * k) = heightGL F g ∧ heightGL F (k * g) = heightGL F g := by
  have hk' : heightGL F k⁻¹ = 1 := (heightGL_inv F k).trans hk
  constructor
  · refine le_antisymm ((heightGL_mul_le F g k).trans (by rw [hk, mul_one])) ?_
    calc heightGL F g = heightGL F (g * k * k⁻¹) := by rw [mul_inv_cancel_right]
      _ ≤ heightGL F (g * k) * heightGL F k⁻¹ := heightGL_mul_le F _ _
      _ = heightGL F (g * k) := by rw [hk', mul_one]
  · refine le_antisymm ((heightGL_mul_le F k g).trans (by rw [hk, one_mul])) ?_
    calc heightGL F g = heightGL F (k⁻¹ * (k * g)) := by rw [inv_mul_cancel_left]
      _ ≤ heightGL F k⁻¹ * heightGL F (k * g) := heightGL_mul_le F _ _
      _ = heightGL F (k * g) := by rw [hk', one_mul]

end Global

end GlobalTheory.AdelicU

end
