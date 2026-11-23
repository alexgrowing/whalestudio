import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LatVacArith

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

theorem trace_mixedEmbedding (y : F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (mixedEmbedding F y) = (Algebra.trace ℚ F y : ℝ) := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi]
  simp only [Algebra.trace_complex_apply]
  have h1 : ((Algebra.trace ℚ F y : ℚ) : ℂ) = ∑ σ : F →+* ℂ, σ y := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := y)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ fun _ => rfl).symm
  have h2 : ((Algebra.trace ℚ F y : ℚ) : ℝ) = ∑ σ : F →+* ℂ, (σ y).re := by
    have := congrArg Complex.re h1
    rw [Complex.re_sum] at this
    rw [← this]; simp
  rw [h2, ← Finset.sum_fiberwise Finset.univ (fun φ : F →+* ℂ => InfinitePlace.mk φ) (fun φ => (φ y).re)]
  have h3 : ∀ w : InfinitePlace F, ∑ i with InfinitePlace.mk i = w, (i y).re = (w.mult : ℝ) * (w.embedding y).re := by
    intro w
    rw [Finset.sum_congr rfl (g := fun _ => (w.embedding y).re), Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]
    intro φ hφ
    have hw := (Finset.mem_filter.1 hφ).2
    subst hw
    rcases InfinitePlace.embedding_mk_eq φ with h | h
    · rw [h]
    · rw [h]; simp [ComplexEmbedding.conjugate_coe_eq]
  simp only [h3]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F => w.IsReal)]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul]
    simp only [mixedEmbedding.mixedEmbedding_apply_isReal]
    rw [← InfinitePlace.embedding_of_isReal_apply w.2, Complex.ofReal_re]
    first
      | exact Algebra.trace_self_apply _ _
      | (have := Algebra.trace_algebraMap (R := ℝ) (S := ℝ) ((InfinitePlace.embedding_of_isReal w.2) y); simpa using this)
  · let e : {w : InfinitePlace F // w.IsComplex} ≃ {w : InfinitePlace F // ¬ w.IsReal} :=
      Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex.symm
    refine Fintype.sum_equiv e _ _ fun w => ?_
    have h := InfinitePlace.mult_isComplex w
    rw [show ((e w : InfinitePlace F)) = w.1 from rfl, h]
    simp

theorem psi_fin_rat {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) := by
  have e : pairA F 0 (algebraMap F (Af F) x) =
      algebraMap F (AF F) x + pairA F (algebraMap F (Ainf F) (-x)) 0 := by
    refine Prod.ext ?_ (add_zero _).symm
    show (0 : Ainf F) = algebraMap F (Ainf F) x + algebraMap F (Ainf F) (-x)
    rw [map_neg, add_neg_cancel]
  have hat : At (evI F) (pairA F (algebraMap F (Ainf F) (-x)) 0) := by
    intro u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  rw [e, AddChar.map_add_eq_mul, hψ.2.1, one_mul, hψ.2.2 _ hat]
  have h2 : evI F (pairA F (algebraMap F (Ainf F) (-x)) 0) = mixedEmbedding F (-x) := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (Ainf F) (-x)) = _
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rw [h2, trace_mixedEmbedding, map_neg]
  congr 1
  push_cast
  ring

theorem psi_int {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : F)
    (ht : ∀ a : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F ((a : F) * t) = k) (α : Af F) (hα : α ∈ intAf F) :
    ψ (pairA F 0 (α * algebraMap F (Af F) t)) = 1 := by
  refine GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hψ.1 t (fun a => ?_) α hα
  obtain ⟨k, hk⟩ := ht a
  rw [psi_fin_rat hψ, hk, Complex.exp_eq_one_iff]
  exact ⟨k, by push_cast; ring⟩

section Gen
variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem hTens_vecMulVec (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (x x' : Fin n → E) (y y' : Fin d → E) :
    GlobalTheory.WeilM.hTens σ JA JB (Matrix.vecMulVec x y) (Matrix.vecMulVec x' y') = form σ JA x x' * form σ JB y y' := by
  unfold GlobalTheory.WeilM.hTens form
  simp only [Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_incM (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (θ : E) (x x' : Fin n → E) (y y' : Fin d → E) :
    GlobalTheory.WeilM.symp (R := AF F) (cA σ) (inclR (F := F) (AF F) θ) (incM F JA) (incM F JB)
      (incM F (Matrix.vecMulVec x y)) (incM F (Matrix.vecMulVec x' y')) =
      algebraMap F (AF F) (Algebra.trace F E (θ * (form σ JA x x' * form σ JB y y'))) := by
  have ht : ∀ e : E, Algebra.trace (AF F) (AF F ⊗[F] E) (inclR (F := F) (AF F) e) =
      algebraMap F (AF F) (Algebra.trace F E e) := fun e => by
    show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  rw [← hTens_vecMulVec, ← ht, GlobalTheory.WeilM.symp]
  simp only [GlobalTheory.WeilM.hTens, incM, Matrix.map_apply, hc, map_mul, map_sum]
end Gen

section Main
variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem trace_int_of_lat (σ : E →ₐ[F] E) (B : Base F E) {n d r s r' s' : ℕ} (X : Spc F E n) (Y : Spc F E d)
    (hX : X.IsHerm σ B r s) (hY : Y.IsSkew σ B r' s') (θ : 𝓞 E) {x x' : Fin n → E} (hx : x ∈ X.L) (hx' : x' ∈ X.L)
    {y y' : Fin d → E} (hy : y ∈ Y.L) (hy' : y' ∈ Y.L) (a : 𝓞 F) :
    ∃ k : ℤ, Algebra.trace ℚ F ((a : F) * Algebra.trace F E ((θ : E) * (form σ X.J x x' * form σ Y.J y y'))) = k := by
  have hfX : IsIntegral ℤ (form σ X.J x x') := (hX.dual x).1 hx x' hx'
  have ha : IsIntegral ℤ (algebraMap F E (a : F)) := (NumberField.RingOfIntegers.isIntegral_coe a).algebraMap
  let o : 𝓞 E := ⟨algebraMap F E (a : F) * (θ : E) * form σ X.J x x',
    (ha.mul (NumberField.RingOfIntegers.isIntegral_coe θ)).mul hfX⟩
  have h := (hY.dual y).1 hy y' hy' o
  have e : (a : F) * Algebra.trace F E ((θ : E) * (form σ X.J x x' * form σ Y.J y y')) =
      Algebra.trace F E ((o : E) * form σ Y.J y y') := by
    rw [← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def]
    congr 1
    show _ = algebraMap F E (a : F) * (θ : E) * form σ X.J x x' * form σ Y.J y y'
    ring
  rw [e, Algebra.trace_trace]
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact ⟨k, by rw [← hk]; simp⟩

theorem liftV_one_mul (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (w : AF F) :
    GlobalTheory.LatVac.liftV v 1 * w = GlobalTheory.LatVac.liftV v (GlobalTheory.AdelicU.evFin F v w) := by
  refine Prod.ext ?_ ?_
  · change (0 : Ainf F) * w.1 = 0
    rw [zero_mul]
  · change GlobalTheory.AdelicU.singleFin v 1 * w.2 = GlobalTheory.AdelicU.singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v w.2)
    apply GlobalTheory.AdelicU.af_ext
    intro u
    rw [map_mul]
    by_cases hu : u = v
    · subst hu
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, zero_mul]

theorem eq_liftV_of_at {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {a : AF F} (ha : At (GlobalTheory.AdelicU.evFin F v) a) :
    a = GlobalTheory.LatVac.liftV v 1 * a := by
  have h := ha (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h
  exact h

theorem psi_gen (σ : E →ₐ[F] E) (B : Base F E) {n d r s r' s' : ℕ} (X : Spc F E n) (Y : Spc F E d)
    (hX : X.IsHerm σ B r s) (hY : Y.IsSkew σ B r' s') (hstd : IsStd B.ψ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (θ : 𝓞 E) (b : AF F)
    (hb : GlobalTheory.AdelicU.evFin F v b ∈ v.adicCompletionIntegers F) {a a' : AF F}
    (ha : At (GlobalTheory.AdelicU.evFin F v) a) (hav : GlobalTheory.AdelicU.evFin F v a ∈ v.adicCompletionIntegers F)
    (hav' : GlobalTheory.AdelicU.evFin F v a' ∈ v.adicCompletionIntegers F)
    {x x' : Fin n → E} (hx : x ∈ X.L) (hx' : x' ∈ X.L) {y y' : Fin d → E} (hy : y ∈ Y.L) (hy' : y' ∈ Y.L) :
    B.ψ (b * GlobalTheory.WeilM.symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F Y.J)
      (a • incM F (Matrix.vecMulVec x y)) (a' • incM F (Matrix.vecMulVec x' y'))) = 1 := by
  rw [GlobalTheory.LatVac.symp_smul_smul, symp_incM]
  set t := Algebra.trace F E ((θ : E) * (form σ X.J x x' * form σ Y.J y y')) with ht
  set c := b * a * a' with hc
  have hcv : GlobalTheory.AdelicU.evFin F v c ∈ v.adicCompletionIntegers F := by
    rw [hc, map_mul, map_mul]
    exact mul_mem (mul_mem hb hav) hav'
  have key : b * (a * a' * algebraMap F (AF F) t) =
      pairA F 0 (GlobalTheory.AdelicU.singleFin v (GlobalTheory.AdelicU.evFin F v c) * algebraMap F (Af F) t) := by
    have e1 : b * (a * a' * algebraMap F (AF F) t) = t • (GlobalTheory.LatVac.liftV v 1 * c) := by
      rw [Algebra.smul_def, hc]
      conv_lhs => rw [eq_liftV_of_at ha]
      ring
    rw [e1, liftV_one_mul, ← LinearMap.map_smul]
    show pairA F 0 (GlobalTheory.AdelicU.singleFin v (t • GlobalTheory.AdelicU.evFin F v c)) = _
    rw [LinearMap.map_smul, Algebra.smul_def, mul_comm]
  rw [key]
  refine psi_int hstd t (trace_int_of_lat σ B X Y hX hY θ hx hx' hy hy') _ fun w => ?_
  by_cases hw : w = v
  · subst hw
    rw [GlobalTheory.AdelicU.evalV_singleFin_self]
    exact hcv
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw]
    exact zero_mem _

end Main

end GlobalTheory.LatVacArith

namespace GlobalTheory.LatVacArith

section Final
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symp_add_left (σ : E →ₐ[F] E) {n d : ℕ} (ξ : AE F E) (JA : Matrix (Fin n) (Fin n) (AE F E))
    (JB : Matrix (Fin d) (Fin d) (AE F E)) (x x' y : Matrix (Fin n) (Fin d) (AE F E)) :
    GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB (x + x') y =
      GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB x y + GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB x' y := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add]

theorem symp_add_right (σ : E →ₐ[F] E) {n d : ℕ} (ξ : AE F E) (JA : Matrix (Fin n) (Fin n) (AE F E))
    (JB : Matrix (Fin d) (Fin d) (AE F E)) (x y y' : Matrix (Fin n) (Fin d) (AE F E)) :
    GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB x (y + y') =
      GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB x y + GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB x y' := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  simp only [Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem symp_zero_left (σ : E →ₐ[F] E) {n d : ℕ} (ξ : AE F E) (JA : Matrix (Fin n) (Fin n) (AE F E))
    (JB : Matrix (Fin d) (Fin d) (AE F E)) (y : Matrix (Fin n) (Fin d) (AE F E)) :
    GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB 0 y = 0 := by
  have h := symp_add_left σ ξ JA JB 0 0 y
  rw [add_zero] at h
  calc _ = (GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB 0 y + GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB 0 y) -
        GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB 0 y := by abel
    _ = 0 := by rw [← h, sub_self]

theorem symp_zero_right (σ : E →ₐ[F] E) {n d : ℕ} (ξ : AE F E) (JA : Matrix (Fin n) (Fin n) (AE F E))
    (JB : Matrix (Fin d) (Fin d) (AE F E)) (x : Matrix (Fin n) (Fin d) (AE F E)) :
    GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB x 0 = 0 := by
  have h := symp_add_right σ ξ JA JB x 0 0
  rw [add_zero] at h
  calc _ = (GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB x 0 + GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB x 0) -
        GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB x 0 := by abel
    _ = 0 := by rw [← h, sub_self]

theorem symp_neg_left (σ : E →ₐ[F] E) {n d : ℕ} (ξ : AE F E) (JA : Matrix (Fin n) (Fin n) (AE F E))
    (JB : Matrix (Fin d) (Fin d) (AE F E)) (x y : Matrix (Fin n) (Fin d) (AE F E)) :
    GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB (-x) y = -GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB x y := by
  have h := symp_add_left σ ξ JA JB x (-x) y
  rw [add_neg_cancel, symp_zero_left] at h
  linear_combination -h

theorem symp_neg_right (σ : E →ₐ[F] E) {n d : ℕ} (ξ : AE F E) (JA : Matrix (Fin n) (Fin n) (AE F E))
    (JB : Matrix (Fin d) (Fin d) (AE F E)) (x y : Matrix (Fin n) (Fin d) (AE F E)) :
    GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB x (-y) = -GlobalTheory.WeilM.symp (R := AF F) (cA σ) ξ JA JB x y := by
  have h := symp_add_right σ ξ JA JB x y (-y)
  rw [add_neg_cancel, symp_zero_right] at h
  linear_combination -h

theorem psi_symp_latAtV : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (θ : 𝓞 E) (b : AF F),
    GlobalTheory.AdelicU.evFin F v b ∈ v.adicCompletionIntegers F →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ γ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      B.ψ (b * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ') = 1 := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY v θ b hb γ hγ γ' hγ'
  have step : ∀ z' ∈ {z | ∃ a : AF F, At (GlobalTheory.AdelicU.evFin F v) a ∧ GlobalTheory.AdelicU.evFin F v a ∈ v.adicCompletionIntegers F ∧
      ∃ x ∈ X.L, ∃ y ∈ Y.L, z = a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (Matrix.vecMulVec x y)},
      ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, B.ψ (b * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ z') = 1 := by
    intro z' hz' γ hγ
    obtain ⟨a', -, ha', x', hx', y', hy', rfl⟩ := hz'
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
      exact psi_gen σ B X Y hX hY hB.std v θ b hb ha hav ha' hx hx' hy hy'
    | zero => rw [symp_zero_left, mul_zero, AddChar.map_zero_eq_one]
    | add x y _ _ hx hy =>
      rw [symp_add_left, mul_add, AddChar.map_add_eq_mul, hx, hy, one_mul]
    | neg x _ hx =>
      rw [symp_neg_left, mul_neg, AddChar.map_neg_eq_inv, hx, inv_one]
  induction hγ' using AddSubgroup.closure_induction with
  | mem z hz => exact step z hz γ hγ
  | zero => rw [symp_zero_right, mul_zero, AddChar.map_zero_eq_one]
  | add x y _ _ hx hy =>
    rw [symp_add_right, mul_add, AddChar.map_add_eq_mul, hx, hy, one_mul]
  | neg x _ hx =>
    rw [symp_neg_right, mul_neg, AddChar.map_neg_eq_inv, hx, inv_one]

end Final

end GlobalTheory.LatVacArith

end
