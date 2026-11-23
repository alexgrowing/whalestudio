import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SymplecticAdelicFormBiadditiveAlternatingRationa
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPoint
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FormMatch

open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem sum_four_eq_trace {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (P : Matrix (Fin n) (Fin n) A)
    (Q : Matrix (Fin m) (Fin m) A) (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a = (P * (y.map σ)ᵀ * Q * x).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem sum_unitary {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (Q g : Matrix (Fin m) (Fin m) A)
    (P P' k : Matrix (Fin n) (Fin n) A) (hP : P = 1) (hP' : P' = 1) (hg : (g.map σ)ᵀ * Q * g = Q)
    (hk : (k.map σ)ᵀ * P' * k = P') (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ ((g * y * k) c b) * Q c d * (g * x * k) d a =
      ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a := by
  subst hP hP'
  rw [sum_four_eq_trace, sum_four_eq_trace]
  have hk1 : (k.map σ)ᵀ * k = 1 := by simpa only [Matrix.mul_one] using hk
  have hk2 : k * (k.map σ)ᵀ = 1 := mul_eq_one_comm.mp hk1
  have hg' : ∀ R : Matrix (Fin m) (Fin n) A, (g.map σ)ᵀ * (Q * (g * R)) = Q * R := by
    intro R
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.one_mul, Matrix.mul_assoc, hg']
  conv_lhs => rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hk2, Matrix.mul_one]

theorem sum_one_four {A : Type} [CommRing A] {m n : ℕ} (u : Fin m → Fin n → A) (Q : Fin m → Fin m → A)
    (x : Fin m → Fin n → A) :
    ∑ a, ∑ b, ∑ c, ∑ d, (1 : Matrix (Fin n) (Fin n) A) a b * u c b * Q c d * x d a =
      ∑ k, ∑ d, ∑ c, x d k * Q c d * u c k := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_eq_single a (fun b hb => by simp [Matrix.one_apply_ne (Ne.symm hb)])]
  simp only [Matrix.one_apply_eq, one_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

variable {D : D7} {S T : HSp D}

theorem hO_actO (hS : S.gram = 1) (h : GA D S) (g : GA D T) (w w' : WO S T) :
    hO S T (actO S T h g w) (actO S T h g w') = hO S T w w' := by
  have hinv : ((HSpace.gram S)⁻¹).map (incA D) = 1 := by
    rw [hS, Matrix.inv_eq_left_inv (Matrix.mul_one 1), Matrix.map_one _ (map_zero _) (map_one _)]
  have key := sum_unitary (cA D) ((HSpace.gram T).map (incA D)) (Formalism.L2.Theta.mt T g)
    (((HSpace.gram S)⁻¹).map (incA D)) 1 (Formalism.L2.Theta.mt S h⁻¹) hinv rfl ?hg ?hk w w'
  · unfold hO actO
    simpa only [Matrix.map_apply] using key
  · have hu := g.2
    exact hu
  · have hu : ((Formalism.L2.Theta.mt S h⁻¹).map (cA D))ᵀ * (HSpace.gram S).map (incA D) * Formalism.L2.Theta.mt S h⁻¹ =
        (HSpace.gram S).map (incA D) := (h⁻¹).2
    have h1 : (HSpace.gram S).map (incA D) = 1 := by
      rw [hS]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1] at hu
    exact hu

theorem hRat_eq (C : Ctx S T) (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T yᵀ y'ᵀ = ∑ k, herm C.X.Gm (y k) (y' k) := by
  unfold GlobalTheory.LatVac.hRat ReciprocityTheory.ChartRestriction.G.FD.herm
  rw [C.m.gS, C.m.gT, Matrix.inv_eq_left_inv (Matrix.mul_one 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_eq_single k (fun b hb => by simp [Matrix.one_apply_ne (Ne.symm hb)])]
  simp only [Matrix.one_apply_eq, one_mul, Matrix.transpose_apply]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  have hs : star (y' k c) = ReciprocityTheory.ChartRestriction.G.FD.cc (y' k c) := rfl
  rw [hs]
  ring

theorem sum_EF (C : Ctx S T) (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    ∑ k, EF C.X (y k) (y' k) = -Algebra.trace ℚ D.host.F
      (Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T yᵀ y'ᵀ)) := by
  simp only [GlobalTheory.ThFr.EF_def]
  rw [← map_sum, ← Finset.mul_sum, ← hRat_eq C, C.m.ka, Algebra.trace_trace,
    show -(2 * D.host.xi0 / 2) * GlobalTheory.LatVac.hRat S T yᵀ y'ᵀ = -(D.host.xi0 * GlobalTheory.LatVac.hRat S T yᵀ y'ᵀ) by ring,
    map_neg]

theorem symplO_rat (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplO S T (ratW T S M) (ratW T S N) = algebraMap D.host.F (AF D.host.F)
      (Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T M N)) := by
  rw [← (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 (ratW T S M) (ratW T S N)]
  have h2 : symplOH S T (ratW T S M) (ratW T S N) = algebraMap D.host.F (AF D.host.F)
      (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T M N)) :=
    GlobalTheory.OrientedFormLaws.symplOH_rat M N
  rw [h2, ← map_add]
  congr 1
  ring

theorem re_match {m n : ℕ} (ξ : ℂ) (Q : Fin m → Fin m → ℂ) (x y : Fin m → Fin n → ℂ) :
    ∑ k, 2 * (conj (-ξ) * ∑ a, ∑ b, conj (x a k) * conj (Q b a) * conj (conj (y b k))).re =
      -(2 * (ξ * ∑ k, ∑ d, ∑ c, x d k * Q c d * conj (y c k)).re) := by
  have key : ∀ k, conj (-ξ) * ∑ a, ∑ b, conj (x a k) * conj (Q b a) * conj (conj (y b k)) =
      conj (-ξ * ∑ a, ∑ b, x a k * Q b a * conj (y b k)) := by
    intro k
    simp only [map_mul, map_sum, map_neg]
  simp only [key, Complex.conj_re, neg_mul, Complex.neg_re, mul_neg, Finset.sum_neg_distrib, neg_inj]
  rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.mul_sum]

theorem EFR_realPt (C : Ctx S T) (w w' : WO S T) :
    EFR C.X (C.realPt w) (C.realPt w') = -omO S T (piW C.θ T S w) (piW C.θ T S w') := by
  rw [omO_apply, ← Finset.sum_neg_distrib]
  unfold EFR Ctx.realPt compAt
  rw [← C.m.e.sum_comp]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hS1 : gramAt D S τ = 1 := by
    unfold gramAt
    rw [C.m.gS]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hom : -omAt S T τ (piW C.θ T S w τ) (piW C.θ T S w' τ) = ∑ k, 2 * (conj (-(tauE D τ D.host.xi0)) *
      ∑ a, ∑ b, conj (piW C.θ T S w τ a k) * conj (gramAt D T τ b a) *
        conj (conj (piW C.θ T S w' τ b k))).re := by
    rw [re_match (tauE D τ D.host.xi0) (gramAt D T τ) (piW C.θ T S w τ) (piW C.θ T S w' τ), neg_inj]
    unfold omAt hAt
    have h4 := GlobalTheory.OrientedChar.trace_four ((gramAt D S τ)⁻¹) (piW C.θ T S w' τ) (gramAt D T τ) (piW C.θ T S w τ)
    have h5 := sum_one_four (fun c b => starRingEnd ℂ (piW C.θ T S w' τ c b)) (gramAt D T τ) (piW C.θ T S w τ)
    rw [h4, hS1, Matrix.inv_eq_left_inv (Matrix.mul_one 1)]
    exact congrArg (fun s => 2 * (tauE D τ D.host.xi0 * s).re) h5
  rw [hom]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hx : -(2 * D.host.xi0 / 2) = -D.host.xi0 := by ring
  simp only [Equiv.symm_apply_apply, ReciprocityTheory.ChartRestriction.G.FD.hermC, C.m.e_emb τ,
    NumberField.ComplexEmbedding.conjugate_coe_eq, C.m.ka, C.m.gT, Matrix.transpose_apply, Matrix.map_apply,
    hx, map_neg]
  rfl

theorem symplO_eq_add (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := ((GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 x y).symm

theorem symplOH_finW (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    symplOH S T (finW S T y) (finW S T y') = pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F)
      (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T yᵀ y'ᵀ))) := by
  have hf : ∀ z : Matrix (Fin S.rank) (Fin T.rank) D.host.E, finW S T z = GlobalTheory.LatVac.finTens 1 zᵀ :=
    fun z => rfl
  have h := (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 (finW S T y) (finW S T y')
  rw [hf, hf, GlobalTheory.LatVac.symplO_finTens] at h
  simp only [one_mul] at h
  rw [hf, hf]
  have key : ∀ X Y : AF D.host.F, X + X = Y + Y → X = Y := by
    intro X Y hXY
    have h2 : (2 : D.host.F) • X = (2 : D.host.F) • Y := by rw [two_smul, two_smul, hXY]
    have h3 := congrArg (fun Z => (2 : D.host.F)⁻¹ • Z) h2
    simpa only [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : D.host.F) ≠ 0), one_smul] using h3
  have hp : ∀ u v : Af D.host.F, pairA D.host.F 0 u + pairA D.host.F 0 v = pairA D.host.F 0 (u + v) := by
    intro u v
    unfold pairA
    exact Prod.ext (add_zero _) rfl
  apply key
  rw [h, hp, ← map_add]
  congr 2
  ring

theorem forms_match : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∀ (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (t : D.host.F), symplO S T (ratW T S yᵀ) (ratW T S y'ᵀ) = algebraMap D.host.F (AF D.host.F) t → ∑ k, EF C.X (y k) (y' k) = -Algebra.trace ℚ D.host.F t) ∧ (∀ w w' : WO S T, IsRealPt w → IsRealPt w' → C.ψ (symplOH S T w w') = cexp (π * I * (EFR C.X (C.realPt w) (C.realPt w') : ℝ))) ∧ (∀ y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.ψ (symplOH S T (finW S T y) (finW S T y')) = cexp (-(π * I * ((∑ k, EF C.X (y k) (y' k) : ℚ) : ℂ)))) ∧ (∀ w u : WO S T, IsRealPt w → IsFinPt u → symplO S T w u = 0 ∧ symplO S T u w = 0) ∧ (∀ w : WO S T, symplO S T w w = 0) ∧ (∀ w w' w'' : WO S T, symplO S T (w + w') w'' = symplO S T w w'' + symplO S T w' w'' ∧ symplO S T w w' = -symplO S T w' w) ∧ (∀ (h : GA D S) (g : GA D T) (w w' : WO S T), symplO S T (actO S T h g w) (actO S T h g w') = symplO S T w w') ∧ ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.realPt (ratW T S yᵀ) = embR C.X y ∧ IsFinPt (finW S T y) ∧ IsRealPt (ratW T S yᵀ - finW S T y) ∧ ∀ y', finW S T (y + y') = finW S T y + finW S T y' := by
  intro D S T C
  have hadd := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have halt := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T
  have htr : ∀ t : D.host.F, Algebra.trace ℚ D.host.F (1 / 2 * t) = 1 / 2 * Algebra.trace ℚ D.host.F t := by
    intro t
    rw [show (1 / 2 : D.host.F) = algebraMap ℚ D.host.F (1 / 2) by simp, ← Algebra.smul_def, map_smul,
      smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, halt.2.2.2.1, fun w w' w'' => ⟨halt.1 w w' w'', halt.2.2.1 w w'⟩, ?_, ?_⟩
  · intro y y' t ht
    rw [symplO_rat] at ht
    have : Nontrivial (AF D.host.F) := by
      unfold AF AdeleRing
      infer_instance
    rw [sum_EF C, (algebraMap D.host.F (AF D.host.F)).injective ht]
  · intro w w' hw _
    rw [GlobalTheory.OrientedChar.char_symplOH D C.θ C.ψ C.inf C.std S T w w' (Or.inl hw), EFR_realPt C]
    congr 1
    push_cast
    ring
  · intro y y'
    rw [symplOH_finW, GlobalTheory.StdRat.stdChar_fin_rat D C.ψ C.std, sum_EF C, htr]
    congr 1
    push_cast
    ring
  · intro w u hw hu
    have h0 : symplOH S T w u = 0 := hadd.2.2.2.2.2.2.2.2 w u hw hu
    have h1 : symplO S T w u = 0 := by rw [← hadd.2.2.2.1 w u, h0, add_zero]
    exact ⟨h1, by rw [halt.2.2.1 u w, h1, neg_zero]⟩
  · intro h g w w'
    unfold symplO
    rw [hO_actO C.m.gS]
  · intro y
    refine ⟨?_, finRat_inf S T yᵀ, ?_, ?_⟩
    · funext σ k a
      unfold Ctx.realPt compAt
      obtain ⟨τ, rfl⟩ := C.m.e.surjective σ
      rw [Equiv.symm_apply_apply]
      have e := congrFun (congrFun (congrFun (piW_ratW C.inf S T yᵀ) τ) a) k
      simp only [Matrix.map_apply, embR, C.m.e_emb τ, NumberField.ComplexEmbedding.conjugate_coe_eq]
      congr 1
    · show (ratW T S yᵀ - finW S T y).map (finPart D) = 0
      have e := finRat_fin S T yᵀ
      ext i j
      have e2 := congrFun (congrFun e i) j
      simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.zero_apply] at e2 ⊢
      rw [← e2]
      exact sub_self _
    · intro y'
      ext a k
      simp only [finW, Matrix.of_apply, Matrix.add_apply, TensorProduct.tmul_add]

end GlobalTheory.FormMatch
