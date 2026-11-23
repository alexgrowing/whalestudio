import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMatrixIntegralCompLinearEquivDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjAverageUnipotentLocallyConstantCompactSupporStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralLeviConstantTerm

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical Kronecker
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtAdj

section Generic

variable {H : Type} [Group H]

theorem rStab_conj (u : H → ℂ) : rStab (fun x => starRingEnd ℂ (u x)) = rStab u := by
  ext k
  constructor
  · intro hk x
    exact (starRingEnd ℂ).injective (hk x)
  · intro hk x
    show starRingEnd ℂ (u (x * k)) = starRingEnd ℂ (u x)
    rw [hk x]

theorem finsum_conj {α : Type} (g : α → ℂ) : ∑ᶠ q, starRingEnd ℂ (g q) = starRingEnd ℂ (∑ᶠ q, g q) :=
  (AddMonoidHom.map_finsum_of_injective (starRingEnd ℂ).toAddMonoidHom (starRingEnd ℂ).injective g).symm

theorem hint_conj (K : Subgroup H) (u : H → ℂ) :
    hint K (fun x => starRingEnd ℂ (u x)) = starRingEnd ℂ (hint K u) := by
  unfold hint
  rw [rStab_conj, map_mul, map_inv₀, map_natCast, finsum_conj]

theorem avg_conj (u : H → ℂ) : avg (fun x => starRingEnd ℂ (u x)) = starRingEnd ℂ (avg u) := by
  unfold avg
  rw [rStab_conj, map_mul, map_inv₀, map_natCast, finsum_conj]

end Generic

theorem det_lr {k : Type} [Field k] {a b : ℕ} (A : Matrix (Fin a) (Fin a) k) (B : Matrix (Fin b) (Fin b) k)
    (L : Matrix (Fin a) (Fin b) k →ₗ[k] Matrix (Fin a) (Fin b) k) (hL : ∀ X, L X = A * X * B) :
    LinearMap.det L = A.det ^ b * B.det ^ a := by
  let e : Matrix (Fin a) (Fin b) k ≃ₗ[k] (Fin a × Fin b → k) := (LinearEquiv.curry k k (Fin a) (Fin b)).symm
  have h : (e.toLinearMap ∘ₗ L ∘ₗ e.symm.toLinearMap) = Matrix.toLin' (A ⊗ₖ Bᵀ) := by
    apply LinearMap.ext
    intro v
    funext ⟨i, j⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hL, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
    show (A * (Matrix.of fun l c => v (l, c)) * B) i j = _
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [← LinearMap.det_conj L e, h, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose,
    Fintype.card_fin, Fintype.card_fin]

variable {E : Type} [Field E] [NumberField E]

theorem absHalf_one (w : Pl E) : absHalf w (1 : w.adicCompletion E) = 1 := by
  have h := GlobalTheory.LeviDesc.absHalf_mul E w 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  have h0 := GlobalTheory.LeviDesc.absHalf_ne_zero' w (1 : w.adicCompletion E)
  exact (mul_right_cancel₀ h0 (by rw [one_mul]; exact h)).symm

theorem absHalf_inv_mul (w : Pl E) {x : w.adicCompletion E} (hx : x ≠ 0) :
    absHalf w x⁻¹ * absHalf w x = 1 := by
  rw [← GlobalTheory.LeviDesc.absHalf_mul E w _ _ (inv_ne_zero hx) hx, inv_mul_cancel₀ hx, absHalf_one]

theorem conj_absHalf (w : Pl E) (x : w.adicCompletion E) : starRingEnd ℂ (absHalf w x) = absHalf w x := by
  unfold absHalf
  exact Complex.conj_ofReal _

variable [IsCMField E]

def negL {a b : ℕ} {w : Pl E} (m : GLw a w × GLw b w) :
    Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E) where
  toFun X := -(m.1.val * X * (m.2⁻¹).val)
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul, neg_add]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem det_inv_val {k : ℕ} {w : Pl E} (g : GLw k w) : (g⁻¹).val.det = (g.val.det)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]

theorem det_ne_zero {k : ℕ} {w : Pl E} (g : GLw k w) : g.val.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero

theorem v_det_negL {a b : ℕ} {w : Pl E} (m : GLw a w × GLw b w) :
    Valued.v (LinearMap.det (negL m)) = Valued.v (m.1.val.det ^ b / m.2.val.det ^ a) := by
  have h : LinearMap.det (negL m) = (-m.1.val).det ^ b * (m.2⁻¹).val.det ^ a :=
    det_lr _ _ _ fun X => by simp [negL, Matrix.neg_mul]
  rw [h, det_inv_val, Matrix.det_neg, Fintype.card_fin, div_eq_mul_inv, map_mul, map_mul, map_pow, map_mul, map_pow,
    map_pow, map_pow, map_inv₀, map_inv₀, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, inv_pow]

theorem det_negL_ne_zero {a b : ℕ} {w : Pl E} (m : GLw a w × GLw b w) : LinearMap.det (negL m) ≠ 0 := by
  intro h0
  have h := v_det_negL m
  rw [h0, map_zero] at h
  exact div_ne_zero (pow_ne_zero _ (det_ne_zero m.1)) (pow_ne_zero _ (det_ne_zero m.2))
    ((Valuation.zero_iff _).1 h.symm)

theorem ct_adj {n a b : ℕ} (h : a + b = n) (w : Pl E) (F : GLw n w → ℂ)
    (hF : ∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' F) (m : GLw a w × GLw b w) :
    ct h w (fun y => starRingEnd ℂ (F y⁻¹)) m = starRingEnd ℂ (ct h w F m⁻¹) := by
  obtain ⟨hU, hcs⟩ := GlobalTheory.T.conjAverage_unipotent_locallyConstant_compactSupport E n a b h w F hF m⁻¹
  have hJ := GlobalTheory.T.normalisedMatrixIntegral_comp_linearEquiv_det E w a b (negL m)
    (fun X => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) F (blk h w m⁻¹ X)) (det_negL_ne_zero m) hU hcs
  have hpt : ∀ X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)),
      avg (fun k : GlobalTheory.LFun.KGL w n => starRingEnd ℂ (F ((((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k))⁻¹))) =
      starRingEnd ℂ (GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) F (blk h w m⁻¹ (negL m (Multiplicative.toAdd X)))) := by
    intro X
    unfold GlobalTheory.LeviDesc.cavg
    rw [← avg_conj]
    congr 1
    funext k
    have e : ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)⁻¹ =
        (k : GLw n w)⁻¹ * blk h w m⁻¹ (negL m (Multiplicative.toAdd X)) * k := by
      have e2 : blk h w m⁻¹ (negL m (Multiplicative.toAdd X)) = (blk h w m (Multiplicative.toAdd X))⁻¹ :=
        (CtLevel.blk_inv h w m _).symm
      rw [e2]
      group
    rw [e]
  have hD0 : m.1.val.det ^ b / m.2.val.det ^ a ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (det_ne_zero m.1)) (pow_ne_zero _ (det_ne_zero m.2))
  have hinv : (m⁻¹).1.val.det ^ b / (m⁻¹).2.val.det ^ a = (m.1.val.det ^ b / m.2.val.det ^ a)⁻¹ := by
    rw [Prod.fst_inv, Prod.snd_inv, det_inv_val, det_inv_val, inv_pow, inv_pow, inv_div, div_eq_mul_inv, inv_inv, mul_comm,
      div_eq_mul_inv]
  have hc : absHalf w (LinearMap.det (negL m)) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) :=
    GlobalTheory.BCT.AbsHalfInv.absHalf_congr (v_det_negL m)
  have h1 : hint (intMat a b w) (fun X => avg fun k : GlobalTheory.LFun.KGL w n =>
        starRingEnd ℂ (F (((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)⁻¹))) =
      starRingEnd ℂ (hint (intMat a b w) fun X =>
        GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) F (blk h w m⁻¹ (negL m (Multiplicative.toAdd X)))) := by
    rw [← hint_conj]
    congr 1
    funext X
    exact hpt X
  have hJ' : (hint (intMat a b w) fun X =>
      GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) F (blk h w m⁻¹ (negL m (Multiplicative.toAdd X)))) =
      (absHalf w (LinearMap.det (negL m)) ^ 2)⁻¹ * hint (intMat a b w) (fun X =>
        GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) F (blk h w m⁻¹ (Multiplicative.toAdd X))) := hJ
  show absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * hint (intMat a b w) (fun X => avg fun k : GlobalTheory.LFun.KGL w n =>
        starRingEnd ℂ (F (((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)⁻¹))) =
      starRingEnd ℂ (absHalf w ((m⁻¹).1.val.det ^ b / (m⁻¹).2.val.det ^ a) * hint (intMat a b w) (fun X =>
        GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) F (blk h w m⁻¹ (Multiplicative.toAdd X))))
  rw [h1, hJ', hc, hinv, map_mul, map_mul, map_inv₀, map_pow, conj_absHalf, conj_absHalf]
  have hA := GlobalTheory.LeviDesc.absHalf_ne_zero' w (m.1.val.det ^ b / m.2.val.det ^ a)
  rw [eq_inv_of_mul_eq_one_left (absHalf_inv_mul w hD0)]
  field_simp

theorem mu_conj {K : Type} [Group K] (μ : K →* ℂˣ) (hμ : ∀ u, ‖((μ u : ℂˣ) : ℂ)‖ = 1) (x : K) :
    ((μ x⁻¹ : ℂˣ) : ℂ) = starRingEnd ℂ ((μ x : ℂˣ) : ℂ) := by
  rw [map_inv, Units.val_inv_eq_inv_val]
  exact Complex.inv_eq_conj (hμ x)

theorem ctStar : PositivityTheory.Rg.BcB.F.MLM.CtStar := by
  intro E _ _ _ n a ha w hw μ hμ f hf
  have hU : UL n w = ⊤ := if_pos hw
  funext m
  have hH := GlobalTheory.CompanionTheory.CtMulSplit.isHk_of_isHecke hU hf
  have hF : ∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' (fun y => f (toSub (UL n w) y)) :=
    ⟨GlobalTheory.LFun.KGL w n, (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, hH.2.2.1, fun k hk x =>
      ⟨by simpa using hH.2.2.2 k hk 1 (Subgroup.one_mem _) x, by simpa using hH.2.2.2 1 (Subgroup.one_mem _) k hk x⟩⟩
  have hstar : (fun y => PositivityTheory.Rg.BcB.F.Eig.lstar f (toSub (UL n w) y)) =
      fun y => starRingEnd ℂ (f (toSub (UL n w) y⁻¹)) := by
    funext y
    show starRingEnd ℂ (f (toSub (UL n w) y)⁻¹) = _
    have e : (toSub (UL n w) y)⁻¹ = toSub (UL n w) y⁻¹ :=
      Subtype.ext (by rw [Subgroup.coe_inv, GlobalTheory.CompanionTheory.CtMulSplit.val_toSub hU, GlobalTheory.CompanionTheory.CtMulSplit.val_toSub hU])
    rw [e]
  show ((μ _ : ℂˣ) : ℂ) * ct _ w (fun y => PositivityTheory.Rg.BcB.F.Eig.lstar f (toSub (UL n w) y)) m =
    starRingEnd ℂ (((μ _ : ℂˣ) : ℂ) * ct _ w (fun y => f (toSub (UL n w) y)) m⁻¹)
  rw [hstar, ct_adj _ w (fun y => f (toSub (UL n w) y)) hF m, map_mul (starRingEnd ℂ)]
  congr 1
  rw [← mu_conj μ hμ]
  congr 2
  have hs : (((-1 : (w.adicCompletion E)ˣ) ^ (a * (n - a)))⁻¹) = (-1) ^ (a * (n - a)) := by
    rw [← inv_pow]
    simp
  simp only [Prod.fst_inv, Prod.snd_inv, map_inv, inv_pow, mul_inv, inv_inv, hs]

end GlobalTheory.CompanionTheory.CtAdj
