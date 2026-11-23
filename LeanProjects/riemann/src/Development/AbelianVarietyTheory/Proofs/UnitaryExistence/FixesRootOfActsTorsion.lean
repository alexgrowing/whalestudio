import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.FieldFixesCurve
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmEndomorphismCommConjugation
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmEllipticCurveIntegersWithPeriod
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmActionPolarisedCurveAdjointConj
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat GlobalTheory.IndefiniteRowSideFullHecke
open scoped CategoryTheory.Obj

namespace GlobalTheory.CurveConjCompare

open CurveEndo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem multiplier_pull (P : Out.PolAV (Sp ℂ)) (hg : P.g = 1) (u : HolUnif P.A P.L P.g)
    (W W' : P.A ⟶ P.A) [IsMonHom W] (hW' : IsMonHom W') (α : ℂ) (hW : ∀ z, u.ex (α • z) = u.ex z ≫ W)
    (τ : ℂ ≃+* ℂ) (io : P.A.left ⟶ P.A.left) (h : IsGrpPullback P.A P.A (spMap (τ : ℂ →+* ℂ)) io)
    (e : W'.left ≫ io = io ≫ W.left) (z : Fin P.g → ℂ) : u.ex (τ α • z) = u.ex z ≫ W' := by
  obtain ⟨hd, he, -⟩ := AnyUnif.tangent_and_unimodular thetaUnifAV_all P u
  obtain ⟨v, ⟨hv, dv⟩, -⟩ := he (fun _ => 1)
  obtain ⟨v', hv', -⟩ := existsUnique_isVecOver h.1 v
  have tv' := hv'.isTangent h hv
  unfold IsVecOver at hv'
  obtain ⟨w', dw', -⟩ := hd v' tv'
  have h1 : (v ≫ W).left = spMap (epsScaleR α) ≫ v.left :=
    left_eq_scale u he α hv dv (HomLinear.isTangent_comp W hv)
      (HomLinear.isDiff_comp u u W (α • LinearMap.id) hW hv dv)
  have h2 : (v' ≫ W').left = spMap (epsScaleR (τ α)) ≫ v'.left := by
    refine h.1.hom_ext ?_ ?_
    · rw [Over.comp_left, Category.assoc, e, ← Category.assoc, hv', Category.assoc, ← Over.comp_left, h1,
        ← Category.assoc, scale_dual, Category.assoc, Category.assoc, hv']
      rfl
    · rw [Over.w, Category.assoc, Over.w]
      refine Eq.trans ?_ (spMap_comp_spMap _ _).symm
      show spMap _ = spMap _
      congr 1
      ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have hne : w' ≠ 0 := by
    rintro rfl
    have h3 := left_eq_scale u he 0 tv' dw' tv' (by rwa [zero_smul])
    have h4 : v.left = spMap (epsScaleR 0) ≫ v.left := by
      have h5 : spMap (Chart.dualMapR (τ : ℂ →+* ℂ)) ≫ v.left =
          spMap (Chart.dualMapR (τ : ℂ →+* ℂ)) ≫ spMap (epsScaleR 0) ≫ v.left := by
        rw [← Category.assoc, scale_dual, map_zero, Category.assoc, ← hv', ← Category.assoc, ← h3]
      have h6 := congrArg (spMap (Chart.dualMapR (τ.symm : ℂ →+* ℂ)) ≫ ·) h5
      simpa only [← Category.assoc, dual_symm_dual, Category.id_comp] using h6
    have h7 := (hd v hv).unique dv
      (CMNormIdentity.isDiff_of_isLieComb u dv 0 ((LieMultiple.isLieComb_one_iff 0 v v).2 h4))
    simpa using congrFun h7 ⟨0, by omega⟩
  obtain ⟨F, hF, -, hT, -⟩ := HomLinear.exists_linear_of_isMonHom P.A P.A P.isAb P.isAb P.L P.L _ _ u u hd he W' hW'
  obtain ⟨tf, df⟩ := hT w' v' tv' dw'
  have h8 : F w' = τ α • w' := (hd _ tf).unique df
    (CMNormIdentity.isDiff_of_isLieComb u dw' _ ((LieMultiple.isLieComb_one_iff _ v' _).2 h2))
  obtain ⟨c, hc⟩ := CurveAdjoint.exists_scalar hg F
  rw [← hF, hc, smul_left_injective ℂ hne ((hc w').symm.trans h8)]

theorem ex_smul_iff (C : Curve H) (W : C.P.A ⟶ C.P.A) (α : ℂ) :
    (∀ z, C.u.ex (α • z) = C.u.ex z ≫ W) ↔ ∀ z, C.pt z ≫ W.left = C.pt (α * z) := by
  have e : ∀ z : ℂ, (α • fun _ => C.c * z : Fin C.P.g → ℂ) = fun _ => C.c * (α * z) := fun z => funext fun _ => by
    rw [Pi.smul_apply, smul_eq_mul]; ring
  constructor
  · intro h z
    unfold Curve.pt
    rw [← Over.comp_left, ← h, e]
  · intro h z
    have hg := C.g_eq
    have hz : z = fun _ => C.c * (z ⟨0, by omega⟩ / C.c) := funext fun j => by
      rw [mul_div_cancel₀ _ C.c_ne]
      congr 1
      exact Fin.ext (by have := j.2; simp only; omega)
    rw [hz, e]
    exact Over.OverMorphism.ext (h _).symm

theorem fixes_root_of_pullback (C : Curve H) {W W' : C.P.A ⟶ C.P.A} [IsMonHom W] (hW' : IsMonHom W')
    (hW : ∀ z, C.pt z ≫ W.left = C.pt (wC H (0, 1) * z)) {τ : ℂ ≃+* ℂ} {io : C.P.A.left ⟶ C.P.A.left}
    (h : IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io) (e : W'.left ≫ io = io ≫ W.left) {n : ℕ} (hn : 2 ≤ n)
    (hp : C.pt (1 / n) ≫ W'.left = C.pt (1 / n) ≫ W.left) : τ H.rt0 = H.rt0 := by
  have k := (ex_smul_iff C W' _).1
    (multiplier_pull C.P C.g_eq C.u W W' hW' _ ((ex_smul_iff C W _).2 hW) τ io h e)
  rw [k, hW] at hp
  obtain ⟨a, ha⟩ := (CompRatModel.pt_eq_iff C _ _).1 hp
  have hs : (τ H.rt0) ^ 2 = H.rt0 ^ 2 := by rw [← map_pow, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  refine (sq_eq_sq_iff_eq_or_eq_neg.1 hs).resolve_right fun hm => ?_
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hα : wC H (0, 1) = (1 + H.rt0) / 2 := by simp [wC]
  rw [hα, map_div₀, map_add, hm, map_one, map_ofNat] at ha
  have : wC H (1, -2) = wC H (n * a.1, n * a.2) := by
    simp only [wC] at ha ⊢
    push_cast
    field_simp at ha ⊢
    linear_combination ha
  have h1 : (1 : ℤ) = n * a.1 := congrArg Prod.fst (CompRatModel.wC_injective H this)
  have := Int.eq_one_of_mul_eq_one_right (by omega) h1.symm
  omega

theorem fixes_root_of_acts_torsion {C : Curve H} {τ : ℂ ≃+* ℂ} {io : C.P.A.left ⟶ C.P.A.left} {n : ℕ} (hn : 2 ≤ n)
    (h : C.ActsBy τ io n (1, 0)) : τ H.rt0 = H.rt0 := by
  obtain ⟨W, hW, hp, -⟩ := exists_endo_comm E H C
  obtain ⟨W', hW', e⟩ := HomDescent.exists_isMonHom_pull h.1 h.1 W
  refine fixes_root_of_pullback C hW' hp h.1 e hn ?_
  have : IsIso (spMap (τ : ℂ →+* ℂ)) := inferInstanceAs (IsIso (Spec.map τ.toCommRingCatIso.hom))
  have : IsIso io := h.1.1.isIso_fst_of_isIso
  have e1 : wC H (1, 0) = 1 := by simp [wC]
  have h1 := h.2 (1, 0)
  have h2 := h.2 (0, 1)
  rw [e1, _root_.one_mul] at h1
  rw [e1, _root_.one_mul] at h2
  rw [← cancel_mono io, Category.assoc, e, ← Category.assoc, h1, Category.assoc, hp, mul_one_div, h2]

end GlobalTheory.CurveConjCompare
