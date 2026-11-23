import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingSmul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieCombOneIffComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CurveEndo

theorem scale_dual (f : ℂ →+* ℂ) (c : ℂ) :
    spMap (Chart.dualMapR f) ≫ spMap (epsScaleR c) = spMap (epsScaleR (f c)) ≫ spMap (Chart.dualMapR f) := by
  rw [spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  ext a <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_symm_dual (τ : ℂ ≃+* ℂ) :
    spMap (Chart.dualMapR (τ.symm : ℂ →+* ℂ)) ≫ spMap (Chart.dualMapR (τ : ℂ →+* ℂ)) = 𝟙 _ := by
  rw [spMap_comp_spMap]
  refine Eq.trans ?_ (Spec.map_id (CommRingCat.of (DualNumber ℂ)))
  congr 1
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem left_eq_scale {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (he : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) {w : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (α : ℂ) (hv : IsTangent v)
    (hw : u.IsDiff w v) (hv' : IsTangent v') (hw' : u.IsDiff (α • w) v') :
    v'.left = spMap (epsScaleR α) ≫ v.left := by
  have hx := (LieMultiple.isLieComb_one_iff_comp α v _).2 rfl
  have hxt : IsTangent (Chart.spMap (Chart.scaleD α) ≫ v) :=
    (Chart.isTan_iff _).1 (Chart.isTan_scale α ((Chart.isTan_iff _).2 hv))
  rw [(he (α • w)).unique ⟨hv', hw'⟩ ⟨hxt, CMNormIdentity.isDiff_of_isLieComb u hw α hx⟩]
  exact (LieMultiple.isLieComb_one_iff α v _).1 hx

theorem comm_of_fixed (P : Out.PolAV (Sp ℂ)) (hg : P.g = 1) (u : HolUnif P.A P.L P.g)
    (hd : ∀ v, IsTangent v → ∃! w, u.IsDiff w v) (he : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)
    (W : P.A ⟶ P.A) [IsMonHom W] (α : ℂ) (hW : ∀ z, u.ex (α • z) = u.ex z ≫ W)
    (τ : ℂ ≃+* ℂ) (hτ : τ α = α) (io : P.A.left ⟶ P.A.left) (h : IsGrpPullback P.A P.A (spMap (τ : ℂ →+* ℂ)) io) :
    W.left ≫ io = io ≫ W.left := by
  obtain ⟨W', hW', e⟩ := HomDescent.exists_isMonHom_pull h h W
  obtain ⟨v, ⟨hv, dv⟩, -⟩ := he (fun _ => 1)
  obtain ⟨v', hv', -⟩ := existsUnique_isVecOver h.1 v
  have tv' := hv'.isTangent h hv
  unfold IsVecOver at hv'
  obtain ⟨w', dw', -⟩ := hd v' tv'
  have h1 : (v ≫ W).left = spMap (epsScaleR α) ≫ v.left :=
    left_eq_scale u he α hv dv (HomLinear.isTangent_comp W hv)
      (HomLinear.isDiff_comp u u W (α • LinearMap.id) hW hv dv)
  have h2 : (v' ≫ W').left = spMap (epsScaleR α) ≫ v'.left := by
    refine h.1.hom_ext ?_ ?_
    · rw [Over.comp_left, Category.assoc, e, ← Category.assoc, hv', Category.assoc, ← Over.comp_left, h1,
        ← Category.assoc, scale_dual, Category.assoc, Category.assoc, hv']
      simp [hτ]
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
  obtain ⟨F, hF, -, hT, hu⟩ := HomLinear.exists_linear_of_isMonHom P.A P.A P.isAb P.isAb P.L P.L _ _ u u hd he W' hW'
  obtain ⟨tf, df⟩ := hT w' v' tv' dw'
  have h8 : F w' = α • w' := (hd _ tf).unique df
    (CMNormIdentity.isDiff_of_isLieComb u dw' α ((LieMultiple.isLieComb_one_iff α v' _).2 h2))
  have h9 : ∀ z, F z = α • z := fun z => by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hz : z = (z i / w' i) • w' := by
      funext j
      have : j = i := Fin.ext (by have := j.2; have := i.2; omega)
      rw [this, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hi]
    rw [hz, map_smul, h8, smul_comm]
  rw [← e, ← hu W fun z => by rw [h9, hW]]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem cmHost_rootComplex_eq_pm_sqrt (H : Host E) : H.rt0 = Complex.I * Real.sqrt H.d ∨ H.rt0 = -(Complex.I * Real.sqrt H.d) := by
  rw [← sq_eq_sq_iff_eq_or_eq_neg, H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
    Real.sq_sqrt (by positivity)]
  simp

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h <;> rw [h] <;> simp

theorem mem_lattice (C : Curve H) (z : Fin C.P.g → ℂ) : z ∈ C.u.Λ ↔ ∃ a, z = fun _ => C.c * wC H a := by
  rw [C.lat z]
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h
  · exact ⟨fun ⟨m, n, e⟩ => ⟨(m, n), by rw [e, wC, h]⟩, fun ⟨a, e⟩ => ⟨a.1, a.2, by rw [e, wC, h]⟩⟩
  · refine ⟨fun ⟨m, n, e⟩ => ⟨(m + n, -n), ?_⟩, fun ⟨a, e⟩ => ⟨a.1 + a.2, -a.2, ?_⟩⟩
    · rw [e, wC, h]
      funext _
      push_cast
      ring
    · rw [e, wC, h]
      funext _
      push_cast
      ring

theorem exists_norm (H : Host E) : ∃ n : ℕ, (1 + H.d : ℂ) = 4 * n := by
  have := H.d_mod
  refine ⟨(1 + H.d) / 4, ?_⟩
  exact_mod_cast (by omega : 1 + H.d = 4 * ((1 + H.d) / 4))

theorem exists_endo_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∃ W : C.P.A ⟶ C.P.A, IsMonHom W ∧ (∀ z, C.pt z ≫ W.left = C.pt (wC H (0, 1) * z)) ∧ (∀ z z', C.pt z = C.pt z' ↔ ∃ a, z - z' = wC H a) ∧ (∀ x : Sp ℂ ⟶ C.P.A.left, x ≫ C.P.A.hom = 𝟙 _ → ∃ z, C.pt z = x) ∧ ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ io : C.P.A.left ⟶ C.P.A.left, IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → W.left ≫ io = io ≫ W.left := by
  intro E _ _ _ H C
  obtain ⟨Hm, χ, Ef, hA, hd, he, hθ, -⟩ := C.theta
  obtain ⟨n, hn⟩ := exists_norm H
  have hsq := H.sqrt_neg_disc_sq
  have hα : wC H (0, 1) = (1 + H.rt0) / 2 := by simp [wC]
  obtain ⟨W, hW, hF⟩ := exists_hom_of_linear_scaling_hermForm C.P C.P C.u C.u Hm χ Hm χ hA hA
    (fun k => (hθ k).2) (fun k => (hθ k).1) (wC H (0, 1) • LinearMap.id) n
    (fun l hl => by
      obtain ⟨a, rfl⟩ := (mem_lattice C l).1 hl
      refine (mem_lattice C _).2 ⟨(-(n * a.2), a.1 + a.2), ?_⟩
      funext _
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, wC]
      push_cast
      linear_combination (C.c * a.2 / 4) * hsq - (C.c * a.2 / 4) * hn)
    (fun x y => by
      have e : wC H (0, 1) * starRingEnd ℂ (wC H (0, 1)) = n := by
        rw [hα, map_div₀, map_add, rt0_conj_neg_ne_zero, map_one, map_ofNat]
        linear_combination (-1 / 4 : ℂ) * hsq + (1 / 4 : ℂ) * hn
      simp only [LinearMap.smul_apply, LinearMap.id_apply, hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      rw [← e, ← _root_.mul_assoc, _root_.mul_comm (wC H (0, 1))]
      rfl)
  refine ⟨W, hW, fun z => ?_, fun z z' => ?_, fun x hx => ?_, fun τ hτ io h => ?_⟩
  · unfold Curve.pt
    rw [← Over.comp_left, ← hF]
    congr 2
    funext _
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have e := C.u.ex_add (fun _ => C.c * (z - z')) (fun _ => C.c * z')
    have e' : ((fun _ => C.c * (z - z')) + fun _ => C.c * z' : Fin C.P.g → ℂ) = fun _ => C.c * z := by
      funext _
      simp only [Pi.add_apply]
      ring
    rw [e'] at e
    have e₁ : C.pt z = C.pt z' ↔ C.u.ex (fun _ => C.c * z) = C.u.ex (fun _ => C.c * z') :=
      ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (fun t => t.left) h⟩
    rw [e₁, e, mul_eq_right, C.u.ker, mem_lattice]
    refine exists_congr fun a => ⟨fun h => ?_, fun h => by rw [h]⟩
    exact mul_left_cancel₀ C.c_ne (congrFun h ⟨0, by rw [C.g_eq]; omega⟩)
  · obtain ⟨z, hz⟩ := C.u.ex_onto (Over.homMk x hx)
    have hg := C.g_eq
    refine ⟨z ⟨0, by omega⟩ / C.c, ?_⟩
    have : (fun _ => C.c * (z ⟨0, by omega⟩ / C.c)) = z := by
      funext j
      rw [mul_div_cancel₀ _ C.c_ne]
      congr 1
      exact Fin.ext (by have := j.2; simp only; omega)
    unfold Curve.pt
    rw [this, hz]
    rfl
  · refine comm_of_fixed C.P C.g_eq C.u hd he W (wC H (0, 1)) hF τ ?_ io h
    rw [hα, map_div₀, map_add, hτ, map_one, map_ofNat]

end GlobalTheory.CurveEndo
