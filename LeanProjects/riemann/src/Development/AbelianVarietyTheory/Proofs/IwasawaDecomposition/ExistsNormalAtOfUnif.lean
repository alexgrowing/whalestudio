import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcClauseClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnfFamily
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcModelWitnessExtension
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInRuleEqDiscriminant
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormOfParts
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TangentVectorExistsUniqueUniformisingVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleValueAtThetaPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyAtIffExistsKeyAtVia
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcFibreUniformisationThetaMultipleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaCoefficientBoundedAlongHolomorphicArcStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieBasisExpCoordsDetBoundedAlongArcStatement
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

theorem sp_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := (Spec.map_comp _ _).symm

theorem mem_of_pow_mem' {F : Type} [Field F] (V : ValuationSubring F) {x : F} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ V) :
    x ∈ V := by
  rw [← ValuationSubring.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff hn).1 h

theorem exists_values' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (V : ValuationSubring c.F) :
    ∃ r z : V, ((V.subtype r : c.F) : ℂ) = H.rt0 ∧ ((V.subtype z : c.F) : ℂ) = zeta l.A := by
  let inc := (IntermediateField.inclusion c.le).toRingHom
  refine ⟨⟨inc (baseKA l).ρ, mem_of_pow_mem' V two_ne_zero ?_⟩,
    ⟨inc (baseKA l).ζ, mem_of_pow_mem' V l.A_pos.ne' ?_⟩, rfl, rfl⟩
  · rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
    exact neg_mem (natCast_mem V _)
  · rw [← map_pow, (baseKA l).ζ_prim.pow_eq_one, map_one]
    exact one_mem V

theorem ratio_bounds {K D n C₂ C₃ : ℝ} (hK : 0 < K) (hC₂ : 0 < C₂) (hC₃ : 0 < C₃) (hD₁ : C₃⁻¹ ≤ D) (hD₂ : D ≤ C₃)
    (hn₁ : C₂⁻¹ ≤ n) (hn₂ : n ≤ C₂) :
    ((K + K⁻¹) * C₃ * C₂ ^ 2)⁻¹ ≤ K * D / n ^ 2 ∧ K * D / n ^ 2 ≤ (K + K⁻¹) * C₃ * C₂ ^ 2 := by
  have hn : 0 < n := lt_of_lt_of_le (inv_pos.2 hC₂) hn₁
  have hD : 0 < D := lt_of_lt_of_le (inv_pos.2 hC₃) hD₁
  have hKi : 0 < K⁻¹ := inv_pos.2 hK
  have h1 : 1 ≤ C₂ * n := by
    have := mul_le_mul_of_nonneg_left hn₁ hC₂.le
    rwa [mul_inv_cancel₀ hC₂.ne'] at this
  have h2 : 1 ≤ C₃ * D := by
    have := mul_le_mul_of_nonneg_left hD₁ hC₃.le
    rwa [mul_inv_cancel₀ hC₃.ne'] at this
  have hKK : 1 ≤ K * (K + K⁻¹) := by
    rw [mul_add, mul_inv_cancel₀ hK.ne']; nlinarith
  constructor
  · rw [inv_le_comm₀ (by positivity) (by positivity), inv_div, div_le_iff₀ (by positivity)]
    have : n ^ 2 ≤ C₂ ^ 2 := pow_le_pow_left₀ hn.le hn₂ 2
    calc n ^ 2 ≤ C₂ ^ 2 * 1 := by simpa using this
      _ ≤ C₂ ^ 2 * ((K * (K + K⁻¹)) * (C₃ * D)) := by
          gcongr; nlinarith
      _ = (K + K⁻¹) * C₃ * C₂ ^ 2 * (K * D) := by ring
  · rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ (C₂ * n) ^ 2 := one_le_pow₀ h1
    calc K * D ≤ K * C₃ * 1 := by nlinarith
      _ ≤ (K + K⁻¹) * C₃ * (C₂ * n) ^ 2 := by
          gcongr
          · linarith
      _ = (K + K⁻¹) * C₃ * C₂ ^ 2 * n ^ 2 := by ring

end GlobalTheory.ArcNormal

open scoped Matrix
namespace GlobalTheory.ArcNormal

theorem exists_normalAt_of_unif {g : ℕ} (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) {La : Type}
    [AddCommGroup La] (P : La →+ (Fin g → ℂ)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La)
    (h τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (c₀ : ℂ) (hu : IsUnit h.det)
    (hsymm : τ.IsSymm) (hpos : (τ.map Complex.im).PosDef) (hc : KeyPow.charHalf g c₁ c₂)
    (hn : ∀ i, h *ᵥ P (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1)
    (hΛ : u.Λ = P.range.toIntSubmodule) (hR : u.IsRig x.rig)
    (hF : u.IsFn x.th fun z => c₀ * thetaChar τ c₁ c₂ (h *ᵥ z)) :
    ∃ (Wv : Fin x.P.g → Fin g → ℂ), (∀ i, u.IsDiff (Wv i) (x.v i)) ∧
      ∃ (τ' Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a' b' : Fin x.P.g → ℂ), KeyPow.charHalf _ a' b' ∧
        KeyPow.NormalAt x τ' Mx a' b' c₀ ∧
        ‖Mx.det‖ = (2 * Real.pi) ^ g * ‖h.det‖ * ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ := by
  subst hg
  choose Wv hW using fun i => ((GlobalTheory.LamT.existsUnique_isDiff_and_linear x u).1 _ (x.basis.1 i)).exists
  refine ⟨Wv, hW, ?_⟩
  let φ : (Fin x.P.g → ℂ) ≃L[ℂ] (Fin x.P.g → ℂ) :=
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).symm.toContinuousLinearEquiv
  have hφ : ∀ z, h *ᵥ φ z = z := fun z =>
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).apply_symm_apply z
  have hφ' : ∀ z, φ (h *ᵥ z) = z := fun z =>
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).symm_apply_apply z
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  clear_value φ
  let Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ := (2 * Real.pi * Complex.I : ℂ) • Matrix.of fun i => h *ᵥ Wv i
  refine ⟨τ, Mx, c₁, c₂, hc, ⟨KeyNormalForm.change u φ (fun _ => 0) (differentiable_const _), hsymm, hpos, fun z => ?_,
    KeyNormalForm.isRig_change u φ _ _ rfl hR,
    KeyNormalForm.isFn_change u φ _ _ hF fun z => by simp only [hφ, Complex.exp_zero, mul_one],
    fun i => KeyNormalForm.isDiff_change u φ _ _ ?_⟩, ?_⟩
  · rw [KeyNormalForm.mem_change, hΛ]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨m, rfl⟩ := bas.surjective v
      refine ⟨fun i => m (Sum.inl i), fun i => m (Sum.inr i), ?_⟩
      rw [← hφ z, ← hv]
      exact GlobalTheory.KeyFourth.mulVec_period _ bas _ _ hn m
    · rintro ⟨m, n, rfl⟩
      refine ⟨bas (Sum.elim m n), ?_⟩
      rw [← hφ' (P _), GlobalTheory.KeyFourth.mulVec_period _ bas _ _ hn]
      rfl
  · have e₁ : (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx i = h *ᵥ Wv i := by
      funext j
      simp only [Mx, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
      rw [inv_mul_cancel_left₀ hπ]
    rw [e₁, hφ']
    exact hW i
  · have e₂ : Mx = (2 * Real.pi * Complex.I : ℂ) • ((Matrix.of fun i j => Wv i j) * hᵀ) := by
      ext i j
      simp [Mx, Matrix.mulVec, Matrix.mul_apply, dotProduct, mul_comm]
    rw [e₂, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose, Fintype.card_fin, norm_mul, norm_mul, norm_pow]
    have : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [this]
    simp only [Fin.cast_eq_self]
    ring

end GlobalTheory.ArcNormal

namespace GlobalTheory.ArcNormal

open scoped Matrix

theorem main_of_lemmas (hFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo
    : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ
    (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a
    : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W
    : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp
    (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th
    : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M
    : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C
    (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries
    ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw
    w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ
    : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∃ (_
    : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (c₀
    : ℂ), u.IsRig x.rig ∧ GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u ∧ u.Λ = (Ha.Pw
    w).range.toIntSubmodule ∧ u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec
    z))) (hTheta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo
    : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ
    (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a
    : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W
    : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp
    (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th
    : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M
    : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C
    (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries
    ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw
    w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ
    : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (u
    : HolUnif x.P.A x.P.L g) (c₀
    : ℂ), u.IsRig x.rig → GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw
    w) x φ u → u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec
    z)) → C⁻¹ ≤ ‖c₀‖ ∧ ‖c₀‖ ≤ C) (hLie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo
    : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ
    (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a
    : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W
    : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp
    (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th
    : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M
    : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C
    (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries
    ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw
    w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ
    : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg
    : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv
    : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw
    w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → C⁻¹ ≤ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast
    hg.symm i) j).det‖ ∧ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ≤ C) : ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H
    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo
    : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (Y
    : Model Xo c V.subtype), 1 ≤ Dw.p + Dw.q → PushInvertible Y.t.G Y.t.PP.L → ∀ (a
    : ArcIn Dw l V.subtype ℂ (c.F.val.toRingHom.comp V.subtype)) (χ : Sp (PowerSeries
    ℂ) ⟶ Y.X), Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R :=
    ℂ)) PowerSeries.X χ → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (c.F.val.toRingHom.comp
    V.subtype) → (∀ x : Sp (PowerSeries
    ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ∀ M : GChart Y, ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ y : ℂ → (Sp
    ℂ ⟶ Y.X), (∀ (U : Y.X.Opens) (f : Γ(Y.X,
    U)), ⊤ ≤ χ ⁻¹ᵁ U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ⊤ ≤ y w ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (y
    w) U f)) ∧ ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ (hz : ⊤ ≤ y w ⁻¹ᵁ M.U) (x
    : KeyIn ℂ), KeyAt M (y w) hz x → ∃ (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a' b'
    : Fin x.P.g → ℂ) (c₀
    : ℂ), GlobalTheory.KeyPow.charHalf _ a' b' ∧ c₀ ≠ 0 ∧ GlobalTheory.KeyPow.NormalAt x τ Mx a' b' c₀ ∧ C⁻¹ ≤ ‖Mx.det‖ / ‖c₀‖ ^ 2 ∧ ‖Mx.det‖ / ‖c₀‖ ^ 2 ≤ C := by
  intro E _ _ _ H Dw l Xo c V Y hpq hP a χ hχ hover hgen M hM
  let _ : Algebra (FractionRing ℂ) ℂ := FractionRing.liftAlgebra ℂ ℂ
  have : IsScalarTower ℂ (FractionRing ℂ) ℂ := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  obtain ⟨h1, h2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨W⟩ := (Y.hasArcData_iff _ _ _ _ χ).1 hχ
  obtain ⟨U, hU, -⟩ := GlobalTheory.UnifFamily.exists_unf_family E H Dw l Xo c hpq
  have hσ : Formalism.L2.PjFree.GoodEmb c c.F.val.toRingHom := (Formalism.L2.PjFree.goodEmb_iff c.F.val.toRingHom).mpr rfl
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c _ _ (U _) (hU _ hσ).1
  have hty := (GlobalTheory.Relab.relab_good E H l c _ hσ).2.2.2 Dw Uw.g Uw.e
  obtain ⟨Ha⟩ := GlobalTheory.arcClause_closed E H Dw l Xo c _ _ Y _ a χ W Uw.g _ Uw.F hσ hty (exists_values' c V) hover hgen
  obtain ⟨-, -, th, hth⟩ := GlobalTheory.ThetaOverField.nonzero_generates h1 h2 ℂ a.D₀
    (⟨fun _ => 0, fun _ _ => by simp⟩ : a.D₀.P.L.Sec)
  obtain ⟨Θ⟩ := GlobalTheory.ArcTheta.nonempty_thetaDat h1 h2 E H Dw l Xo c _ _ _ Y a χ W _ _ Uw.F Ha hty th hth
  have hlift : ∀ w : ℂ, Ha.T < w.im → ∃ yF : Sp ℂ ⟶ Xo.XF c,
      yF ≫ pullback.fst _ _ = Uw.F.u Ha.i (Ha.Pw w) ∧ yF ≫ pullback.snd _ _ = spMap c.F.val.toRingHom := by
    intro w hw
    refine ⟨pullback.lift (Uw.F.u Ha.i (Ha.Pw w)) (spMap c.F.val.toRingHom) ?_, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
    rw [Uw.F.over_σ _ _ (Ha.period w hw)]
    exact (sp_comp' _ _).symm
  classical
  let y : ℂ → (Sp ℂ ⟶ Y.X) := fun w =>
    if h : ∃ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Uw.F.u Ha.i (Ha.Pw w) ∧
      yF ≫ pullback.snd _ _ = spMap c.F.val.toRingHom then h.choose ≫ Y.j
    else spMap (PowerSeries.constantCoeff (R := ℂ)) ≫ χ
  have hy : ∀ w : ℂ, Ha.T < w.im → ∃ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Uw.F.u Ha.i (Ha.Pw w) ∧
      yF ≫ pullback.snd _ _ = spMap c.F.val.toRingHom ∧ y w = yF ≫ Y.j := by
    intro w hw
    have h := hlift w hw
    exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, dif_pos h⟩
  refine ⟨y, fun U f hUf => ?_, ?_⟩
  · obtain ⟨T', hT'⟩ := Ha.point U f hUf
    refine ⟨max T' Ha.T, fun w hw => ?_⟩
    obtain ⟨yF, k₁, k₂, e⟩ := hy w ((le_max_right _ _).trans_lt hw)
    rw [e]
    exact hT' w ((le_max_left _ _).trans_lt hw) yF k₁ k₂
  · obtain ⟨T₁, hF⟩ := hFib E H Dw l Xo c _ V Y a χ W _ _ Uw.F Ha th Θ M hσ hty hP hover hgen hM
    obtain ⟨T₂, C₂, hC₂, hT⟩ := hTheta E H Dw l Xo c _ V Y a χ W _ _ Uw.F Ha th Θ M hσ hty hP hover hgen hM
    obtain ⟨T₃, C₃, hC₃, hL⟩ := hLie E H Dw l Xo c _ V Y a χ W _ _ Uw.F Ha th Θ M hσ hty hP hover hgen hM
    have hh : IsUnit Θ.h.det := by
      refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun i k => Ha.Pw 0 (Θ.bas (Pi.single (.inl k) 1)) i) ?_
      ext i k
      have e := congrFun (Θ.per 0 k).1 i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm] using e
    set K : ℝ := (2 * Real.pi) ^ Uw.g * ‖Θ.h.det‖ with hKdef
    have hK : 0 < K := mul_pos (pow_pos Real.two_pi_pos _) (norm_pos_iff.2 hh.ne_zero)
    refine ⟨max Ha.T (max T₁ (max T₂ T₃)), (K + K⁻¹) * C₃ * C₂ ^ 2, by positivity, fun w hw hz x hx => ?_⟩
    have hw₀ : Ha.T < w.im := (le_max_left _ _).trans_lt hw
    have hw₁ : T₁ < w.im := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hw
    have hw₂ : T₂ < w.im := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans_lt hw
    have hw₃ : T₃ < w.im := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans_lt hw
    obtain ⟨yF, k₁, k₂, e⟩ := hy w hw₀
    have hx' : ∃ hz' : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U, KeyAt M (yF ≫ Y.j) hz' x := by
      rw [← e]; exact ⟨hz, hx⟩
    obtain ⟨hz', φ, hφ⟩ := hx'
    obtain ⟨hg, u, c₀, hR, hA, hΛ, hFn⟩ := hF w hw₁ yF k₁ k₂ hz' x φ hφ
    obtain ⟨hc₁, hc₂⟩ := hT w hw₂ yF k₁ k₂ hz' x φ hφ u c₀ hR hA hFn
    obtain ⟨Wv, hW, τ', Mx, a', b', hab, hN, hdet⟩ := exists_normalAt_of_unif x hg u (Ha.Pw w) Θ.bas Θ.h (Θ.τ w)
      Θ.c₁ Θ.c₂ c₀ hh (Θ.pos w hw₀).1 (Θ.pos w hw₀).2 ⟨Θ.half₁, Θ.half₂⟩ (Θ.per w) hΛ hR hFn
    obtain ⟨hd₁, hd₂⟩ := hL w hw₃ yF k₁ k₂ hz' x φ hφ hg u Wv hA hW
    have hc₀ : c₀ ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hc₁
      exact absurd hc₁ (not_le.2 (inv_pos.2 hC₂))
    refine ⟨τ', Mx, a', b', c₀, hab, hc₀, hN, ?_⟩
    rw [hdet, ← hKdef]
    exact ratio_bounds hK hC₂ hC₃ hd₁ hd₂ hc₁ hc₂

end GlobalTheory.ArcNormal

namespace GlobalTheory.ArcNormal

theorem arc_normal_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype), 1 ≤ Dw.p + Dw.q → PushInvertible Y.t.G Y.t.PP.L → ∀ (a : ArcIn Dw l V.subtype ℂ (c.F.val.toRingHom.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X), Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (c.F.val.toRingHom.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ∀ M : GChart Y, ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ y : ℂ → (Sp ℂ ⟶ Y.X), (∀ (U : Y.X.Opens) (f : Γ(Y.X, U)), ⊤ ≤ χ ⁻¹ᵁ U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ⊤ ≤ y w ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (y w) U f)) ∧ ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ (hz : ⊤ ≤ y w ⁻¹ᵁ M.U) (x : KeyIn ℂ), KeyAt M (y w) hz x → ∃ (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a' b' : Fin x.P.g → ℂ) (c₀ : ℂ), GlobalTheory.KeyPow.charHalf _ a' b' ∧ c₀ ≠ 0 ∧ GlobalTheory.KeyPow.NormalAt x τ Mx a' b' c₀ ∧ C⁻¹ ≤ ‖Mx.det‖ / ‖c₀‖ ^ 2 ∧ ‖Mx.det‖ / ‖c₀‖ ^ 2 ≤ C :=
  main_of_lemmas GlobalTheory.T.exists_arc_fibre_uniformisation_theta_multiple GlobalTheory.T.thetaCoefficient_bounded_along_holomorphicArc GlobalTheory.T.lieBasis_expCoords_det_bounded_along_arc

end GlobalTheory.ArcNormal
