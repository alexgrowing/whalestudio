import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTwConjMemCentMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellMulSimpleUIntegral
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.InertUniq

section Fixed
variable {L : Type} [Field L]

abbrev fixF (σ : L →+* L) : Subfield L := σ.eqLocusField (RingHom.id L)

abbrev starOfInv (σ : L →+* L) (h : ∀ x, σ (σ x) = x) : StarRing L where
  star := σ
  star_involutive := h
  star_mul x y := by rw [map_mul]; exact mul_comm _ _
  star_add := map_add σ

theorem finrank_fixF (σ : L →+* L) (h : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) :
    Module.finrank (fixF σ) L = 2 := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hd : x₀ - σ x₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hx₀)
  have hli : LinearIndependent (fixF σ) ![(1 : L), x₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hs : σ (s : L) = s := s.2
    have ht : σ (t : L) = t := t.2
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    change (s : L) + (t : L) * x₀ = 0 at hst
    have h2 : (s : L) + (t : L) * σ x₀ = 0 := by
      have := congrArg σ hst
      rwa [map_add, map_mul, hs, ht, map_zero] at this
    have ht0 : (t : L) = 0 := by
      have : (t : L) * (x₀ - σ x₀) = 0 := by linear_combination hst - h2
      exact (mul_eq_zero.1 this).resolve_right hd
    refine ⟨Subtype.ext ?_, Subtype.ext ht0⟩
    simpa [ht0] using hst
  have hsp : ⊤ ≤ Submodule.span (fixF σ) (Set.range ![(1 : L), x₀]) := by
    intro y _
    set b := (y - σ y) / (x₀ - σ x₀) with hbdef
    have hb : σ b = b := by
      rw [hbdef, map_div₀, map_sub, map_sub, h, h, ← neg_sub y (σ y), ← neg_sub x₀ (σ x₀), neg_div_neg_eq]
    set a := y - b * x₀ with hadef
    have hbm : b * (x₀ - σ x₀) = y - σ y := div_mul_cancel₀ _ hd
    have ha : σ a = a := by
      rw [hadef, map_sub, map_mul, hb]
      linear_combination hbm
    have hy : y = (⟨a, ha⟩ : fixF σ) • (1 : L) + (⟨b, hb⟩ : fixF σ) • x₀ := by
      rw [Algebra.smul_def, Algebra.smul_def]
      change y = a * 1 + b * x₀
      rw [hadef]; ring
    rw [hy]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)]
  simp

end Fixed

theorem eq_twCent_mul_KGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
    ∀ y g : GLw n w, y ∈ GlobalTheory.LFun.KGL w n →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w y).val.charpoly + v * derivative (nrmL n w y).val.charpoly = 1) →
    g⁻¹ * y * thL n w g ∈ GlobalTheory.LFun.KGL w n → ∃ t ∈ twCent (thL n w) y, ∃ k ∈ GlobalTheory.LFun.KGL w n, g = t * k := by
  intro E _ _ _ hU n w hs y g hy hbez hyg
  obtain ⟨hc, hinv, hval, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨-, ⟨ϖ, q, hϖ, -⟩, -⟩ := hns hs
  obtain ⟨-, -, hϖf, hϖv, ⟨x₀, -, hx₀⟩, -⟩ := hϖ
  letI : NontriviallyNormedField (w.adicCompletion E) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  letI : StarRing (w.adicCompletion E) := starOfInv (cj w) hinv
  have hle1 : ∀ x : w.adicCompletion E, ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 := fun x => Valued.toNormedField.norm_le_one_iff
  have hneq : ∀ x y : w.adicCompletion E, Valued.v x = Valued.v y → ‖x‖ = ‖y‖ := fun x y h =>
    le_antisymm (Valued.toNormedField.norm_le_iff.2 h.le) (Valued.toNormedField.norm_le_iff.2 h.ge)
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖv; exact WithZero.zero_ne_coe hϖv
  have hϖi : cj w ϖ⁻¹ = ϖ⁻¹ := by rw [map_inv₀, hϖf]
  have hϖn : 1 < ‖ϖ⁻¹‖ := by
    rw [Valued.toNormedField.one_lt_norm_iff, map_inv₀, hϖv]
    exact one_lt_inv₀ (by simp) |>.2 (by rw [← WithZero.coe_one, WithZero.coe_lt_coe]; decide)
  letI nF : NontriviallyNormedField (fixF (cj w)) :=
    { (inferInstance : NormedField (fixF (cj w))) with non_trivial := ⟨⟨ϖ⁻¹, hϖi⟩, hϖn⟩ }
  letI : NormedAlgebra (fixF (cj w)) (w.adicCompletion E) :=
    { (inferInstance : Algebra (fixF (cj w)) (w.adicCompletion E)) with
      norm_smul_le := fun r x => by rw [Algebra.smul_def, norm_mul]; exact le_of_eq rfl }
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  haveI hUn : GlobalTheory.JR.Unram (fixF (cj w)) (w.adicCompletion E) :=
    { charZero := ⟨fun a b h => Nat.cast_injective (R := w.adicCompletion E) (by simpa using congrArg (algebraMap (fixF (cj w)) (w.adicCompletion E)) h)⟩
      ultraF := inferInstance
      ultraE := inferInstance
      lcF := (isClosed_eq hc continuous_id).isClosedEmbedding_subtypeVal.locallyCompactSpace
      lcE := inferInstance
      finrank_eq := finrank_fixF (cj w) hinv ⟨x₀, fun h => by rw [h, sub_self, map_zero] at hx₀; exact zero_ne_one hx₀⟩
      star_fix := fun x => x.2
      star_ne := ⟨x₀, fun h => by change cj w x₀ = x₀ at h; rw [h, sub_self, map_zero] at hx₀; exact zero_ne_one hx₀⟩
      norm_star := fun x => hneq _ _ (hval x)
      unram := by
        intro x
        by_cases hx : x = 0
        · exact ⟨0, by rw [hx]; rfl⟩
        · have hv0 : Valued.v x ≠ 0 := by simpa using hx
          refine ⟨⟨ϖ ^ (-WithZero.log (Valued.v x)), by
            change cj w (ϖ ^ (-WithZero.log (Valued.v x))) = ϖ ^ (-WithZero.log (Valued.v x)); rw [map_zpow₀, hϖf]⟩, ?_⟩
          change ‖x‖ = ‖ϖ ^ (-WithZero.log (Valued.v x))‖
          apply hneq
          rw [map_zpow₀, hϖv, show ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) from rfl,
            ← WithZero.exp_zsmul, smul_eq_mul, neg_mul_neg, mul_one, WithZero.exp_log hv0] }
  have hcs : cj w = starRingEnd (w.adicCompletion E) := RingHom.ext fun _ => rfl
  have hth : ∀ h : GLw n w, (thL n w h).val = GlobalTheory.Tw.theta h.val := by
    intro h
    rw [thL, if_neg hs, hcs, thetaGL_val]
  have hnr : (nrmL n w y).val = GlobalTheory.Tw.nrm y.val := by
    rw [nrmL, if_neg hs, Units.val_mul, hcs, thetaGL_val]; rfl

  have hint : ∀ h : GLw n w, h ∈ GlobalTheory.LFun.KGL w n → (∀ i j, ‖h.val i j‖ ≤ 1) ∧ ‖h.val.det‖ = 1 := by
    intro h hh
    obtain ⟨h1, h2⟩ := (GlobalTheory.GKFactor.UnitaryInt.mem_GLint_iff_entries (Ov E w) h).1 hh
    have hdet : ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ i j, M i j ∈ Ov E w) → M.det ∈ Ov E w := by
      intro M hM
      let M₀ : Matrix (Fin n) (Fin n) (Ov E w) := fun i j => ⟨M i j, hM i j⟩
      have hM₀ : M = (Ov E w).subtype.mapMatrix M₀ := by ext i j; rfl
      rw [hM₀, ← RingHom.map_det]
      exact (M₀.det).2
    have d1 : ‖h.val.det‖ ≤ 1 := (hle1 _).2 (hdet _ h1)
    have d2 : ‖(h⁻¹).val.det‖ ≤ 1 := (hle1 _).2 (hdet _ h2)
    have hprod : ‖h.val.det‖ * ‖(h⁻¹).val.det‖ = 1 := by
      rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]
    refine ⟨fun i j => (hle1 _).2 (h1 i j), ?_⟩
    nlinarith [norm_nonneg h.val.det, norm_nonneg (h⁻¹).val.det]
  have hintR : ∀ h : GLw n w, (∀ i j, ‖h.val i j‖ ≤ 1) → ‖h.val.det‖ = 1 → h ∈ GlobalTheory.LFun.KGL w n := by
    intro h h1 h2
    refine (GlobalTheory.GKFactor.UnitaryInt.mem_GLint_iff_entries (Ov E w) h).2 ⟨fun i j => (hle1 _).1 (h1 i j), fun i j => ?_⟩
    rw [Matrix.coe_units_inv]
    exact (hle1 _).1 (GlobalTheory.TwIntegral.intg_inv h1 h2 i j)
  obtain ⟨hy1, hy2⟩ := hint y hy
  obtain ⟨hg1, hg2⟩ := hint _ hyg
  have htw : GlobalTheory.Tw.twConj g.val y.val = (g⁻¹ * y * thL n w g).val := by
    rw [Units.val_mul, Units.val_mul, hth, Matrix.coe_units_inv]; rfl
  obtain ⟨u, v, hu, hv, huv⟩ := hbez
  rw [hnr] at huv
  obtain ⟨t, ⟨htu, htc⟩, k, hk1, hk2, hx⟩ := GlobalTheory.TwIntegral.integral_twConj_mem_cent_mul (fixF (cj w)) (w.adicCompletion E) n
    y.val g.val hy1 hy2 ⟨u, v, fun i => (hle1 _).2 (hu i), fun i => (hle1 _).2 (hv i), huv⟩ g.isUnit
    (by rw [htw]; exact hg1) (by rw [htw]; exact hg2)
  have hku : IsUnit k := GlobalTheory.TwIntegral.isUnit_of_norm_det hk2
  refine ⟨htu.unit, ?_, hku.unit, hintR _ (by simpa using hk1) (by simpa using hk2), Units.ext ?_⟩
  · show htu.unit * y = y * thL n w htu.unit
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hth, IsUnit.unit_spec]
    exact htc
  · rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]
    exact hx

end GlobalTheory.InertUniq
