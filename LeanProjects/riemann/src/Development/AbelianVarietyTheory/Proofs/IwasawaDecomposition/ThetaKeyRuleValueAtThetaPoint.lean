import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TangentVectorExistsUniqueUniformisingVector
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRulePowComplex
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormOfParts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

section Unif

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.OrthoMetric GlobalTheory.ArchMetricCompare Formalism.L2.LamCM GlobalTheory.CM GlobalTheory.Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem exists_unif_of_frame {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) (i : Fin F.n)
    {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) {y : Sp ℂ ⟶ Xo.X} (hy : y = F.u i P)
    {s : LB.Sec (PPx y)} (Φ : FibKey Xo ℂ y) (ht : SecTie Φ.m Φ.th s)
    {θ : (Fin g → ℂ) → ℂ} {fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ}
    (c₁ : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (c₂ : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (c₃ : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex i P z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
      (Xo.univ.t.PP.L.g j j').val * fr j' z)
    (c₄ : ∀ j, ⊤ ≤ (F.ex i P 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' y ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
      (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (c₆ : ∀ j z (pt : Sp ℂ ⟶ Gx y), pt ≫ gxFst y = (F.ex i P z).left → pt ≫ gxSnd y = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z) :
    ∃ u : HolUnif Φ.key.P.A Φ.key.P.L g, u.Λ = P.range.toIntSubmodule ∧
      u.IsRig Φ.key.rig ∧ u.IsFn Φ.key.th θ ∧ ∀ z, (u.ex z).left ≫ Φ.m.φ = (F.ex i P z).left := by
  subst hy
  obtain ⟨w, ⟨hw, hrig⟩, hth⟩ := val_tie Φ.m ht
  obtain ⟨w', hw', hinv⟩ := ConjUnif.exists_inv w hw
  have hL := Φ.T.t.PP.isLB
  have hM := pull_isLB Xo.univ.t.PP.isLB Φ.m.φ
  have hol := isHolTo_exp F i hP
  let u₁ := fibreUnif Φ.m.cart (F.ex i P) P.range fr (F.ex_add i P hP) (F.ex_onto i P hP) (F.ex_ker i P hP)
    hP.2.2.1 hP.2.2.2.1 hol c₁ c₂ c₃
  have hex : ∀ z, (u₁.ex z).left ≫ Φ.m.φ = (F.ex i P z).left := fun z => liftPt_comp Φ.m.cart _
  have hle : ∀ z j, ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ (Xo.univ.t.PP.L.pull Φ.m.φ).U j →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (j PUnit.unit) := fun z j => (lift_le Φ.m.cart _ j).1
  have hfr : ∀ (j : Xo.univ.t.PP.L.ι) (k : Φ.T.t.PP.L.ι) (z : Fin g → ℂ),
      ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ ((Xo.univ.t.PP.L.pull Φ.m.φ).U (fun _ => j) ⊓ Φ.T.t.PP.L.U k) →
      valAt' (u₁.ex z).left ((Xo.univ.t.PP.L.pull Φ.m.φ).U (fun _ => j) ⊓ Φ.T.t.PP.L.U k)
        (w.s (fun _ => j, k)).val * (carry u₁ hM hL hw').fr k z = fr j z := by
    intro j k z hz
    obtain ⟨hj, hk⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [carry_fr u₁ hM hL hw' k (fun _ => j) z hk hj, hinv _ _ _ hz]
    exact mul_inv_cancel_left₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j, k))) _
  refine ⟨carry u₁ hM hL hw', rfl, ?_, ?_, hex⟩
  · intro k hk
    have h0 : (u₁.ex 0).left = eSec Φ.T.t.G := by
      rw [(u₁.ker 0).2 u₁.Λ.zero_mem, Hom.one_def]
      simp [eSec]
    obtain ⟨j, hj⟩ := exists_chart_at hM (u₁.ex 0).left
    have hk' : ⊤ ≤ (u₁.ex 0).left ⁻¹ᵁ Φ.T.t.PP.L.U (k PUnit.unit) := by
      rw [h0]
      exact fun p hp => mem_pull.1 (hk hp)
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hk'⟩
    have e := hfr (j PUnit.unit) (k PUnit.unit) 0 hz
    rw [c₄ _ (hle 0 j hj), h0] at e
    rw [h0] at hz
    have e' := val_rig Φ.m.cm.e_comm w Φ.T.t.PP.rig Xo.univ.t.PP.rig hrig (j PUnit.unit) (k PUnit.unit) hz
    rw [Φ.m.base] at e'
    exact mul_left_cancel₀ (valAt'_unit_ne_zero _ hz _) (e.trans e')
  · intro k z hk
    obtain ⟨j, hj⟩ := exists_chart_at hM (u₁.ex z).left
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hk⟩
    obtain ⟨pt, p₁, p₂, hpt⟩ := hth (u₁.ex z).left (Over.w _)
    have e := hfr (j PUnit.unit) k z hz
    refine mul_left_cancel₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j PUnit.unit, k))) ?_
    have e₁ := hpt (j PUnit.unit) k hz
    have e₂ := c₆ (j PUnit.unit) z pt (p₁.trans (hex z)) p₂ (hle z j hj)
    rw [← e] at e₂
    exact e₁.symm.trans (e₂.trans (mul_left_comm _ _ _))

end Unif

theorem mulVec_period {g : ℕ} {La : Type} [AddCommGroup La] (P : La →+ (Fin g → ℂ))
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (h τ : Matrix (Fin g) (Fin g) ℂ)
    (hn : ∀ i, h *ᵥ P (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1) (a : Fin g ⊕ Fin g → ℤ) :
    h *ᵥ P (bas a) = (fun i => (a (Sum.inl i) : ℂ)) + τ *ᵥ (fun i => (a (Sum.inr i) : ℂ)) := by
  have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
    intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
  have h2 : a = ∑ s, a s • (Pi.single s 1 : Fin g ⊕ Fin g → ℤ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [h1 (fun i => a (Sum.inl i)), h1 (fun i => a (Sum.inr i))]
  conv_lhs => rw [h2]
  simp only [map_sum, map_zsmul, Fintype.sum_sum_type, map_add, Matrix.mulVec_add, Matrix.mulVec_sum,
    Matrix.mulVec_smul, (hn _).1, (hn _).2]

theorem normalAt_of_coord (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) {La : Type} [AddCommGroup La]
    (P : La →+ (Fin x.P.g → ℂ)) (bas : (Fin x.P.g ⊕ Fin x.P.g → ℤ) ≃ₗ[ℤ] La)
    (h τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c₁ c₂ : Fin x.P.g → ℂ) (a : ℂ) (hu : IsUnit h.det)
    (hsymm : τ.IsSymm) (hpos : (τ.map Complex.im).PosDef)
    (hn : ∀ i, h *ᵥ P (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1)
    (hΛ : u.Λ = P.range.toIntSubmodule) (hR : u.IsRig x.rig)
    (hF : u.IsFn x.th fun z => a * thetaChar τ c₁ c₂ (h *ᵥ z)) (hD : ∀ i, u.IsDiff (Pi.single i 1) (x.v i)) :
    KeyPow.NormalAt x τ ((2 * Real.pi * Complex.I : ℂ) • hᵀ) c₁ c₂ a := by
  let φ : (Fin x.P.g → ℂ) ≃L[ℂ] (Fin x.P.g → ℂ) :=
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).symm.toContinuousLinearEquiv
  have hφ : ∀ z, h *ᵥ φ z = z := fun z =>
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).apply_symm_apply z
  have hφ' : ∀ z, φ (h *ᵥ z) = z := fun z =>
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).symm_apply_apply z
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  clear_value φ
  refine ⟨KeyNormalForm.change u φ (fun _ => 0) (differentiable_const _), hsymm, hpos, fun z => ?_,
    KeyNormalForm.isRig_change u φ _ _ rfl hR,
    KeyNormalForm.isFn_change u φ _ _ hF fun z => by simp only [hφ, Complex.exp_zero, mul_one],
    fun i => KeyNormalForm.isDiff_change u φ _ _ ?_⟩
  · rw [KeyNormalForm.mem_change, hΛ]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨m, rfl⟩ := bas.surjective v
      refine ⟨fun i => m (Sum.inl i), fun i => m (Sum.inr i), ?_⟩
      rw [← hφ z, ← hv]
      exact mulVec_period _ bas _ _ hn m
    · rintro ⟨m, n, rfl⟩
      refine ⟨bas (Sum.elim m n), ?_⟩
      rw [← hφ' (P _), mulVec_period _ bas _ _ hn]
      rfl
  · have e₁ : (2 * Real.pi * Complex.I : ℂ)⁻¹ • ((2 * Real.pi * Complex.I : ℂ) • hᵀ) i = h *ᵥ Pi.single i 1 := by
      funext j
      simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.mulVec_single_one,
        Matrix.col_apply]
      rw [inv_mul_cancel_left₀ hπ]
    rw [e₁, hφ']
    exact hD i

theorem value_at_thetaPt : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.ThetaOne κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (a : ℂ) (y : FrPt Xo c (CAt σ)) (Φ : FibKey Xo ℂ y.x), a ≠ 0 → IsThetaPt T b a y → Tied (S := ℂ) e y.s y.u Φ → a ^ 8 * (κ ℂ Φ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g * (T.h b).det) ^ 4 := by
  intro κ hH hT E _ _ _ H Dw l Xo c σ g e F r M k T b hb a y Φ ha ⟨hx, hder, hsec⟩ ⟨ht, hg, hv⟩
  subst hg
  have hP := T.isPer _ hb
  obtain ⟨hu, hsymm, hpos, hn⟩ := T.norm b hb
  have hj : Differentiable ℂ (fun z : Fin Φ.T.g → ℂ => (b, z)) := by fun_prop
  obtain ⟨u, hΛ, hR, hF, hex⟩ := exists_unif_of_frame F k hP hx Φ ht
    (θ := fun z => a * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z)) (fr := fun j z => T.fr j (b, z))
    (fun j => (T.fr_hol j).comp hj.differentiableOn fun z hz => ⟨hb, hz⟩)
    (fun j z hz => T.fr_ne j b z hb hz) (fun j j' z hz => T.fr_coc j j' b z hb hz)
    (fun j hj => (T.fr_rig j b hb hj).trans (congrArg (fun q => valAt' q _ _) hx.symm)) hsec
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hN := normalAt_of_coord Φ.key u _ T.bas (T.h b) (T.ta b) T.c₁ T.c₂ a hu hsymm hpos hn hΛ hR hF fun i => by
    obtain ⟨W, hW, -⟩ := (existsUnique_isDiff_and_linear Φ.key u).1 _ (Φ.basis.1 i)
    have d := OrthoMetric.isDerivAt0_comp u Φ.m.φ (e := fun z => (F.ex k (T.Pf (T.co b)) z).left) hex (Φ.basis.1 i) hW
    have d' := hder (e i).1 (e i).2
    rw [show e.symm ⟨(e i).1, (e i).2⟩ = i from e.symm_apply_apply i,
      ← show _ = y.u (e i).1 (e i).2 from hv i] at d'
    obtain ⟨t₁, -, t₃⟩ := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ F k _ hP
    have hWi : W = Pi.single i 1 := (t₃ _ (t₁ _ _ d)).unique d d'
    exact hWi ▸ hW
  have hdet : ((2 * Real.pi * Complex.I : ℂ) • (T.h b)ᵀ).det = (2 * Real.pi * Complex.I) ^ Φ.T.g * (T.h b).det := by
    rw [Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
  have key := KeyCl.value_of_normalAt hH hT Φ.key ⟨T.half₁, T.half₂⟩ ha
    (hdet.trans_ne (mul_ne_zero (pow_ne_zero _ hπ) hu.ne_zero)) hN
  rw [key, mul_div_cancel₀ _ (pow_ne_zero 8 ha)]
  exact congrArg (· ^ 4) hdet

end GlobalTheory.KeyFourth
