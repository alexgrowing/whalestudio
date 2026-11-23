import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceW0PowFourEven
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsChangeLevelIsometryLinearMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RatioSqEqDetJAut
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChangeOfNormalisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSecGeneratorFibre
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaSqTransformLevelEight

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.GeoLevel

theorem exists_entire_ratio {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (W : ι → Set V)
    (hW : ∀ i, IsOpen (W i)) (hcov : ∀ w, ∃ i, w ∈ W i) (f f' : ι → V → ℂ) (c : ι → ι → V → ℂ)
    (hd : ∀ i, DifferentiableOn ℂ (f i) (W i)) (hd' : ∀ i, DifferentiableOn ℂ (f' i) (W i))
    (hn : ∀ i, ∀ w ∈ W i, f i w ≠ 0) (hn' : ∀ i, ∀ w ∈ W i, f' i w ≠ 0)
    (hc : ∀ i j w, w ∈ W i → w ∈ W j → f i w = c i j w * f j w)
    (hc' : ∀ i j w, w ∈ W i → w ∈ W j → f' i w = c i j w * f' j w) :
    ∃ ρ : V → ℂ, Differentiable ℂ ρ ∧ (∀ w, ρ w ≠ 0) ∧ ∀ i, ∀ w ∈ W i, f' i w = ρ w * f i w := by
  choose J hJ using hcov
  have key : ∀ i, ∀ w ∈ W i, f' i w = f' (J w) w / f (J w) w * f i w := fun i w h => by
    have := hn _ _ (hJ w)
    rw [hc i (J w) w h (hJ w), hc' i (J w) w h (hJ w)]
    field_simp
  refine ⟨_, fun w => ?_, fun w => div_ne_zero (hn' _ _ (hJ w)) (hn _ _ (hJ w)), key⟩
  refine (((hd' (J w)).mul ((hd (J w)).inv (hn _))).congr fun w' h => ?_).differentiableAt ((hW _).mem_nhds (hJ w))
  exact (eq_div_of_mul_eq (hn _ _ h) (key _ _ h).symm).trans (div_eq_mul_inv _ _)

open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi in

theorem det_eq_sq_mul_of_theta_ratio (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La)
    (gam : D.La ≃ₗ[𝓞 E] D.La) (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (P P' : D.La →+ (Fin g → ℂ))
    (h h' τ τ' : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (ρ : (Fin g → ℂ) → ℂ) (κ : ℂ)
    (hbas : ∀ a b, D.EF (bas a) (bas b) = -omegaStd a b) (hiso : ∀ a b, D.EF (gam a) (gam b) = D.EF a b)
    (hN : ∀ u v, N u v = bas.symm (gam (bas (Pi.single v 1))) u) (hP : ∀ a, P' a = P (gam a))
    (hn : ∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1)
    (hn' : ∀ k, h' *ᵥ P' (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧
      h' *ᵥ P' (bas (Pi.single (Sum.inr k) 1)) = τ' *ᵥ Pi.single k 1)
    (hτ : τ ∈ SiegelH (Fin g)) (hτ' : τ' ∈ SiegelH (Fin g)) (hu : IsUnit h.det)
    (h8 : ∀ i j, (8 : ℤ) ∣ N (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ N (Sum.inr i) (Sum.inl j))
    (hdet : (4 : ℤ) ∣ N.toBlocks₁₁.det - 1)
    (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2)
    (hρd : Differentiable ℂ ρ) (hρ0 : ∀ z, ρ z ≠ 0) (hρ1 : ρ 0 = 1) (hκ : κ ≠ 0)
    (hrel : ∀ z, thetaChar τ' c₁ c₂ (h' *ᵥ z) * ρ z = κ * thetaChar τ c₁ c₂ (h *ᵥ z)) :
    h.det = κ ^ 2 * h'.det := by
  obtain ⟨ga, hga, hgae, hτe, hhe, hde⟩ := PeriodChange.period_change E H D g bas gam N
    P P' h h' τ τ' hbas hiso hN hP hn hn' hτ hτ' hu
  have h8ga : ∀ i j, (8 : ℤ) ∣ ga (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ ga (Sum.inr i) (Sum.inl j) :=
    fun i j => by
      rw [hgae]
      exact h8 j i
  have hχ : ((ZMod.χ₄ ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) = 1 := by
    have e : ga.toBlocks₂₂.det = N.toBlocks₁₁.det := by
      rw [hgae, Matrix.toBlocks_fromBlocks₂₂, Matrix.det_transpose]
    have e' : ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) = 1 := by
      have h4 : ((4 : ℕ) : ℤ) ∣ N.toBlocks₁₁.det - 1 := hdet
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 h4
      rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at this
      rw [e, this]
    rw [e', map_one, Int.cast_one]
  have hl := GlobalTheory.theta_sq_transform_level_eight g ga hga h8ga
  rw [hχ] at hl
  have dl : Differentiable ℂ (fun w : Fin g → ℂ => h⁻¹ *ᵥ w) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h⁻¹)).differentiable
  have hκ2 := ThetaRatio.ratio_sq_eq_det_jAut g ga hga h8ga hl c₁ c₂ h₁ h₂ τ hτ
    (fun w => ρ (h⁻¹ *ᵥ w)) κ (hρd.comp dl) (fun w => hρ0 _)
    (by simp only [Matrix.mulVec_zero, hρ1]) hκ (fun w => by
      have := hrel (h⁻¹ *ᵥ w)
      simp only [Matrix.mulVec_mulVec] at this
      rw [hhe, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hτe] at this
      exact this)
  rw [hde, hκ2]

set_option maxHeartbeats 1600000 in

theorem theta_move_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y z y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (A : Matrix (Fin r) (Fin r) E) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (t : Ix Dw → (CAt σ)ˣ), κ ≠ 0 → κ' ≠ 0 → IsThetaPt T b κ y → IsThetaPt T b' κ' z → (∀ a a', (F.Di k).EF (gam a) (gam a') = (F.Di k).EF a a') → (∀ a, (M.φ k (gam a) : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E)) → (A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → (∀ a, T.Pf (T.co b') (gam a) = T.Pf (T.co b) a) → (∀ w, (F.ex k (T.Pf (T.co b')) w).left = (F.ex k (T.Pf (T.co b)) w).left ≫ ν.φ) → FrMove ρ ν y y' → FrBor t z y' → Formalism.L2.PjFree.toC (t none : CAt σ) ^ 2 * (κ' ^ 2 * (T.h b).det) = κ ^ 2 * (T.h b').det := by
  intro E _ _ _ H Dw l Xo c σ g e F r M k T b hb b' hb' κ κ' y z y' gam A ρ ν t hκ hκ' hy hz hiso hA hdA hPP hex hmv hbor
  obtain ⟨O, ω, o1, o2, o3, o4, o5⟩ := GlobalTheory.MoveValues.frMove_values E H Dw l Xo c σ ρ ν _ _ hmv
  have hxρ : z.x = y.x ≫ ρ := hbor.1.symm.trans hmv.1
  obtain ⟨hxx, -, hbc⟩ := hbor
  clear hmv
  have hp := T.isPer _ hb
  have hp' := T.isPer _ hb'
  obtain ⟨hu, -, hv⟩ := hy
  obtain ⟨hu', -, hv'⟩ := hz
  obtain ⟨hdu, hsy, hpos, hn⟩ := T.norm b hb
  obtain ⟨hdu', hsy', hpos', hn'⟩ := T.norm b' hb'
  have hd : ∀ j, DifferentiableOn ℂ (fun w => T.fr j (b, w))
      {w | ⊤ ≤ (F.ex k (T.Pf (T.co b)) w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := fun j =>
    (T.fr_hol j).comp (f := fun w => (b, w)) (by fun_prop) (fun w h => ⟨hb, h⟩)
  have hd' : ∀ j, DifferentiableOn ℂ (fun w => T.fr j (b', w))
      {w | ⊤ ≤ (F.ex k (T.Pf (T.co b')) w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := fun j =>
    (T.fr_hol j).comp (f := fun w => (b', w)) (by fun_prop) (fun w h => ⟨hb', h⟩)
  have hne := fun j w => T.fr_ne j b w hb
  have hne' := fun j w => T.fr_ne j b' w hb'
  have hc := fun j j' w => T.fr_coc j j' b w hb
  have hc' := fun j j' w => T.fr_coc j j' b' w hb'
  have h0 := fun j => T.fr_rig j b hb
  have h0' := fun j => T.fr_rig j b' hb'
  generalize T.Pf (T.co b) = P at *
  generalize T.Pf (T.co b') = P' at *
  have hcov2 : ∀ w, ∃ q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι, ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O q.1 q.2 := fun w => by
    obtain ⟨j, hj⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (F.ex k P w).left
    obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB ((F.ex k P w).left ≫ ν.φ)
    exact ⟨(j', j), (o1 _ _ _).2 ⟨hj', hj⟩⟩
  have tr : ∀ j j' w, ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex k P' w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j j' w hw => by
    rw [hex]; exact ((o1 _ _ _).1 hw).1
  have tr2 : ∀ j j' w, ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j' := fun j j' w hw => ((o1 _ _ _).1 hw).2
  have hw0 : ∀ w, (F.ex k P w).left ≫ Xo.univ.t.G.hom = (y.x : Sp ℂ ⟶ Xo.X) := fun w =>
    (Over.w (F.ex k P w)).trans hu.symm
  have hw0' : ∀ w, (F.ex k P' w).left ≫ Xo.univ.t.G.hom = (z.x : Sp ℂ ⟶ Xo.X) := fun w =>
    (Over.w (F.ex k P' w)).trans hu'.symm
  have hz0 : (F.ex k P 0).left = (y.x : Sp ℂ ⟶ Xo.X) ≫ eSec Xo.univ.t.G := by
    rw [(F.ex_ker k P hp 0).2 (zero_mem _), hu]
    rfl
  obtain ⟨ρf, hρd, hρ0, hfr⟩ := exists_entire_ratio
    (fun q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι => {w | ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O q.1 q.2})
    (fun j => GlobalTheory.FamilyUnif_isOpen_ex F k P hp _) hcov2
    (fun q w => valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) * T.fr q.2 (b, w)) (fun q w => T.fr q.1 (b', w))
    (fun q q' w => valAt' ((F.ex k P w).left ≫ ν.φ) (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
      (Xo.univ.t.PP.L.g q.1 q'.1).val)
    (fun q => (((GlobalTheory.ClassUniq.isHolTo_ex F k P hp) (O q.1 q.2) (ω q.1 q.2)).2.mono
      fun w hw => ⟨Set.mem_univ _, hw⟩).mul ((hd q.2).mono fun w hw => tr2 _ _ w hw))
    (fun q => (hd' q.1).mono fun w hw => tr _ _ w hw)
    (fun q w hw => mul_ne_zero (o2 _ _ _ hw) (hne _ w (tr2 _ _ w hw)))
    (fun q w hw => hne' _ w (tr _ _ w hw))
    (fun q q' w h1 h2 => by
      rw [hc q.2 q'.2 w ((top_le_preimage_inf _ _ _).2 ⟨tr2 _ _ w h1, tr2 _ _ w h2⟩), ← mul_assoc,
        o3 _ _ _ _ _ h1 h2, mul_assoc])
    (fun q q' w h1 h2 => by
      have e2 := hc' q.1 q'.1 w ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ _ h1, tr _ _ _ h2⟩)
      rw [hex] at e2
      exact e2)
  have hρ1 : ρf 0 = 1 := by
    obtain ⟨q, hq⟩ := hcov2 0
    have e1 := hfr q 0 hq
    have e2 : T.fr q.1 (b', 0) = valAt' (F.ex k P 0).left (O q.1 q.2) (ω q.1 q.2) * T.fr q.2 (b, 0) := by
      rw [h0 _ (tr2 _ _ 0 hq), h0' _ (tr _ _ 0 hq), ← hu', hxρ]
      exact (o4 _ _ _ _ hz0 hq).trans (congrArg (fun x : Sp ℂ ⟶ Xo.X => _ * valAt' x _ _) hu)
    exact (mul_eq_right₀ (mul_ne_zero (o2 _ _ _ hq) (hne _ 0 (tr2 _ _ 0 hq)))).1 (e1.symm.trans e2)
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) z.x y'.x z.s y'.s := by
    obtain ⟨pm, p1, p2, p3⟩ := hbc
    exact ⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩
  have ht0 : Formalism.L2.PjFree.toC (t none : CAt σ) ≠ 0 := Units.ne_zero (M₀ := ℂ) (t none)
  generalize Formalism.L2.PjFree.toC (t none : CAt σ) = t₀ at *
  have hrel : ∀ w, thetaChar (T.ta b') T.c₁ T.c₂ (T.h b' *ᵥ w) * ρf w =
      κ / (t₀ * κ') * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w) := fun w => by
    obtain ⟨q, hq⟩ := hcov2 w
    let p : Over.mk (y.x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex k P w).left (hw0 w)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv q.2 w _ e1 e2 (tr2 _ _ w hq)
    have hval := GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc'
      (Over.homMk (F.ex k P' w).left (hw0' _)) q.1 _ _
      (fun pt h1 h2 => hv' q.1 w pt h1 h2 (tr _ _ w hq))
      (fun pt h1 h2 => o5 q.1 q.2 _ pt _ e1 e2 (h1.trans (hex w)) h2 hq)
    have hval2 : valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) *
        (κ * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w) * T.fr q.2 (b, w)) =
        t₀ * (κ' * thetaChar (T.ta b') T.c₁ T.c₂ (T.h b' *ᵥ w) * T.fr q.1 (b', w)) :=
      (congrArg (valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) * ·) v1).symm.trans hval
    have e3 : T.fr q.1 (b', w) = ρf w * (valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) * T.fr q.2 (b, w)) :=
      hfr q w hq
    rw [e3] at hval2
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero ht0 hκ')]
    apply mul_right_cancel₀ (mul_ne_zero (o2 _ _ _ hq) (hne _ w (tr2 _ _ w hq)))
    linear_combination -hval2
  have hAu : IsUnit A.det := by
    rcases hdA with h | ⟨⟨m, hm, h⟩, -⟩
    · rw [h]; exact isUnit_one
    · exact IsUnit.of_pow_eq_one h hm.ne'
  have hdA' : A⁻¹.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A⁻¹.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E) := by
    rw [Matrix.det_nonsing_inv]
    rcases hdA with h | ⟨⟨m, hm, h⟩, h4⟩
    · left; rw [h]; simp
    · right; exact ⟨⟨m, hm, by rw [Ring.inverse_eq_inv', inv_pow, h, inv_one]⟩, h4⟩
  have hiso' : ∀ a a', (F.Di k).EF (gam.symm a) (gam.symm a') = (F.Di k).EF a a' := fun a a' => by
    rw [← hiso, gam.apply_symm_apply, gam.apply_symm_apply]
  let N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
    Matrix.of fun u v => T.bas.symm (gam.symm (T.bas (Pi.single v 1))) u
  obtain ⟨h8, hdet⟩ := GlobalTheory.AdaptedDetSign.blocks_det_mod_four E H (F.Di k) g r T.bas gam.symm N
    ((M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap) A⁻¹ T.adapt
    (Subtype.val_injective.comp (M.φ k).injective)
    (by
      rw [← (M.X k).Λ_span]
      congr 1
      ext v
      exact ⟨fun ⟨a, ha⟩ => ha ▸ (M.φ k a).2, fun hv => ⟨(M.φ k).symm ⟨v, hv⟩,
        congrArg Subtype.val ((M.φ k).apply_symm_apply ⟨v, hv⟩)⟩⟩)
    (fun a => by
      have := hA (gam.symm a)
      rw [gam.apply_symm_apply] at this
      show (M.φ k (gam.symm a) : Fin r → E) = A⁻¹ *ᵥ (M.φ k a : Fin r → E)
      rw [this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec])
    hdA' (fun _ _ => rfl)
  have hκ2 := det_eq_sq_mul_of_theta_ratio E H (F.Di k) g T.bas gam.symm N P P' (T.h b) (T.h b') (T.ta b) (T.ta b')
    T.c₁ T.c₂ ρf _ T.sympl hiso' (fun _ _ => rfl) (fun a => by rw [← hPP, gam.apply_symm_apply]) hn hn'
    ⟨hsy, hpos⟩ ⟨hsy', hpos'⟩ hdu h8 hdet T.half₁ T.half₂ hρd hρ0 hρ1
    (div_ne_zero hκ (mul_ne_zero ht0 hκ')) hrel
  rw [hκ2]
  field_simp

end GlobalTheory.GeoLevel
