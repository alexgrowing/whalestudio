import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PeriodCoordinateThetaOfSignedHeisenbergVacuumStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdmissibleIndicatorFunctions
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeDatumOfSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmUnitPowFourIdempotentModEight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaSqTransformLevelEight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RatioSqEqDetJAut
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChangeOfNormalisation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealPlaceEmbeddings

namespace GlobalTheory.VacMult

section Analytic

open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem factor_ratio {α : Type} (F F' : α → ℂ) (k : ℕ) (A B : ℂ) (hA : A ≠ 0) (z₀ : α) (h₀ : F z₀ ≠ 0)
    (h : ∀ z : Fin (k + 1) → α, A * ∏ i, F (z i) = B * ∏ i, F' (z i)) :
    ∃ κ : ℂ, κ ≠ 0 ∧ (∀ w, F' w = κ * F w) ∧ A = B * κ ^ (k + 1) := by
  have h1 : ∀ w, A * (F w * F z₀ ^ k) = B * (F' w * F' z₀ ^ k) := fun w => by
    simpa [Fin.prod_univ_succ] using h (Fin.cons w fun _ => z₀)
  have h2 : B * (F' z₀ * F' z₀ ^ k) ≠ 0 := by
    rw [← h1]
    exact mul_ne_zero hA (mul_ne_zero h₀ (pow_ne_zero _ h₀))
  have hB : B ≠ 0 := left_ne_zero_of_mul h2
  have h₀' : F' z₀ ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul h2)
  refine ⟨F' z₀ / F z₀, div_ne_zero h₀' h₀, fun w => ?_, ?_⟩
  · rw [div_mul_eq_mul_div, eq_div_iff h₀]
    refine mul_left_cancel₀ (mul_ne_zero hB (pow_ne_zero k h₀')) ?_
    linear_combination F w * h1 z₀ - F z₀ * h1 w
  · rw [div_pow]
    field_simp
    linear_combination h1 z₀

theorem scalar_eq_one {g n : ℕ} (hn : Even n) (σ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hσ : σ ∈ Matrix.symplecticGroup (Fin g) ℤ)
    (h8 : ∀ i j, (8 : ℤ) ∣ σ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ σ (Sum.inr i) (Sum.inl j))
    (hdet : (8 : ℤ) ∣ σ.toBlocks₂₂.det - 1) (c₁ c₂ : Fin g → ℂ) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2)
    (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) (τ τ' h h' Q Q' : Matrix (Fin g) (Fin g) ℂ)
    (hτ : τ ∈ SiegelH (Fin g)) (hu : IsUnit h.det) (e₁ : τ' = spAct σ τ)
    (e₂ : h' = ((jAut σ τ)⁻¹)ᵀ * h) (e₃ : h.det = (jAut σ τ).det * h'.det) (C a : ℂ) (hC : C ≠ 0)
    (hz : ∀ z : Fin n → Fin g → ℂ,
      C * h.det ^ (n / 2) * ∏ k, (cexp (Real.pi / 2 * ((h *ᵥ z k) ⬝ᵥ Q *ᵥ (h *ᵥ z k))) *
        thetaChar τ c₁ c₂ (h *ᵥ z k)) =
      a * (C * h'.det ^ (n / 2) * ∏ k, (cexp (Real.pi / 2 * ((h' *ᵥ z k) ⬝ᵥ Q' *ᵥ (h' *ᵥ z k))) *
        thetaChar τ' c₁ c₂ (h' *ᵥ z k)))) : a = 1 := by
  rcases n with _ | k
  · simpa [hC] using (hz 0).symm
  have hχ : ((ZMod.χ₄ ((σ.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) = 1 := by
    have h4 : ((4 : ℕ) : ℤ) ∣ σ.toBlocks₂₂.det - 1 := Dvd.dvd.trans (by norm_num) hdet
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 h4
    rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at this
    rw [this, map_one, Int.cast_one]
  have hl := theta_sq_transform_level_eight g σ hσ h8
  rw [hχ] at hl
  obtain ⟨w₀, hw₀⟩ : ∃ w, thetaChar τ c₁ c₂ w ≠ 0 := by
    obtain ⟨m, rfl⟩ := ThetaRatio.exists_eq_halfVec h₁
    obtain ⟨m', rfl⟩ := ThetaRatio.exists_eq_halfVec h₂
    by_contra hc
    push_neg at hc
    refine theta_ne_zero hτ (halfVec m) (halfVec m') (funext fun w => ?_)
    have := hc w
    rw [ThetaRatio.thetaChar_ofRealVec] at this
    exact this
  have hi : ∀ w, h *ᵥ (h⁻¹ *ᵥ w) = w := fun w => by
    rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hi' : ∀ w, h' *ᵥ (h⁻¹ *ᵥ w) = zAct σ τ w := fun w => by
    rw [e₂, ← mulVec_mulVec, hi, zAct]
  obtain ⟨κ, hκ, hF, hA⟩ := factor_ratio
    (fun z => cexp (Real.pi / 2 * ((h *ᵥ z) ⬝ᵥ Q *ᵥ (h *ᵥ z))) * thetaChar τ c₁ c₂ (h *ᵥ z))
    (fun z => cexp (Real.pi / 2 * ((h' *ᵥ z) ⬝ᵥ Q' *ᵥ (h' *ᵥ z))) * thetaChar τ' c₁ c₂ (h' *ᵥ z))
    k (C * h.det ^ ((k + 1) / 2)) (a * (C * h'.det ^ ((k + 1) / 2)))
    (mul_ne_zero hC (pow_ne_zero _ hu.ne_zero)) (h⁻¹ *ᵥ w₀)
    (mul_ne_zero (Complex.exp_ne_zero _) (by rwa [hi])) (fun z => by rw [hz z, mul_assoc a])
  have hκ2 := ThetaRatio.ratio_sq_eq_det_jAut g σ hσ h8 hl c₁ c₂ h₁ h₂ τ hτ
    (fun w => cexp (Real.pi / 2 * (zAct σ τ w ⬝ᵥ Q' *ᵥ zAct σ τ w) - Real.pi / 2 * (w ⬝ᵥ Q *ᵥ w))) κ
    (by
      simp only [zAct, mulVec, dotProduct]
      fun_prop)
    (fun w => Complex.exp_ne_zero _) (by simp [zAct]) hκ (fun w => by
      have := hF (h⁻¹ *ᵥ w)
      simp only [hi, hi', e₁] at this
      rw [Complex.exp_sub, ← mul_div_assoc, div_eq_iff (Complex.exp_ne_zero _)]
      linear_combination this)
  obtain ⟨m, hm⟩ := hn
  have hm' : (k + 1) / 2 = m := by omega
  have h'0 : h'.det ≠ 0 := right_ne_zero_of_mul (e₃ ▸ hu.ne_zero)
  rw [hm', hm, e₃, ← hκ2, ← two_mul, pow_mul, mul_pow] at hA
  refine mul_right_cancel₀ (mul_ne_zero hC (mul_ne_zero (pow_ne_zero m h'0)
    (pow_ne_zero m (pow_ne_zero 2 hκ)))) ?_
  linear_combination -hA

end Analytic

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem hostHalfRoot_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h3 : τ H.rt ^ 2 = -(H.d : ℂ) := by simpa using congrArg τ h1
  have h4 : 2 * τ H.w0 = 1 + τ H.rt := by simpa [map_ofNat] using congrArg τ h2
  have h5 : (τ H.rt).re = 0 := by
    have a := congrArg Complex.re h3
    have b := congrArg Complex.im h3
    have c : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp only [pow_two, mul_re, mul_im, neg_re, neg_im, natCast_re, natCast_im, neg_zero] at a b
    by_contra h
    have : (τ H.rt).im = 0 := mul_left_cancel₀ h (by linarith)
    rw [this] at a
    nlinarith [mul_self_nonneg (τ H.rt).re]
  apply τ.injective
  rw [map_add, cc, IsCMField.complexEmbedding_complexConj, map_one, Complex.add_conj]
  have h6 := congrArg Complex.re h4
  simp only [add_re, one_re, h5, add_zero, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] at h6
  exact_mod_cast h6

theorem wG_vac_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (H : Host E) (Dw : Datum H) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), r = Dw.p + Dw.q → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a b, ((Dw.EF a b : ℤ) : ℚ) = EF X (φ a) (φ b)) → ∀ L : Lt E r, SelfD X L → ∀ (M : ℕ), 3 ≤ M → ∀ ga : GL (Fin r) E, IsUn X ga → mapL ga L = L → (∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u') → ∀ v : TF n g, IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → wG X bas idx ga v = v := by
  intro E _ _ _ r X g bas idx n hs hn H Dw φ hr hφi hφs hφE L hL M hM ga hga hgL hgM v hv
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := hostHalfRoot_add_conj_eq_one H
  have hξ : cc (-(X.κ0 / 2)) = -(-(X.κ0 / 2)) := by
    have h1 : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
    rcases X.κ0_xi with h | h <;> simp [cc, h, h1, neg_div]
  obtain ⟨D, ψ, hp, hq, hψL, hψi, -, -, -, hψE⟩ := LatticeDatum.exists_datum_of_selfDual E H Dw r
    (-(X.κ0 / 2)) X.Gm φ L hξ ⟨hφi, hφs, X.Gm_herm, X.Gm_det, hφE⟩ hL.1 (TensLat.span_of_selfD X hL)
    (fun u => (hL.2 u).symm)
  replace hψE : ∀ a b, ((D.EF a b : ℤ) : ℚ) = EF X (ψ a) (ψ b) := hψE
  have hg : g = Module.finrank ℚ E / 2 * (D.p + D.q) := by
    have h1 := Fintype.card_congr idx
    have h2 := RealPlaceEmbeddings.two_card_Psi X
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h1
    rw [hp, hq, ← hr, ← h2, h1, Nat.mul_div_cancel_left _ two_pos]
  obtain ⟨bs, hbs, hb8⟩ := exists_symplectic_basis_adapted_mod_eight E H D g hg
  have hmem : ∀ u, u ∈ L ↔ ∃ a, ψ a = u := fun u => by rw [← hψL]; rfl
  let gi : Matrix (Fin r) (Fin r) E := ((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
  have hgi : ∀ u, (ga : Matrix (Fin r) (Fin r) E) *ᵥ gi *ᵥ u = u := gl_mulVec_inv_mulVec ga
  have hig : ∀ u, gi *ᵥ (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u := RecSum.inv_mulVec ga
  have hgaL : ∀ u ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u ∈ L := fun u hu => by
    rw [← hgL]
    exact ⟨u, hu, rfl⟩
  have hgiL : ∀ u ∈ L, gi *ᵥ u ∈ L := fun u hu => by
    rw [← hgL] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    exact (hig u').symm ▸ hu'
  obtain ⟨gam, hgam⟩ : ∃ gam : D.La ≃ₗ[𝓞 E] D.La, ∀ a, ψ (gam a) = gi *ᵥ ψ a := by
    choose f hf using fun a => (hmem _).1 (hgiL _ ((hmem _).2 ⟨a, rfl⟩))
    choose f' hf' using fun a => (hmem _).1 (hgaL _ ((hmem _).2 ⟨a, rfl⟩))
    exact ⟨{ toFun := f
             invFun := f'
             map_add' := fun a b => hψi (by rw [map_add, hf, hf, hf, map_add, mulVec_add])
             map_smul' := fun c a => hψi (by
               rw [map_smul, hf, hf, map_smul, RingHom.id_apply, mulVec_smul])
             left_inv := fun a => hψi (by rw [hf', hf, hgi])
             right_inv := fun a => hψi (by rw [hf, hf', hig]) }, hf⟩
  have hiso : ∀ a b, D.EF (gam a) (gam b) = D.EF a b := fun a b => by
    refine Int.cast_injective (α := ℚ) ?_
    rw [hψE, hψE, hgam, hgam, EF_def, ← hga, hgi, hgi, EF_def]
  have hfull : ∀ a, ∃ e, gam a = a + M • e := fun a => by
    obtain ⟨u, hu, he⟩ := hgM _ ((hmem _).2 ⟨gam a, rfl⟩)
    obtain ⟨e, rfl⟩ := (hmem _).1 hu
    refine ⟨-e, hψi ?_⟩
    rw [hgam, hgi, ← hgam] at he
    rw [map_add, map_nsmul, map_neg, he, smul_neg, add_neg_cancel_right]
  let N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
    Matrix.of fun u v => bs.symm (gam (bs (Pi.single v 1))) u
  obtain ⟨h8, hdet⟩ := AdaptedDet.blocks_det_mod_eight E H D g M bs gam N hb8 hM hiso hfull
    (fun _ _ => rfl)
  have hsum : ∀ m : Fin g ⊕ Fin g → ℤ, ψ (bs m) = ∑ j, m j • ψ (bs (Pi.single j 1)) := fun m => by
    have hm : m = ∑ j, m j • Pi.single j (1 : ℤ) := by
      funext j; simp [Pi.single_apply]
    conv_lhs => rw [hm]
    simp only [map_sum, map_zsmul]
  obtain ⟨c₁, c₂, C, hC, h₁, h₂, hth⟩ := GlobalTheory.T.periodCoordinateTheta_of_signedHeisenbergVacuum E r X g bas idx n hs hn _ hw hw' L hL v hv
    (fun j => ψ (bs (Pi.single j 1)))
    (fun u => by
      rw [hmem]
      exact ⟨fun ⟨a, ha⟩ => ⟨bs.symm a, by rw [← hsum, bs.apply_symm_apply, ha]⟩,
        fun ⟨m, hm⟩ => ⟨bs m, by rw [hsum, hm]⟩⟩)
    (fun i j => by rw [← hψE, hbs, Int.cast_neg])
  obtain ⟨x, hx⟩ := UnAct.exists_mem_dom X
  have hx' := hga.lact_mem hx
  obtain ⟨hu, hτ, -, -, hz⟩ := hth x hx _ _ rfl rfl
  obtain ⟨hu', hτ', -, -, hz'⟩ := hth _ hx' _ _ rfl rfl
  let P : Frame X.Ψ r → D.La →+ (Fin g → ℂ) := fun y =>
    { toFun := fun a => pv X idx y (ψ a)
      map_zero' := by rw [map_zero, pv, per_zero]; rfl
      map_add' := fun a b => by rw [map_add, pv, per_add]; rfl }
  have hnorm : ∀ y : Frame X.Ψ r,
      IsUnit (Matrix.of fun i k => pv X idx y (ψ (bs (Pi.single (Sum.inl k) 1))) i)⁻¹.det → ∀ k,
      (Matrix.of fun i k => pv X idx y (ψ (bs (Pi.single (Sum.inl k) 1))) i)⁻¹ *ᵥ
        P y (bs (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧
      (Matrix.of fun i k => pv X idx y (ψ (bs (Pi.single (Sum.inl k) 1))) i)⁻¹ *ᵥ
        P y (bs (Pi.single (Sum.inr k) 1)) =
      ((Matrix.of fun i k => pv X idx y (ψ (bs (Pi.single (Sum.inl k) 1))) i)⁻¹ *
        Matrix.of fun i k => pv X idx y (ψ (bs (Pi.single (Sum.inr k) 1))) i) *ᵥ Pi.single k 1 := by
    intro y hy k
    have e : ∀ s : Fin g → Fin g ⊕ Fin g, P y (bs (Pi.single (s k) 1)) =
        (Matrix.of fun i k => pv X idx y (ψ (bs (Pi.single (s k) 1))) i) *ᵥ Pi.single k 1 := fun s => by
      funext i
      simp [P]
    rw [e Sum.inl, e Sum.inr, mulVec_mulVec, mulVec_mulVec, nonsing_inv_mul _
      (isUnit_nonsing_inv_det_iff.1 hy), one_mulVec]
    exact ⟨rfl, rfl⟩
  obtain ⟨σ, hσ, hσe, e₁, e₂, e₃⟩ := PeriodChange.period_change E H D g bs gam N (P x)
    (P (lact ga x)) _ _ _ _ hbs hiso (fun _ _ => rfl)
    (fun a => by
      change pv X idx _ _ = pv X idx _ _
      rw [hgam, pv, pv, ← per_lact x hga, hgi])
    (hnorm x hu) (hnorm _ hu') hτ hτ' hu
  have hv' := RecSum.isVac_wG (idx := idx) hs hn hga hv
  rw [hgL] at hv'
  have ha := (TensVac.vacua E r X g bas idx n hs hn _ hw hw' L hL 1 _ (stdL_mem_Vset 1)).2.1
    _ _ hv hv'.1 hv'.2.2
  have h1 := (wG_laws E r X g bas idx n hs hn ga hga v hv.1).2.1 x hx
  rw [ha, UnAct.thA_smul] at h1
  have h2 := scalar_eq_one hn σ hσ (fun i j => by rw [hσe]; exact h8 j i)
    (by rw [hσe, Matrix.toBlocks_fromBlocks₂₂, Matrix.det_transpose]; exact hdet)
    c₁ c₂ h₁ h₂ _ _ _ _ _ _ hτ hu e₁ e₂ e₃ C (ip (wG X bas idx ga v) v) hC
    (fun z => by rw [← hz z, ← hz' z, ← h1]; rfl)
  rw [ha, h2, one_smul]

end GlobalTheory.VacMult
