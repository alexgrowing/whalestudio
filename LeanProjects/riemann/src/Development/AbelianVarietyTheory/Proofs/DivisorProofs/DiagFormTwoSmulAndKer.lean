import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoSymmetricBirigidifiedComplStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingComplexValueUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorOfHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierTrivialization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsRapoportOfBasis
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertDiagonalReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfComplexExponentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfLineBundleIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackTrivialOfImFormIntStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

open GlobalTheory.CechPic in

theorem GlobalTheory.SymBirig.diag_form_two_smul_and_ker : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → ∃ E₁ : LinearMap.BilinForm ℤ La, EF = (2 : ℤ) • E₁ ∧ ∀ (k : ℕ) (a : La), 0 < k → ((∀ y, (k : ℤ) ∣ E₁ a y) ↔ ∃ t : (P.pull (lift (snd A (Over.mk (𝟙 (Sp ℂ))) ≫ e ((k : ℂ)⁻¹ • Q a)) (fst A (Over.mk (𝟙 (Sp ℂ))))).left).Gen, t.IsGen) := by
  intro A _ _ g hA hg P hP h1 h2 hsym hamp e La _ Q EF hexp hQ hker hW
  obtain ⟨M, hM, hPM⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hg P hP h1 h2 hsym
  have hPM' : LBIso P (abelian₂ A M) := hPM
  obtain ⟨u, Hm, χ, hue, hF⟩ := GlobalTheory.T.exists_appellHumbertFrame_of_complexExponential A g hA hg M hM e hexp
  obtain ⟨u', χ', hue', hF'⟩ := GlobalTheory.TorusRM.exists_isFactorAH_lam_diag g A hA M u Hm χ hM hF
  have hlam : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hD := GlobalTheory.GenSpread.lbIso_pullback hPM' (lift (𝟙 A) (𝟙 A)).left
  obtain ⟨v, ψ, hve, hFv⟩ := GlobalTheory.T.exists_appellHumbertFrame_of_lineBundleIso A g _ _ u' _ χ' (pull_isLB hP _) (pull_isLB hlam _) hD hF'
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ (pull_isLB hP _) hamp g v _ ψ hFv.1 hFv.2.1 hFv.2.2
  have hAH := GlobalTheory.TorusRM.isAH_of_isFactorAH hFv hpos
  have hmemu : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range := fun z => by rw [← u.ker, hue]; exact hker z
  have hmemv : ∀ z, z ∈ v.Λ ↔ z ∈ Q.range := fun z => by rw [← v.ker, hve, hue', hue]; exact hker z
  have hvx : ∀ z, v.ex z = e z := fun z => by rw [hve, hue', hue]
  have hNex : ∀ a b : La, ∃ n : ℤ, (hermForm Hm (Q a) (Q b)).im = n := fun a b =>
    GlobalTheory.RiemInt.im_hermForm_int hM u hF ⟨Q a, (hmemu _).2 ⟨a, rfl⟩⟩ ⟨Q b, (hmemu _).2 ⟨b, rfl⟩⟩
  choose N hN using hNex
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have key : ∀ a b : La, EF a b = 2 * N a b := by
    intro a b
    have hk : ∀ k : ℕ, 0 < k → ∃ n : ℤ, ((EF a b : ℂ) - 2 * N a b) / k = n := by
      intro k hk
      let c₁ : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k)) (Complex.exp_ne_zero _)
      let c₂ : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) *
        (((Q a ⬝ᵥ ((2 : ℂ) • Hm) *ᵥ star (Q b)).im : ℝ) : ℂ) / k)) (Complex.exp_ne_zero _)
      have w1 := hW k a b c₁ hk rfl
      have w2 := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm A hA _ (pull_isLB hP _) g v _ ψ hAH k (Q a) (Q b) c₂ hk
        ((hmemv _).2 ⟨a, rfl⟩) ((hmemv _).2 ⟨b, rfl⟩) rfl
      rw [hvx, hvx] at w2
      have h3 := congrArg (fun c : ℂˣ => (c : ℂ)) (GlobalTheory.T.weilPairing_complex_value_unique (Sp ℂ) A g hA hg _ (pull_isLB hP _) (𝟙 (Sp ℂ)) k _ _ c₁ c₂ w1 w2)
      simp only [c₁, c₂, Units.val_mk0] at h3
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h3
      have h2 : ((Q a ⬝ᵥ ((2 : ℂ) • Hm) *ᵥ star (Q b)).im) = 2 * (N a b : ℝ) := by
        have h4 := hN a b
        unfold hermForm at h4
        have h5 : ((2 : ℂ) • Hm) *ᵥ star (Q b) = (2 : ℂ) • (Hm *ᵥ star (Q b)) := by
          rw [Matrix.smul_mulVec]
        rw [h5, dotProduct_smul, smul_eq_mul, Complex.mul_im, h4]
        simp
      rw [h2] at hn
      refine ⟨-n, mul_left_cancel₀ hpi ?_⟩
      push_cast at hn ⊢
      linear_combination (-1 : ℂ) * hn
    obtain ⟨K, hK⟩ : ∃ K : ℕ, K = (EF a b - 2 * N a b).natAbs + 1 := ⟨_, rfl⟩
    obtain ⟨n, hn⟩ := hk K (by omega)
    have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
    rw [div_eq_iff hK0] at hn
    have e2 : EF a b - 2 * N a b = (K : ℤ) * n := Int.cast_injective (α := ℂ) (by push_cast; rw [hn]; ring)
    have e3 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨n, e2⟩ (by rw [Int.natAbs_natCast]; omega)
    omega
  have hadd : ∀ a a' b, N (a + a') b = N a b + N a' b := by
    intro a a' b
    have h := key (a + a') b
    rw [map_add, LinearMap.add_apply, key, key] at h
    omega
  have hadd' : ∀ a b b', N a (b + b') = N a b + N a b' := by
    intro a b b'
    have h := key a (b + b')
    rw [map_add, key, key] at h
    omega
  have hsm : ∀ (c : ℤ) a b, N (c • a) b = c * N a b := by
    intro c a b
    have h := key (c • a) b
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul, key] at h
    have h' : 2 * (N (c • a) b - c * N a b) = 0 := by linear_combination -h
    linear_combination (mul_eq_zero.1 h').resolve_left two_ne_zero
  have hsm' : ∀ (c : ℤ) a b, N a (c • b) = c * N a b := by
    intro c a b
    have h := key a (c • b)
    rw [map_zsmul, smul_eq_mul, key] at h
    have h' : 2 * (N a (c • b) - c * N a b) = 0 := by linear_combination -h
    linear_combination (mul_eq_zero.1 h').resolve_left two_ne_zero
  refine ⟨LinearMap.mk₂ ℤ N hadd (fun c a b => by rw [hsm, smul_eq_mul]) hadd' (fun c a b => by rw [hsm', smul_eq_mul]), ?_, ?_⟩
  · ext a b
    simp [key]
  · intro k a hk
    simp only [LinearMap.mk₂_apply]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hwl : ∀ y, (((k : ℂ)⁻¹ • Q a) ⬝ᵥ Hm *ᵥ star (Q y)).im = (N a y : ℝ) / k := by
      intro y
      have h4 := hN a y
      unfold hermForm at h4
      rw [smul_dotProduct, smul_eq_mul, show ((k : ℂ)⁻¹) = (((k : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
        Complex.im_ofReal_mul, h4, div_eq_inv_mul]
    have stepA : (∀ y, (k : ℤ) ∣ N a y) ↔
        ∀ l ∈ u.Λ, ∃ n : ℤ, (((k : ℂ)⁻¹ • Q a) ⬝ᵥ Hm.mulVec (star l)).im = n := by
      constructor
      · rintro h l hl
        obtain ⟨y, rfl⟩ := (hmemu l).1 hl
        obtain ⟨n, hn⟩ := h y
        exact ⟨n, by rw [hwl, hn]; push_cast; field_simp⟩
      · intro h y
        obtain ⟨n, hn⟩ := h (Q y) ((hmemu _).2 ⟨y, rfl⟩)
        rw [hwl, div_eq_iff hk0] at hn
        exact ⟨n, by exact_mod_cast (show (N a y : ℝ) = (k : ℝ) * n by rw [hn]; ring)⟩
    have stepB := (show _ ↔ _ from ⟨GlobalTheory.T.mumfordBundle_pullback_trivial_of_im_form_int A g hA M u Hm χ hM hF ((k : ℂ)⁻¹ • Q a), fun h => by
      obtain ⟨θ, hθ, h0, hp⟩ := GlobalTheory.TorusRM.exists_theta_of_hasGen_lam_pull g A hA M u Hm χ hM hF _ h
      exact GlobalTheory.ThetaLiouville.im_form_mem_int g u.Λ u.full Hm hF.1 _ θ hθ h0 hp⟩)
    refine stepA.trans (stepB.trans ?_)
    have c1 := GlobalTheory.RealMult.Elliptic.cls_pull_lam hM (fst A (𝟙_ (Over (Sp ℂ))))
      (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a)) (pull_isLB hlam _)
    have c2 := GlobalTheory.RealMult.Elliptic.cls_pull_lam hM (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a))
      (fst A (𝟙_ (Over (Sp ℂ)))) (pull_isLB hlam _)
    have c3 : cls (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a)) (fst A (𝟙_ (Over (Sp ℂ))))).left)
        (pull_isLB hP _) = cls ((abelian₂ A M).pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a))
          (fst A (𝟙_ (Over (Sp ℂ))))).left) (pull_isLB hlam _) := by
      rw [cls_pull hP, cls_pull hlam, (cls_eq_iff hP hlam).2 hPM']
    rw [← cls_eq_zero_iff (pull_isLB hlam _), c1, lam_comm, ← c2, ← c3, cls_eq_zero_iff, hue]
    exact Iff.rfl
