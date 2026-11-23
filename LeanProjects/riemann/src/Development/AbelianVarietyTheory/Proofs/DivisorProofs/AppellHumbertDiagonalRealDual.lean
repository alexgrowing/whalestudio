import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundleStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusRealMultAppellHumbertStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductTorusFactorAppellHumbertStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedUniformizationPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyPositivePolarizationProjectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.RiemFormKer.smul_mem_lattice : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∀ x : Fin (Module.finrank ℚ F) → ℂ, (∀ l : u.Λ, ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (x j * starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j))).im = 2 * n) →
    ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → (fun j ↦ (e j (a : F) : ℂ) * x j) ∈ u.Λ := by
  intro F _ _ _ 𝔠 X c hc u e hu h χ hAH x hx a ha
  obtain ⟨U0, hU0⟩ := GlobalTheory.T.product_abelian_uniformization X.A X.ab (X.diag c) _ u
  have hAb2 := AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab
  obtain ⟨U, H, χ', hUex, hF⟩ := GlobalTheory.T.exists_appell_humbert_line_bundle (X.A ⊗ X.A) hAb2 _ _ U0 (X.P c) (X.isLB c)
  have hex : ∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y) := fun x y => by rw [hUex]; exact hU0 x y
  have hb := GlobalTheory.T.torus_real_mult_appell_humbert F 𝔠 X c hc u e hu h χ hAH U H χ' hex hF
  have hχ := GlobalTheory.T.product_torus_factor_appell_humbert X.A (X.diag c) _ u (X.P c) (X.isLB c) (X.rig₂ c) U H χ' hex hF
    (fun z w => by rw [hb]; simp [hermForm])
  obtain ⟨u', hu'ex, hu'ch, hu'fr⟩ := GlobalTheory.T.translated_uniformization_pullback X.A (X.diag c) _ u (X.P c) U hex x
  have hgen : HasGen ((X.P c).pull (lift (𝟙 X.A) (toUnit X.A ≫ u.ex x)).left) := by
    refine GlobalTheory.T.theta_nonvanishing_bundle_generated X.A X.ab (GlobalTheory.T.totally_positive_polarization_projective F 𝔠 X c hc) _ (LB.isLB_pull (X.isLB c) _) _ u'
      (fun z => Complex.exp (Real.pi * hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) z x / 2)) ?_
      (fun z => Complex.exp_ne_zero _) ?_
    · simp only [hermForm, dotProduct]
      fun_prop
    · intro l hl i z hz
      have hlu : l ∈ u.Λ := by rw [← u.ker, ← hu'ex]; exact (u'.ker l).2 hl
      have h0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
      have hm : Fin.append l (0 : Fin (Module.finrank ℚ F) → ℂ) ∈ U.Λ := by
        rw [← U.ker, hex, (u.ker l).2 hlu, ← h0, ← hex]
        have hz0 : Fin.append (0 : Fin (Module.finrank ℚ F) → ℂ) (0 : Fin (Module.finrank ℚ F) → ℂ) = 0 := by
          funext k
          refine Fin.addCases (fun k => ?_) (fun k => ?_) k
          · simp only [Fin.append_left, Pi.zero_apply]
          · simp only [Fin.append_right, Pi.zero_apply]
        rw [hz0]
        exact (U.ker 0).2 U.Λ.zero_mem
      have hz' : ⊤ ≤ (U.ex (Fin.append z x)).left ⁻¹ᵁ (X.P c).U (i PUnit.unit) := (hu'ch i z).1 hz
      have happ : Fin.append z x + Fin.append l 0 = Fin.append (z + l) x := by
        funext k
        refine Fin.addCases (fun k => ?_) (fun k => ?_) k
        · simp only [Pi.add_apply, Fin.append_left]
        · simp only [Pi.add_apply, Fin.append_right, Pi.zero_apply, add_zero]
      have e1 : hermForm H (Fin.append z x) (Fin.append l 0) =
          hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l / 2 := by
        rw [hb]; simp [hermForm]
      have e2 : hermForm H (Fin.append l 0) (Fin.append l 0) = 0 := by
        rw [hb]; simp [hermForm]
      have hf : U.fr (i PUnit.unit) (Fin.append z x) = Complex.exp (Real.pi *
          (hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l / 2)) * U.fr (i PUnit.unit) (Fin.append (z + l) x) := by
        have h3 := hF.2.2 ⟨_, hm⟩ (i PUnit.unit) (Fin.append z x) hz'
        rw [hχ ⟨_, hm⟩ l rfl, _root_.one_mul] at h3
        dsimp only at h3
        rw [h3, happ]
        congr 2
        rw [show (Fin.append z x ⬝ᵥ H.mulVec (star (Fin.append l 0))) = hermForm H (Fin.append z x) (Fin.append l 0) from rfl,
          show (Fin.append l 0 ⬝ᵥ H.mulVec (star (Fin.append l 0))) = hermForm H (Fin.append l 0) (Fin.append l 0) from rfl,
          e1, e2]
        ring
      obtain ⟨n, hn⟩ := hx ⟨l, hlu⟩
      have hs : hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l = ∑ j, (h j : ℂ) * (x j * starRingEnd ℂ (l j)) := by
        simp only [hermForm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hsw : hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) l x =
          starRingEnd ℂ (hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l) := by
        simp only [hermForm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def, map_sum, map_mul,
          Complex.conj_conj, Complex.conj_ofReal]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hadd : hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) (z + l) x =
          hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) z x + hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) l x := by
        simp only [hermForm, add_dotProduct]
      have hc : starRingEnd ℂ (hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l) =
          hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l - 4 * n * Complex.I := by
        rw [hs]
        apply Complex.ext
        · simp
        · simp only [Complex.conj_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im]
          rw [hn]
          simp
          ring
      rw [hu'fr, hu'fr, hf]
      beta_reduce
      rw [← _root_.mul_assoc, ← Complex.exp_add]
      congr 1
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨-n, ?_⟩
      rw [hadd, hsw, hc]
      push_cast
      ring
  have hgen2 : HasGen ((X.P c).pull (lift (fst X.A (𝟙_ (Over (Sp ℂ)))) (snd X.A (𝟙_ (Over (Sp ℂ))) ≫ u.ex x)).left) := by
    obtain ⟨t, ht⟩ := hgen
    have hm : lift (fst X.A (𝟙_ (Over (Sp ℂ)))) (snd X.A (𝟙_ (Over (Sp ℂ))) ≫ u.ex x) =
        fst X.A (𝟙_ (Over (Sp ℂ))) ≫ lift (𝟙 X.A) (toUnit X.A ≫ u.ex x) := by
      ext
      · simp
      · have hs : snd X.A (𝟙_ (Over (Sp ℂ))) = fst X.A (𝟙_ (Over (Sp ℂ))) ≫ toUnit X.A := toUnit_unique _ _
        simp [hs]
    rw [hm, Over.comp_left]
    exact ⟨LB.pullGen _ (fun _ : PUnit => _) (fun _ => 1) t (fst X.A _).left, DVR.pullGen_isGen _ _ _ t ht _⟩
  have h1 := X.ker c (𝟙_ _) (u.ex x) hgen2 a ha
  rw [← u.ker, hu a x]
  exact h1
