import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjGLOfCharpolyEqOfSeparableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCharpolyEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryConjIffExistsCentralizerNormStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NonsplitPlaceNormCentraliserStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNonsplitSignTotallyPositiveEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetHermitianTotallyPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SesquilinearDetOrdSignOnKernelConjGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEqStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.HermitianLocalDataAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LandherrStandardDefiniteHermitianCmFieldStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnitaryClasses

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem conjGL : ∀ (K : Type) [Field K] (n : ℕ) (a b : GL (Fin n) K), a.val.charpoly = b.val.charpoly → a.val.charpoly.Separable → ∃ h : GL (Fin n) K, b = h⁻¹ * a * h := GlobalTheory.T.exists_conj_GL_of_charpoly_eq_of_separable

theorem companionEll : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), ∀ P ∈ Ell E n, ∃ a : GL (Fin n) E, a.val.charpoly = P := GlobalTheory.T.exists_GL_charpoly_eq_of_mem_Ell

theorem unitConj : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (γ h : GL (Fin n) K), (∃ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) K), h⁻¹ * γ * h = g⁻¹ * γ * g) ↔ ∃ c : Matrix (Fin n) (Fin n) K, c * γ.val = γ.val * c ∧ cT σ c * c = (h.val * cT σ h.val)⁻¹ := GlobalTheory.T.exists_unitary_conj_iff_exists_centralizer_norm

theorem normHasse : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ h : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → h⁻¹ * γ * h ∈ UE E n → (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val * cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val)⁻¹) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = (h.val * cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val)⁻¹ := GlobalTheory.T.nonsplit_place_norm_centraliser

theorem signProd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ d : E, d ≠ 0 → (∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ d = r) → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) d)) = 1 := GlobalTheory.T.finprod_nonsplit_sign_totallyPositive_eq_one

theorem gramPos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (V : Submodule E (Fin n → E)), (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det ≠ 0 ∧ ∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det = r := GlobalTheory.T.gram_det_hermitian_totally_positive

theorem sgnConj : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K), (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (Q : K[X]) (a k : GL (Fin n) K), sgnOn σ 1 Q (k⁻¹ * a * k).val = sgnOn σ (cT σ (k⁻¹).val * (k⁻¹).val) Q a.val := GlobalTheory.T.sesquilinearDetOrdSignOnKernel_conj_GL

theorem baseChangeSign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (H A : Matrix (Fin n) (Fin n) E), (-1 : ℂ) ^ ordL (gramOn (cj w) (H.map (algebraMap E (w.adicCompletion E))) (LinearMap.ker (Matrix.toLin' (A.map (algebraMap E (w.adicCompletion E)))))).det = (-1) ^ ordL (algebraMap E (w.adicCompletion E) (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H (LinearMap.ker (Matrix.toLin' A))).det) := GlobalTheory.T.gramKernelSign_nonsplit_baseChange_eq

theorem existForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ k m : GL (Fin n) (w.adicCompletion E), k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k ∈ GlobalTheory.LFun.KGL w n ∧ m ∈ GlobalTheory.LFun.KGL w n ∧ m.val = cT (cj w) k.val * H w * k.val) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H w) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) → ∃ H' : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H' ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H' * γ₀.val = H' ∧ (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H'.map τ = cT (starRingEnd ℂ) Q * Q) ∧ ∀ w, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H'.map (algebraMap E (w.adicCompletion E)) = cT (cj w) c.val * H w * c.val := GlobalTheory.T.hermitian_local_data_almost_all

theorem landherrStd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ w : Pl E, ¬ IsSplitAt w → ∃ g : Matrix (Fin n) (Fin n) (w.adicCompletion E), H.map (algebraMap E (w.adicCompletion E)) = cT (cj w) g * g) → ∃ h : GL (Fin n) E, H = cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val * h.val := GlobalTheory.T.landherr_standard_definite_hermitian_cmField

theorem part1 (hU : Unr E) {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) {P : E[X]} (hP : P ∈ Ell E n) (γ γ' : UE E n)
    (h1 : γ.1.val.charpoly = P) (h2 : γ'.1.val.charpoly = P)
    (hloc : ∀ w ∈ S, ∃ g : UL n w, locPt w γ' = g⁻¹ * locPt w γ * g) : ∃ g : UE E n, γ' = g⁻¹ * γ * g := by
  obtain ⟨h, hh⟩ := conjGL E n γ.1 γ'.1 (h1.trans h2.symm) (h1 ▸ hP.2.2.1)
  have hγ' : h⁻¹ * γ.1 * h ∈ UE E n := hh ▸ γ'.2
  obtain ⟨c, hc1, hc2⟩ := normHasse E hU n γ.1 h γ.2 (h1 ▸ hP) hγ' (fun w hw => by
    obtain ⟨g, hg⟩ := hloc w (mem_S hS hw)
    have hUL : UL n w = UJ (cj w) 1 := by unfold UL; rw [if_neg hw]
    refine (unitConj _ (cj w) n _ _).1 ⟨g.1, hUL ▸ g.2, ?_⟩
    have := congrArg Subtype.val hg
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, locPt_val hU] at this
    rw [← map_inv, ← map_mul, ← map_mul, ← hh]; exact this)
  obtain ⟨g, hg, hgg⟩ := (unitConj E _ n γ.1 h).2 ⟨c, hc1, hc2⟩
  exact ⟨⟨g, hg⟩, Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; rw [hh, hgg])⟩

theorem part2 (hU : Unr E) {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) (γ : UE E n) (P₁ : E[X]) :
    ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (locPt w γ).1 = 1 := by
  obtain ⟨hd0, hdpos⟩ := gramPos E n (LinearMap.ker (Matrix.toLin' (aeval γ.1.val P₁)))
  rw [← signProd E hU S hS _ hd0 hdpos]
  apply finprod_mem_congr rfl
  intro w _
  by_cases hw : IsSplitAt w
  · rw [if_pos hw]; unfold kapSign; rw [if_pos hw]
  · rw [if_neg hw, kapSign_eq w hw, locPt_val hU]
    unfold sgnOn
    have hA := aeval_map_mat w γ.1.val P₁
    have := baseChangeSign E hU w hw n 1 (aeval γ.1.val P₁)
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [← this, ← hA]
    rfl

theorem part3 (hU : Unr E) {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) {P : E[X]} (hP : P ∈ Ell E n)
    (y : ∀ w : Pl E, UL n w) (hy : ∀ w, (y w).1.val.charpoly = atPl w P) (hK : ∀ᶠ w in cofinite, y w ∈ KL n w)
    (hsg : ∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (y w).1 = 1) :
    ∃ γ : UE E n, γ.1.val.charpoly = P ∧ ∀ w ∈ S, ∃ g : UL n w, locPt w γ = g⁻¹ * y w * g := by
  obtain ⟨γ₀, hγ₀⟩ := companionEll E n P hP
  have hAcp : ∀ w : Pl E, (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀).val.charpoly = atPl w P :=
    fun w => by rw [← hγ₀]; exact Matrix.charpoly_map _ _
  have hsep : ∀ w : Pl E, (atPl w P).Separable := fun w => hP.2.2.1.map
  have hk : ∀ w : Pl E, ∃ k : GLw n w,
      (y w).1 = k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k := fun w =>
    conjGL _ n _ (y w).1 ((hAcp w).trans (hy w).symm) (hAcp w ▸ hsep w)
  choose k hk using hk
  have hinvol : ∀ w : Pl E, ∀ x, cj w (cj w x) = x := fun w => (GlobalTheory.ConjAtPlace.main E hU w).2.1
  have hval : ∀ w : Pl E, ∀ x, Valued.v (cj w x) = Valued.v x := fun w => (GlobalTheory.ConjAtPlace.main E hU w).2.2.1
  have hUL : ∀ w : Pl E, ¬ IsSplitAt w → UL n w = UJ (cj w) 1 := fun w hw => by unfold UL; rw [if_neg hw]
  have hyU : ∀ w : Pl E, ¬ IsSplitAt w → cT (cj w) (y w).1.val * 1 * (y w).1.val = 1 := fun w hw => by
    have h3 : ∀ z : GLw n w, z ∈ UL n w → cT (cj w) z.val * 1 * z.val = 1 := by
      intro z hz; unfold UL at hz; rw [if_neg hw] at hz; exact hz
    exact h3 _ (y w).2
  obtain ⟨H', hH'h, hH'i, hH'p, hH'l⟩ := existForm E hU S hS n γ₀ (hγ₀ ▸ hP)
    (fun w => cT (cj w) ((k w)⁻¹).val * ((k w)⁻¹).val)
    (fun w hw => ⟨herm_of _ (hinvol w) _, det_ne _ _,
      inv_of_unit _ (k w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀) (hk w ▸ hyU w hw)⟩)
    (hK.mono fun w hw _ => ⟨k w, 1, by rw [← hk w]; exact (Subgroup.mem_subgroupOf).1 hw, one_mem _,
      (one_of _ (k w)).symm⟩)
    (fun P₁ hm hd => by
      refine Eq.trans ?_ (hsg P₁ hm (hγ₀ ▸ hd))
      apply finprod_mem_congr rfl
      intro w _
      by_cases hw : IsSplitAt w
      · rw [if_pos hw]; unfold kapSign; rw [if_pos hw]
      · rw [if_neg hw, kapSign_eq w hw, hk w, sgnConj _ (cj w) (hval w)]
        rfl)
  obtain ⟨h, hh⟩ := landherrStd E hU n H' hH'h hH'p (fun w hw => by
    obtain ⟨c, -, hc⟩ := hH'l w hw
    exact ⟨((k w)⁻¹).val * c.val, by rw [hc, cT_mul]; simp only [Matrix.mul_assoc]⟩)
  have hγU : h * γ₀ * h⁻¹ ∈ UE E n := unit_of_form _ γ₀ h (by rw [← hh]; exact hH'i)
  refine ⟨⟨_, hγU⟩, ?_, fun w hwS => ?_⟩
  · show (h.val * γ₀.val * (h⁻¹).val).charpoly = P
    rw [Matrix.coe_units_inv, ← hγ₀]
    exact Matrix.charpoly_units_conj h γ₀.val
  · by_cases hw : IsSplitAt w
    · have hb : ((locPt w (⟨_, hγU⟩ : UE E n) : UL n w) : GLw n w).val.charpoly = (y w).1.val.charpoly := by
        rw [locPt_val hU, hy w, ← hAcp w]
        show ((h * γ₀ * h⁻¹ : GL (Fin n) E).val.map _).charpoly = (γ₀.val.map _).charpoly
        rw [Matrix.charpoly_map, Matrix.charpoly_map]
        congr 1
        show (h.val * γ₀.val * (h⁻¹).val).charpoly = _
        rw [Matrix.coe_units_inv]
        exact Matrix.charpoly_units_conj h γ₀.val
      obtain ⟨h', hh'⟩ := conjGL _ n (y w).1 _ hb.symm ((hy w) ▸ hsep w)
      have hmem : h' ∈ UL n w := by unfold UL; rw [if_pos hw]; trivial
      exact ⟨⟨h', hmem⟩, Subtype.ext (by simpa using hh')⟩
    · obtain ⟨c, hc1, hc2⟩ := hH'l w hw
      have hg : (k w)⁻¹ * c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h)⁻¹ ∈ UL n w := by
        rw [hUL w hw]
        refine unit_of_two _ (k w) c (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h) _ hc2 ?_
        rw [hh, Matrix.map_mul, cT_map hU w hw]; rfl
      refine ⟨⟨_, hg⟩, Subtype.ext ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [locPt_val hU, hk w]
      have hcA : c * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ =
          GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * c := Units.ext hc1
      have key : ∀ x : GLw n w, c⁻¹ * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * (c * x)) =
          GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * x := fun x => by
        rw [← mul_assoc _ c x, ← hcA, mul_assoc, inv_mul_cancel_left]
      show GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (h * γ₀ * h⁻¹) = _
      simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, key]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, (∀ γ γ' : UE E n, γ.1.val.charpoly = P → γ'.1.val.charpoly = P → (∀ w ∈ S, ∃ g : UL n w, locPt w γ' = g⁻¹ * locPt w γ * g) → ∃ g : UE E n, γ' = g⁻¹ * γ * g) ∧ (∀ γ : UE E n, γ.1.val.charpoly = P → ∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (locPt w γ).1 = 1) ∧ ∀ y : ∀ w : Pl E, UL n w, (∀ w, (y w).1.val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ KL n w) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (y w).1 = 1) → ∃ γ : UE E n, γ.1.val.charpoly = P ∧ ∀ w ∈ S, ∃ g : UL n w, locPt w γ = g⁻¹ * y w * g := by
  intro E _ _ _ hU n _ S hS P hP
  exact ⟨fun γ γ' h1 h2 hl => part1 hU hS hP γ γ' h1 h2 hl, fun γ _ P₁ _ _ => part2 hU hS γ P₁,
    fun y hy hK hsg => part3 hU hS hP y hy hK hsg⟩

end GlobalTheory.UnitaryClasses
