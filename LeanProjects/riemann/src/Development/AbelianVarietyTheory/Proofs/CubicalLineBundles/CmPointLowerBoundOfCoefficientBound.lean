import Mathlib
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import ReciprocityTheory.SemistableReduction.LemmaH
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

theorem cmLowerBound_of_coeffBound :
    (∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (H : (K →+* ℂ) → Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin x.P.g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → U.det ≠ 0 → 1 ≤ La → (∀ σ, (H σ).PosDef) → (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) → (∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin x.P.g → K), IsLocGen p cd abelian₂.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd) → (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) → (∀ j, (ℓ j).ndeg = logOm / 2) → MvPolynomial.coeff μ G ≠ 0 → MvPolynomial.coeff μ G ∈ (lineNN T.dual ℓ c μ n).I → (∀ σ, 0 < S σ) → 0 < Rr → (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) → ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) → - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (x.P.g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)) → ReciprocityTheory.MultiplicativeHeights.LemmaHStatement → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (e : (Σ b, Fin (m b)) ≃ Fin x.P.g) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (G : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (n r : ℕ) (La logOm : ℝ) (S : (K →+* ℂ) → ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → (∀ j, (ℓ j).ndeg = logOm / 2) → U.det ≠ 0 → G ≠ 0 → 1 ≤ La → 1 ≤ r → (∀ b, m b ≤ r) → (∀ σ, 0 < S σ) → (∀ p, Step5Loc e T.dual abelian₂ ℓ U G n p) → (∀ σ, Step5Arch e T.dual abelian₂ ℓ U G a n La (S σ) σ) → - ((pDeg logOm + (1 / 2) * Real.log La) * (((∑ b, ∑ i, a b i : ℕ) : ℝ) + (x.P.g : ℝ) * n)) - ((∑ b, ∑ i, a b i : ℕ) : ℝ) * Real.log ((r : ℝ) * La) ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ) := by
  intro hLK hH K _ _ x T abelian₂ B _ _ m e ℓ U G a n r La logOm S hT hLam hloc harch hℓ hℓdeg hU hG hLa hr hmr hS hS5L hS5A
  classical
  obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.mp hG
  have hTd : T.dual.Good := (degree_algebraic K T T hT hT).2.2.1
  obtain ⟨σ₀⟩ : Nonempty (K →+* ℂ) := inferInstance

  have hsum : ∑ v, μ v = ∑ b, ∑ i, a b i := by
    obtain ⟨H₀, -, -, -, heq, -⟩ := hS5A σ₀
    refine subst_homogeneous B m a (MvPolynomial.map σ₀ G) (fun _ => 1) heq μ ?_
    rw [substFr_one, MvPolynomial.coeff_map]
    exact (map_ne_zero σ₀).mpr hμ
  unfold Step5Arch at hS5A
  choose Hs hHs using hS5A
  have hRr : (0 : ℝ) < (r : ℝ) * La := mul_pos (Nat.cast_pos.mpr hr) (by linarith)

  have hmem : MvPolynomial.coeff μ G ∈ (lineNN T.dual ℓ (fun v : FrVar m => e ⟨v.1, v.2.2⟩) μ n).I := by
    refine coeff_mem_of_local K x.P.g ℓ T.dual (FrVar m) _ μ n _ hTd hℓ fun p => ?_
    obtain ⟨t, cd, cl, ht, hcd, hcl, hv, V, K', _, _, _, _, _, _, f, Ub, hVc, hfin, hind, hUb, hclUb, hW⟩ := hS5L p
    refine ⟨t, cl, ht, hcl, ?_⟩
    have htn : t ^ n ≠ 0 := pow_ne_zero _ ht.1
    have hftn : f (t ^ n) ≠ 0 := (map_ne_zero f).mpr htn
    obtain ⟨w, hw⟩ := coeff_integral_local V K' B m (MvPolynomial.map f G) Ub (fun b j => f (cl (e ⟨b, j⟩)))
      (f (t ^ n)) hVc hfin hftn hUb hclUb hW μ
    have hrange : f (MvPolynomial.coeff μ G * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) ∈
        Set.range (algebraMap V K') := by
      refine ⟨w, ?_⟩
      rw [map_div₀, map_mul, map_prod]
      simp only [map_pow]
      rw [← map_pow f t n, ← MvPolynomial.coeff_map, hw, mul_div_cancel_left₀ _ hftn]
    have h1 := (hind _).mp hrange
    calc p.valuation K (MvPolynomial.coeff μ G * ∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v)
        = p.valuation K (MvPolynomial.coeff μ G * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) *
            p.valuation K (t ^ n) := by
          rw [← map_mul, div_mul_cancel₀ _ htn]
      _ ≤ p.valuation K (t ^ n) := mul_le_of_le_one_left' h1

  have harch' : ∀ (σ : K →+* ℂ) (z : FrVar m → ℂ),
      (∀ v, ‖z v‖ * (ℓ ((fun v : FrVar m => e ⟨v.1, v.2.2⟩) v)).n σ ≤ 1) →
      ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * ((r : ℝ) * La) ^ (∑ v, μ v) := by
    intro σ z hz
    obtain ⟨hpd, -, hbd, heq, hY⟩ := hHs σ
    have hTn : 0 < T.dual.n σ ^ n := pow_pos (hTd.2 σ) n
    have hA := ArchTie_of hH B m a (MvPolynomial.map σ G) (fun b => gramBlock e U (Hs σ) σ b) (fun _ => 1)
      (fun b j => (ℓ (e ⟨b, j⟩)).n σ) (S σ / T.dual.n σ ^ n) La r
      (fun b => gramBlock_posDef e U (Hs σ) σ b hpd hU) heq
      (fun X hX => by rw [le_div_iff₀ hTn]; exact hY X hX)
      (fun b j => (hℓ _).2 σ) (by linarith) hmr
      (fun b j => (hermitian_form_gramBlock_basis e U (Hs σ) σ b j).le.trans (hbd _)) z hz
    rw [substFr_one] at hA
    rw [hsum]
    calc ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n
        ≤ S σ / T.dual.n σ ^ n * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i) * T.dual.n σ ^ n :=
          mul_le_mul_of_nonneg_right hA hTn.le
      _ = S σ * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i) := by
          rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hTn.ne']
  unfold Step5Loc at hS5L
  have key := hLK K x T abelian₂ ℓ U Hs La logOm (FrVar m) (fun v => e ⟨v.1, v.2.2⟩) G μ n S ((r : ℝ) * La)
    hT hLam hloc harch hℓ hU hLa (fun σ => (hHs σ).1) (fun σ => (hHs σ).2.1)
    (fun p => by
      obtain ⟨t, cd, cl, ht, hcd, hcl, hv, -⟩ := hS5L p
      exact ⟨cd, cl, hcd, hcl, hv⟩)
    (fun σ j => (hHs σ).2.2.1 j) hℓdeg hμ hmem hS hRr harch'
  have hc : (∑ v, (μ v : ℝ)) = ((∑ b, ∑ i, a b i : ℕ) : ℝ) := by
    rw [← hsum, Nat.cast_sum]
  rw [hc] at key
  exact key

end GlobalTheory
