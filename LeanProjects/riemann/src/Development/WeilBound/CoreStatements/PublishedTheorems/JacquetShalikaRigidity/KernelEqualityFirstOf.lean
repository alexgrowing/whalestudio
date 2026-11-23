import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKEq1

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

def fC (η : (Fin k → Ad E) → ℝ) (s : (Fin k → Ad E) → GA E k) (φ : XB E k) (g : GA E k) : ℂ :=
  (η (lastRow g) : ℂ) * φ (g * (s (lastRow g))⁻¹)

theorem whit_fC (hP2 : P2) (hP3 : P3) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (φ : XB E k)
    (η : (Fin k → Ad E) → ℝ) (s : (Fin k → Ad E) → GA E k) (g : GA E k) :
    whit ψ (k - 1) (fC η s φ) g = (η (lastRow g) : ℂ) * Wh ψ φ (g * (s (lastRow g))⁻¹) := by
  have hl := (hP2 E k ψ hψ).2.2.2.2.2.2.1
  refine hP3 E k ψ (k - 1) _ _ g _ _ fun u hu => ?_
  simp only [fC, hl u g hu, mul_assoc]

theorem sq_wt_le {B : ℝ} (hB : 1 ≤ B) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ B * y) (M : ℕ) :
    min 1 x ^ M ≤ B ^ M * min 1 y ^ M := by
  rw [← mul_pow]
  refine pow_le_pow_left₀ (le_min zero_le_one hx.le) ?_ M
  rw [mul_min_of_nonneg _ _ (by linarith)]
  exact min_le_min (by linarith) hxy

theorem sq_fC (hD0 : D0) (hP2 : P2) (hG5t : RowsInCompactSet) (hK1 : K1) (hk : 1 ≤ k) {ψ : AddChar (Ad E) ℂ}
    {S : Finset (Pl E)} {U : Set (GA E k)} {φ : XB E k} {η : (Fin k → Ad E) → ℝ} {s : (Fin k → Ad E) → GA E k}
    (hcut : Cut ψ S U φ η s) (hinv : RatInv (φ : GA E k → ℂ)) (hdec : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * wt (k + 1) g) :
    ∃ a ε C : ℝ, 0 < ε ∧ ∀ g, ∑' ξ : RowT E k k, ‖fC η s φ (ratGL E k (gam ξ) * g)‖ₑ ^ 2 ≤
      ENNReal.ofReal (C * min (Dt g) (Dt g)⁻¹ ^ ε * Dt g ^ (-a)) := by
  obtain ⟨hdc, hdpos, -, hdrat, hdB, -⟩ := hK1 E k hk
  obtain ⟨Cs, hCs, -, hsC⟩ := hcut.small
  obtain ⟨B, hB1, hB⟩ := hdB ((fun x => x⁻¹) '' Cs) (hCs.image continuous_inv)
  obtain ⟨Cη, hCη⟩ := hcut.cont.bounded_above_of_compact_support hcut.cpt
  obtain ⟨Cφ, hCφ⟩ := hdec
  set T := tsupport η with hT
  have hTc : IsCompact T := hcut.cpt.isCompact
  obtain ⟨-, hG⟩ := hG5t E k hk T hTc
  obtain ⟨C₁, hC₁⟩ := hG k le_rfl
  obtain ⟨C₂, hC₂⟩ := hG (k + 1) (by omega)
  set A : ℝ := max Cη 0 * (max Cφ 0 * B ^ (k + 1)) with hA
  have hA0 : 0 ≤ A := mul_nonneg (le_max_right _ _) (mul_nonneg (le_max_right _ _) (by positivity))
  have hwt0 : ∀ M (g : GA E k), 0 ≤ wt M g := fun M g => pow_nonneg (le_min zero_le_one (hdpos g).le) _

  have hpt : ∀ h : GA E k, ‖fC η s φ h‖ ≤ A * wt (k + 1) h * T.indicator (fun _ => (1 : ℝ)) (lastRow h) := by
    intro h
    by_cases hT' : lastRow h ∈ T
    · rw [Set.indicator_of_mem hT', mul_one]
      by_cases h0 : η (lastRow h) = 0
      · rw [show fC η s φ h = 0 by simp [fC, h0], norm_zero]
        exact mul_nonneg hA0 (hwt0 _ _)
      have hsy := (hsC _ h0).1
      have hdm : dmin (h * (s (lastRow h))⁻¹) ≤ B * dmin h := hB _ ⟨_, hsy, rfl⟩ h
      have hw := sq_wt_le hB1 (hdpos _) hdm (k + 1)
      simp only [fC, norm_mul, Complex.norm_real]
      have e1 : ‖η (lastRow h)‖ ≤ max Cη 0 := (hCη _).trans (le_max_left _ _)
      have e2 : ‖φ (h * (s (lastRow h))⁻¹)‖ ≤ max Cφ 0 * (B ^ (k + 1) * wt (k + 1) h) := by
        refine (hCφ _).trans ?_
        have hw0 : 0 ≤ wt (k + 1) (h * (s (lastRow h))⁻¹) := by
          unfold wt; exact pow_nonneg (le_min zero_le_one (hdpos _).le) _
        calc Cφ * wt (k + 1) (h * (s (lastRow h))⁻¹) ≤ max Cφ 0 * wt (k + 1) (h * (s (lastRow h))⁻¹) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hw0
          _ ≤ max Cφ 0 * (B ^ (k + 1) * wt (k + 1) h) := mul_le_mul_of_nonneg_left hw (le_max_right _ _)
      calc ‖(η (lastRow h) : ℝ)‖ * ‖φ (h * (s (lastRow h))⁻¹)‖
          ≤ max Cη 0 * (max Cφ 0 * (B ^ (k + 1) * wt (k + 1) h)) :=
            mul_le_mul e1 e2 (norm_nonneg _) (le_max_right _ _)
        _ = A * wt (k + 1) h := by rw [hA]; ring
    · rw [Set.indicator_of_notMem hT', mul_zero]
      simp [fC, image_eq_zero_of_notMem_tsupport hT']
  have hwr : ∀ (M : ℕ) (ξ : RowT E k k) (g : GA E k), wt M (ratGL E k (gam ξ) * g) = wt M g := by
    intro M ξ g; simp only [wt, hdrat (gam ξ) g]

  have hsum : ∀ (a : ℕ) (Ca : ℝ), (∀ g : GA E k, (∑' ξ : RowT E k k,
        T.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g))) * ENNReal.ofReal (wt a g) ≤
        ENNReal.ofReal (Ca * Dt g ^ (-(a : ℝ) / k))) → ∀ g : GA E k, wt (k + 1) g ^ 2 ≤ wt a g →
      ∑' ξ : RowT E k k, ‖fC η s φ (ratGL E k (gam ξ) * g)‖ₑ ^ 2 ≤
        ENNReal.ofReal (A ^ 2 * (Ca * Dt g ^ (-(a : ℝ) / k))) := by
    intro a Ca hCa g hwa
    have hterm : ∀ ξ : RowT E k k, ‖fC η s φ (ratGL E k (gam ξ) * g)‖ₑ ^ 2 ≤ ENNReal.ofReal (A ^ 2) *
        (T.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) * ENNReal.ofReal (wt a g)) := by
      intro ξ
      have hp := hpt (ratGL E k (gam ξ) * g)
      rw [hwr] at hp
      by_cases hT' : lastRow (ratGL E k (gam ξ) * g) ∈ T
      · rw [Set.indicator_of_mem hT', one_mul, ← ENNReal.ofReal_mul (sq_nonneg _), ← ofReal_norm,
          ← ENNReal.ofReal_pow (norm_nonneg _)]
        rw [Set.indicator_of_mem hT', mul_one] at hp
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖fC η s φ (ratGL E k (gam ξ) * g)‖ ^ 2 ≤ (A * wt (k + 1) g) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hp 2
          _ = A ^ 2 * wt (k + 1) g ^ 2 := by ring
          _ ≤ A ^ 2 * wt a g := mul_le_mul_of_nonneg_left hwa (sq_nonneg _)
      · rw [Set.indicator_of_notMem hT', mul_zero] at hp
        have h0 : fC η s φ (ratGL E k (gam ξ) * g) = 0 := norm_le_zero_iff.1 hp
        simp [h0]
    calc ∑' ξ : RowT E k k, ‖fC η s φ (ratGL E k (gam ξ) * g)‖ₑ ^ 2
        ≤ ∑' ξ : RowT E k k, ENNReal.ofReal (A ^ 2) *
          (T.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) * ENNReal.ofReal (wt a g)) :=
          ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (A ^ 2) * ((∑' ξ : RowT E k k,
          T.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g))) * ENNReal.ofReal (wt a g)) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
      _ ≤ ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (Ca * Dt g ^ (-(a : ℝ) / k)) := by gcongr; exact hCa g
      _ = ENNReal.ofReal (A ^ 2 * (Ca * Dt g ^ (-(a : ℝ) / k))) := (ENNReal.ofReal_mul (sq_nonneg _)).symm
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set Cm : ℝ := max (max C₁ C₂) 0 with hCm
  refine ⟨1 + 1 / (2 * k), 1 / (2 * k), A ^ 2 * Cm, by positivity, fun g => ?_⟩
  have hD : 0 < Dt g := (hD0 E k).1 g
  have hm0 : 0 ≤ min 1 (dmin g) := le_min zero_le_one (hdpos g).le
  have hm1 : min 1 (dmin g) ≤ 1 := min_le_left _ _
  have hwa : ∀ a : ℕ, a ≤ k + 1 → wt (k + 1) g ^ 2 ≤ wt a g := by
    intro a ha
    simp only [wt, ← pow_mul]
    exact pow_le_pow_of_le_one hm0 hm1 (by omega)
  have key : ∀ c X : ℝ, 0 ≤ X → c ≤ Cm → A ^ 2 * (c * X) ≤ A ^ 2 * Cm * X := fun c X hX hc => by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hX) (sq_nonneg A)
  rcases le_total 1 (Dt g) with h1 | h1
  · have hmin : min (Dt g) (Dt g)⁻¹ = (Dt g)⁻¹ := min_eq_right ((inv_le_one_of_one_le₀ h1).trans h1)
    have hX : min (Dt g) (Dt g)⁻¹ ^ (1 / (2 * (k : ℝ))) * Dt g ^ (-(1 + 1 / (2 * (k : ℝ)))) =
        Dt g ^ (-((k + 1 : ℕ) : ℝ) / k) := by
      rw [hmin, Real.inv_rpow hD.le, ← Real.rpow_neg hD.le, ← Real.rpow_add hD]
      congr 1; push_cast; field_simp; ring
    refine (hsum (k + 1) C₂ hC₂ g (hwa _ le_rfl)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_assoc (A ^ 2 * Cm), hX]
    exact key _ _ (Real.rpow_nonneg hD.le _) ((le_max_right _ _).trans (le_max_left _ _))
  · have hmin : min (Dt g) (Dt g)⁻¹ = Dt g := min_eq_left (h1.trans (one_le_inv₀ hD |>.2 h1))
    have hX : min (Dt g) (Dt g)⁻¹ ^ (1 / (2 * (k : ℝ))) * Dt g ^ (-(1 + 1 / (2 * (k : ℝ)))) =
        Dt g ^ (-((k : ℕ) : ℝ) / k) := by
      rw [hmin, ← Real.rpow_add hD]
      congr 1; field_simp; ring
    refine (hsum k C₁ hC₁ g (hwa _ (by omega))).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_assoc (A ^ 2 * Cm), hX]
    exact key _ _ (Real.rpow_nonneg hD.le _) ((le_max_left _ _).trans (le_max_left _ _))

theorem pos_adele_ext {x y : Ad E} (h1 : pInf E x = pInf E y)
    (h2 : ∀ w : Pl E, pLoc E w (pFin E x) = pLoc E w (pFin E y)) : x = y := by
  refine Prod.ext ?_ ?_
  · exact (infEq E).symm.injective h1
  · exact Subtype.ext (funext fun w => h2 w)

theorem pos_one_map {R : Type} [CommRing R] (f : Ad E →+* R) (i c : Fin k) :
    f ((1 : Matrix (Fin k) (Fin k) (Ad E)) i c) = (1 : Matrix (Fin k) (Fin k) R) i c := by
  simp only [Matrix.one_apply]
  split_ifs <;> simp

theorem pos_mir {S : Finset (Pl E)} {g : GA E k} (hm : MirS S g) (hi : InS S g) : Mir (k - 1) g := by
  intro i c hic
  apply pos_adele_ext
  · have h := hm.1 i c hic
    rw [pos_one_map]
    exact h
  · intro w
    have e1 := pos_one_map ((pLoc E w).comp (pFin E)) i c
    simp only [RingHom.comp_apply] at e1
    rw [e1]
    by_cases hw : w ∈ S
    · exact hm.2 w hw i c hic
    · have h := hi w hw
      have h' : (cLoc w g).val i c = (1 : GL (Fin k) (w.adicCompletion E)).val i c := by rw [h]
      exact h'

theorem pos_PW (hP2 : P2) (hP3 : P3) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (φ φ' : XB E k)
    (η : (Fin k → Ad E) → ℝ) (s : (Fin k → Ad E) → GA E k) (g : GA E k) :
    PW ψ (fC η s φ) φ' g = (η (lastRow g) : ℂ) * Wh ψ φ (g * (s (lastRow g))⁻¹) * conj (Wh ψ φ' g) := by
  simp only [PW, whit_fC hP2 hP3 hψ]
  rfl

theorem pos_fC (hG0 : jumpWindows.G0) (hD0 : D0) (hP2 : P2) (hP3 : P3) (hC0 : C0) (hk : 1 ≤ k) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ)
    {S : Finset (Pl E)} {u : ℝ} {U U₀ : Set (GA E k)} {φ φ' : XB E k} {η : (Fin k → Ad E) → ℝ}
    {s : (Fin k → Ad E) → GA E k} (hcut : Cut ψ S U φ η s) (hgood : Good ψ (k - 1) φ) (hgood' : Good ψ (k - 1) φ')
    (hUU : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U₀)
    (hKU : ∀ c ∈ U₀, 1 / 2 ≤ Dt c ∧ Dt c ≤ 2 ∧ 0 < (conj (Wh ψ φ' c) * (Dt c : ℂ) ^ ((u : ℂ) * Complex.I)).re)
    (hbump : ∃ C, C ⊆ U ∧ (∀ c ∈ C, GlobalTheory (k - 1) c) ∧ Bump ψ S (fun g => InS S g ∧ Mir (k - 1) g) C (Wh ψ φ))
    (hsph : SphOff S (PW ψ (fC η s φ) φ')) :
    ∃ a b : ℝ, 0 < a ∧ ∀ g ∈ G0 S, PW ψ (fC η s φ) φ' g ≠ 0 →
      a ≤ Dt g ∧ Dt g ≤ b ∧ 0 ≤ (PW ψ (fC η s φ) φ' g * (Dt g : ℂ) ^ ((u : ℂ) * Complex.I)).re := by
  obtain ⟨-, hDmul, -, -, hDUU, -, -, -, -, -, hDκ⟩ := hD0 E k
  obtain ⟨hlaw, hpsN, hUU01, hwh, -, hgoodpre, hlr, -⟩ := hP2 E k ψ hψ
  have whlaw : ∀ φ : XB E k, Good ψ (k - 1) φ → ∀ n, UU 0 n → ∀ h, Wh ψ φ (n * h) = psN ψ n * Wh ψ φ h :=
    fun φ hg n hn h => hlaw 0 _ (hwh (k - 1) (by omega) _ (hgoodpre _ _ hg)) n (hUU01 n hn) h
  have hcj : ∀ n : GA E k, psN ψ n * conj (psN ψ n) = 1 := fun n => by
    rw [RCLike.mul_conj, hpsN n]; simp
  refine ⟨1 / 2, 2, by norm_num, fun g hg hne => ?_⟩
  obtain ⟨n, g₀, κ, hn, hg₀, hκ1, hκS, hκi, rfl⟩ := (hC0 E k S).2.2.2.1 g hg
  have hDg : Dt (n * g₀ * κ) = Dt g₀ := by
    rw [hDmul, hDmul, hDUU 0 n hn, hDκ κ hκ1 hκi]; ring
  have hPn : PW ψ (fC η s φ) φ' (n * g₀) = PW ψ (fC η s φ) φ' g₀ := by
    rw [pos_PW hP2 hP3 hψ, pos_PW hP2 hP3 hψ, hlr n g₀ hn, mul_assoc n g₀, whlaw φ hgood n hn,
      whlaw φ' hgood' n hn, map_mul]
    linear_combination (↑(η (lastRow g₀)) * Wh ψ φ (g₀ * (s (lastRow g₀))⁻¹) * conj (Wh ψ φ' g₀)) * hcj n
  rw [hsph _ κ hκ1 hκS hκi, hPn] at hne ⊢
  rw [hDg]
  set y := lastRow g₀ with hy
  set σ := s y with hσ
  have hPW := pos_PW hP2 hP3 hψ φ φ' η s g₀
  rw [← hy, ← hσ] at hPW
  rw [hPW] at hne ⊢
  have hη : η y ≠ 0 := fun h => hne (by rw [h]; simp)
  have hW : Wh ψ φ (g₀ * σ⁻¹) ≠ 0 := fun h => hne (by rw [h]; simp)
  obtain ⟨Cs, -, hCsU, hsm⟩ := hcut.small
  obtain ⟨hσC, hσS⟩ := hsm y hη
  have hmir := hcut.mir g₀ hg₀ hη
  rw [← hy, ← hσ] at hmir
  have hIn : InS S (g₀ * σ⁻¹) := fun w hw => by
    rw [map_mul, map_inv, hg₀ w hw, hσS w hw]; simp
  obtain ⟨C, hCU, -, -, -, -, hB⟩ := hbump
  obtain ⟨n', c, hc, t, hn', -, hgc, ht, hWt⟩ := hB _ ⟨hIn, pos_mir hmir hIn⟩ hW
  have hg₀' : g₀ = n' * (c * σ) := by rw [← mul_assoc]; exact mul_inv_eq_iff_eq_mul.mp hgc
  have hcs : c * σ ∈ U₀ := hUU c (hCU hc) σ (hCsU hσC)
  obtain ⟨h1, h2, h3⟩ := hKU _ hcs
  have hD : Dt g₀ = Dt (c * σ) := by rw [hg₀', hDmul, hDUU 0 n' hn', one_mul]
  refine ⟨hD ▸ h1, hD ▸ h2, ?_⟩
  have hW' : Wh ψ φ' g₀ = psN ψ n' * Wh ψ φ' (c * σ) := by rw [hg₀']; exact whlaw φ' hgood' n' hn' _
  have e : (η y : ℂ) * Wh ψ φ (g₀ * σ⁻¹) * conj (Wh ψ φ' g₀) * (Dt g₀ : ℂ) ^ ((u : ℂ) * Complex.I) =
      ((η y * t : ℝ) : ℂ) * (conj (Wh ψ φ' (c * σ)) * (Dt (c * σ) : ℂ) ^ ((u : ℂ) * Complex.I)) := by
    rw [hWt, hW', hD, map_mul]
    push_cast
    linear_combination (↑(η y) * ↑t * conj (Wh ψ φ' (c * σ)) * (Dt (c * σ) : ℂ) ^ ((u : ℂ) * Complex.I)) * hcj n'
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg (mul_nonneg (hcut.nonneg y) ht) h3.le

open scoped ValuativeRel

theorem law_memO {w : Pl E} (x : w.adicCompletion E) :
    x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Formalism.UG.Ov E w := by
  rw [Valuation.mem_integer_iff]
  change _ ↔ x ∈ w.adicCompletionIntegers E
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem law_lr (hk : 1 ≤ k) {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') (M : Matrix (Fin k) (Fin k) R) (c : Fin k) :
    σ (∑ i : Fin k, if (i : ℕ) + 1 = k then M i c else 0) = M.map σ ⟨k - 1, by omega⟩ c := by
  rw [map_sum, Finset.sum_eq_single (⟨k - 1, by omega⟩ : Fin k)]
  · rw [if_pos (by simp; omega)]; rfl
  · intro b _ hb; rw [if_neg, map_zero]
    intro h; exact hb (Fin.ext (by simp; omega))
  · simp

section Loc
variable {w : Pl E}

theorem law_row (hk : 1 ≤ k) {n κ : GL (Fin k) (w.adicCompletion E)} (hn : n ∈ Iwasawa.unipotent _ k)
    (l : Fin k → ℤ) (c : Fin k) :
    ((n * Iwasawa.torusPow (w.adicCompletion E) k l * κ : GL (Fin k) (w.adicCompletion E)) :
      Matrix (Fin k) (Fin k) (w.adicCompletion E)) ⟨k - 1, by omega⟩ c =
      (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ^ l ⟨k - 1, by omega⟩ * κ.val ⟨k - 1, by omega⟩ c := by
  rw [mul_assoc, Units.val_mul, Units.val_mul, Iwasawa.coe_torusPow, Matrix.mul_apply,
    Finset.sum_eq_single (⟨k - 1, by omega⟩ : Fin k)]
  · rw [(Iwasawa.mem_unipotent _ _).1 hn |>.2, one_mul, Matrix.diagonal_mul]
  · intro b _ hb
    rw [(Iwasawa.mem_unipotent _ _).1 hn |>.1, zero_mul]
    have := b.2
    exact Fin.lt_def.2 (by have : (b : ℕ) ≠ k - 1 := fun h => hb (Fin.ext h); simp; omega)
  · simp

end Loc

section Loc2
variable {w : Pl E}

theorem law_int (hk : 1 ≤ k) {κ : GL (Fin k) (w.adicCompletion E)} (hκ : κ ∈ GLnLocal.integralGL _ k)
    {m : ℤ} (hm : 0 ≤ m) (c : Fin k) :
    (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ^ m * κ.val ⟨k - 1, by omega⟩ c ∈
      𝒪[w.adicCompletion E] := by
  refine Subring.mul_mem _ ?_ (((GLnLocal.mem_integralGL_iff _ _).1 hκ).1 _ _)
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  rw [zpow_natCast]
  exact Subring.pow_mem _ (GLnLocal.uniformizer _).2 j

theorem law_nonneg (hk : 1 ≤ k) {κ : GL (Fin k) (w.adicCompletion E)} (hκ : κ ∈ GLnLocal.integralGL _ k)
    {m : ℤ} (h : ∀ c : Fin k, (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ^ m *
      κ.val ⟨k - 1, by omega⟩ c ∈ 𝒪[w.adicCompletion E]) : 0 ≤ m := by
  set π := (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E)
  set ℓ : Fin k := ⟨k - 1, by omega⟩
  have hsum : π ^ m = ∑ c, (π ^ m * κ.val ℓ c) * (κ⁻¹ : GL (Fin k) _).val c ℓ := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    have : ∑ c, κ.val ℓ c * (κ⁻¹ : GL (Fin k) _).val c ℓ = 1 := by
      rw [← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [this, mul_one]
  have h1 : π ^ m ∈ 𝒪[w.adicCompletion E] := by
    rw [hsum]
    exact Subring.sum_mem _ fun c _ => Subring.mul_mem _ (h c) (((GLnLocal.mem_integralGL_iff _ _).1 hκ).2 _ _)
  by_contra hneg
  have h2 : π ^ (-m) ∈ 𝒪[w.adicCompletion E] := by
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -m by omega)
    rw [hj, zpow_natCast]
    exact Subring.pow_mem _ (GLnLocal.uniformizer _).2 j
  have hπ : π ≠ 0 := fun h0 => (GLnLocal.irreducible_uniformizer (w.adicCompletion E)).ne_zero (Subtype.ext h0)
  have hprod : π ^ m * π ^ (-m) = 1 := by rw [← zpow_add₀ hπ, add_neg_cancel, zpow_zero]
  have v1 := (Valuation.mem_integer_iff _ _).1 h1
  have v2 := (Valuation.mem_integer_iff _ _).1 h2
  have hv : ValuativeRel.valuation (w.adicCompletion E) (π ^ m) = 1 := by
    refine le_antisymm v1 (not_lt.1 fun hlt => ?_)
    have := congrArg (ValuativeRel.valuation (w.adicCompletion E)) hprod
    rw [map_mul, map_one] at this
    have h3 : ValuativeRel.valuation (w.adicCompletion E) (π ^ m) * ValuativeRel.valuation (w.adicCompletion E) (π ^ (-m)) ≤
        ValuativeRel.valuation (w.adicCompletion E) (π ^ m) := by
      calc _ ≤ ValuativeRel.valuation (w.adicCompletion E) (π ^ m) * 1 := by gcongr
        _ = _ := mul_one _
    rw [this] at h3
    exact absurd (lt_of_le_of_lt h3 hlt) (lt_irrefl _)
  exact hneg (le_of_eq (Iwasawa.eq_zero_of_valuation_zpow_uniformizer_eq_one _ hv).symm)

end Loc2

theorem law_pad (l : Fin k → ℤ) : pad k l = l := by
  funext a; simp [pad, a.2]

theorem law_sph (hK8a : LocalHeckeAlgebra) (hk : 1 ≤ k) {S : Finset (Pl E)} (α α' : Off E S → Fin k → ℂˣ) (w : Off E S)
    {χ : AddChar (w.1.adicCompletion E) ℂ} (hχ : PositivityTheory.JacquetShalikaLocal.PsiOK χ)
    {n κ : GL (Fin k) (w.1.adicCompletion E)} (hn : n ∈ Iwasawa.unipotent _ k) (hκ : κ ∈ GLnLocal.integralGL _ k)
    (l : Fin k → ℤ) (hl : 0 ≤ l ⟨k - 1, by omega⟩) :
    sphericalWhittaker χ (α w) (n * Iwasawa.torusPow (w.1.adicCompletion E) k l * κ) *
      conj (sphericalWhittaker χ (α' w) (n * Iwasawa.torusPow (w.1.adicCompletion E) k l * κ)) = aLoc α α' w l := by
  have hK := (hK8a E S k k α α' w χ hχ hk le_rfl).2 l
  have key := hK.2.1 (Or.inr fun i hi => by
    have : i = ⟨k - 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [this]; exact hl)
  rw [law_pad] at key
  have e : ∀ z : Fin k → ℂˣ, sphericalWhittaker χ z (n * Iwasawa.torusPow (w.1.adicCompletion E) k l * κ) =
      Whittaker.psiN χ n * sphericalWhittaker χ z (Iwasawa.torusPow (w.1.adicCompletion E) k l) := by
    intro z
    rw [sphericalWhittaker_mul_right hχ.1 z _ hκ, sphericalWhittaker_mul_left hχ.1 z hn]
  rw [e, e, ← key, map_mul]
  have hn1 : Whittaker.psiN χ n * conj (Whittaker.psiN χ n) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Whittaker.psiN, hχ.2.2]; simp
  linear_combination (sphericalWhittaker χ (α w) (Iwasawa.torusPow (w.1.adicCompletion E) k l) *
    conj (sphericalWhittaker χ (α' w) (Iwasawa.torusPow (w.1.adicCompletion E) k l))) * hn1

theorem law_inf (hk : 1 ≤ k) (g : GA E k) (i : Fin k) : pInf E (lastRow g i) = (cInf g).val ⟨k - 1, by omega⟩ i :=
  law_lr hk (pInf E) g.val i

theorem law_loc (hk : 1 ≤ k) (v : Pl E) (g : GA E k) (i : Fin k) :
    pLoc E v (pFin E (lastRow g i)) = (cLoc v g).val ⟨k - 1, by omega⟩ i :=
  law_lr hk ((pLoc E v).comp (pFin E)) g.val i

theorem law_fC (hG0 : jumpWindows.G0) (hG5 : jumpWindows.G5) (hP2 : P2) (hP3 : P3) (hC0 : C0) (hK7 : K7) (hK8a : LocalHeckeAlgebra)
    (hk : 1 ≤ k) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)} (hS : ∀ w, w ∉ S → Cond ψ w)
    {α α' : Off E S → Fin k → ℂˣ} {U : Set (GA E k)} {φ φ' : XB E k} {η : (Fin k → Ad E) → ℝ}
    {s : (Fin k → Ad E) → GA E k} (hcut : Cut ψ S U φ η s) (hgood : Good ψ (k - 1) φ)
    (hsat : ∀ w : Off E S, SatFn w.1 (Finset.univ.val.map (α w)) φ) (hgood' : Good ψ (k - 1) φ')
    (hsat' : ∀ w : Off E S, SatFn w.1 (Finset.univ.val.map (α' w)) φ') :
    LawOff S (PW ψ (fC η s φ) φ') (aLoc α α') := by
  intro w g hg n hn κ hκ l
  have hG := hG0 E k
  have hwS : w.1 ∉ S := w.2
  obtain ⟨χ, hχ, -, hW⟩ := hK7 E k ψ hψ w.1 (hS w.1 hwS)
  set x := n * Iwasawa.torusPow (w.1.adicCompletion E) k l * κ with hx
  set g' := g * fl k w.1 x with hg'
  have hinf : cInf g' = cInf g := by rw [hg', map_mul, hG.2.2.1, mul_one]
  have hloc : ∀ v, v ≠ w.1 → cLoc v g' = cLoc v g := fun v hv => by
    rw [hg', map_mul, hG.2.2.2.2.1 w.1 v x hv, mul_one]
  have hlocw : cLoc w.1 g' = x := by rw [hg', map_mul, hg, one_mul, hG.2.2.2.1]
  have hyI : ∀ i, pInf E (lastRow g' i) = pInf E (lastRow g i) := fun i => by
    rw [law_inf hk, law_inf hk, hinf]
  have hyv : ∀ v, v ≠ w.1 → ∀ i, pLoc E v (pFin E (lastRow g' i)) = pLoc E v (pFin E (lastRow g i)) :=
    fun v hv i => by rw [law_loc hk, law_loc hk, hloc v hv]
  have hyS : ∀ v ∈ S, ∀ i, pLoc E v (pFin E (lastRow g' i)) = pLoc E v (pFin E (lastRow g i)) :=
    fun v hv => hyv v (fun h => hwS (h ▸ hv))
  have hyw : ∀ i, pLoc E w.1 (pFin E (lastRow g' i)) =
      (GLnLocal.uniformizer (w.1.adicCompletion E) : w.1.adicCompletion E) ^ l ⟨k - 1, by omega⟩ *
        κ.val ⟨k - 1, by omega⟩ i := fun i => by
    rw [law_loc hk, hlocw]; exact law_row hk hn l i
  have hyw1 : ∀ i, pLoc E w.1 (pFin E (lastRow g i)) ∈ Formalism.UG.Ov E w.1 := fun i => by
    rw [law_loc hk, hg, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have hdep := hcut.dep _ _ (fun i => (hyI i).symm) (fun v hv i => (hyS v hv i).symm)
  have hPW : ∀ h, PW ψ (fC η s φ) φ' h =
      (η (lastRow h) : ℂ) * Wh ψ φ (h * (s (lastRow h))⁻¹) * conj (Wh ψ φ' h) := fun h => by
    rw [PW, whit_fC hP2 hP3 hψ]; rfl
  have haL0 : ¬ 0 ≤ l ⟨k - 1, by omega⟩ → aLoc α α' w l = 0 := fun h =>
    ((hK8a E S k k α α' w χ hχ hk le_rfl).2 l).2.2 ⟨⟨k - 1, by omega⟩, by omega⟩
  by_cases hη' : η (lastRow g') = 0
  · rw [hPW g', hη', Complex.ofReal_zero, zero_mul, zero_mul]
    by_cases hη : η (lastRow g) = 0
    · rw [hPW g, hη, Complex.ofReal_zero, zero_mul, zero_mul, zero_mul]
    · have : ¬ 0 ≤ l ⟨k - 1, by omega⟩ := by
        intro hl
        refine hη ?_
        rw [← hdep.2 ?_ hη]
        · exact hη'
        intro v hv i
        by_cases hvw : v = w.1
        · subst hvw; rw [hyw]; exact (law_memO _).1 (law_int hk hκ hl i)
        · rw [hyv v hvw]; exact hcut.int _ hη v hv i
      rw [haL0 this, mul_zero]
  · have hl : 0 ≤ l ⟨k - 1, by omega⟩ :=
      law_nonneg hk hκ fun c => (law_memO _).2 (hyw c ▸ hcut.int _ hη' w.1 hwS c)
    have hdep' := hcut.dep _ _ hyI hyS
    have hηe : η (lastRow g) = η (lastRow g') := by
      refine hdep'.2 ?_ hη'
      intro v hv i
      by_cases hvw : v = w.1
      · subst hvw; exact hyw1 i
      · rw [← hyv v hvw]; exact hcut.int _ hη' v hv i
    obtain ⟨C, -, -, hC⟩ := hcut.small
    have hσ : InS S (s (lastRow g')) := (hC _ hη').2
    set σ := s (lastRow g') with hσdef
    have hσw : cLoc w.1 σ⁻¹ = 1 := by rw [map_inv, hσ w.1 hwS, inv_one]
    have hcomm := hG.2.2.2.2.2.2.2.1 w.1 σ⁻¹ hσw x
    have e1 : g' * σ⁻¹ = g * σ⁻¹ * fl k w.1 x := by rw [hg', mul_assoc, ← hcomm, mul_assoc]
    have hgσ : cLoc w.1 (g * σ⁻¹) = 1 := by rw [map_mul, hg, hσw, mul_one]
    have h1 := hW _ φ hgood (hsat w) _ hgσ x
    have h2 := hW _ φ' hgood' (hsat' w) g hg x
    have h3 := law_sph hK8a hk α α' w hχ hn hκ l hl
    rw [hPW g', hPW g, hdep.1, e1, h1, h2, hηe, map_mul]
    rw [← h3]
    ring

open scoped ValuativeRel

theorem sph_memO {w : Pl E} (x : w.adicCompletion E) :
    x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Formalism.UG.Ov E w := by
  rw [Valuation.mem_integer_iff]
  change _ ↔ x ∈ w.adicCompletionIntegers E
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem sph_lr (hk : 1 ≤ k) {R' : Type} [CommRing R'] (σ : Ad E →+* R') (g : GA E k) (c : Fin k) :
    σ (lastRow g c) = (g.val.map σ) ⟨k - 1, by omega⟩ c := by
  rw [lastRow, map_sum, Finset.sum_eq_single (⟨k - 1, by omega⟩ : Fin k)]
  · rw [if_pos (by simp; omega)]; rfl
  · intro b _ hb; rw [if_neg, map_zero]
    intro h; exact hb (Fin.ext (by simp; omega))
  · simp

theorem sph_rowint {w : Pl E} (r : Fin k → w.adicCompletion E) (hr : ∀ c, r c ∈ 𝒪[w.adicCompletion E])
    (M : Matrix (Fin k) (Fin k) (w.adicCompletion E)) (hM : ∀ i j, M i j ∈ 𝒪[w.adicCompletion E]) (c : Fin k) :
    (∑ j, r j * M j c) ∈ 𝒪[w.adicCompletion E] :=
  Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hr j) (hM j c)

theorem sph_fC (hG0 : jumpWindows.G0) (hP2 : P2) (hP3 : P3) (hK8 : K8) (hk : 1 ≤ k) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ)
    {S : Finset (Pl E)} (hS : ∀ w, w ∉ S → Cond ψ w)
    {α α' : Off E S → Fin k → ℂˣ} {U : Set (GA E k)} {φ φ' : XB E k} {η : (Fin k → Ad E) → ℝ}
    {s : (Fin k → Ad E) → GA E k} (hcut : Cut ψ S U φ η s) (hgood : Good ψ (k - 1) φ)
    (hsat : ∀ w : Off E S, SatFn w.1 (Finset.univ.val.map (α w)) φ) (hgood' : Good ψ (k - 1) φ')
    (hsat' : ∀ w : Off E S, SatFn w.1 (Finset.univ.val.map (α' w)) φ') :
    SphOff S (PW ψ (fC η s φ) φ') := by
  intro g κ hκi hκS hκint
  have hext := (hG0 E k).2.2.2.2.2.1
  have hW := (hK8 E k ψ hψ S hS α φ hgood hsat).2.1
  have hW' := (hK8 E k ψ hψ S hS α' φ' hgood' hsat').2.1
  set ℓ : Fin k := ⟨k - 1, by omega⟩
  set y := lastRow g
  set y' := lastRow (g * κ)
  have hinf : ∀ i, pInf E (y' i) = pInf E (y i) := by
    intro i
    rw [sph_lr hk (pInf E), sph_lr hk (pInf E)]
    have : (g * κ).val.map (pInf E) = g.val.map (pInf E) := by
      change (cInf (g * κ)).val = (cInf g).val
      rw [map_mul, hκi, mul_one]
    rw [this]
  have hloc : ∀ w, ∀ i, pLoc E w (pFin E (y' i)) = ∑ j, (cLoc w g).val ℓ j * (cLoc w κ).val j i := by
    intro w i
    have := sph_lr hk ((pLoc E w).comp (pFin E)) (g * κ) i
    simp only [RingHom.comp_apply] at this
    rw [this]
    change (cLoc w (g * κ)).val ℓ i = _
    rw [map_mul, Units.val_mul, Matrix.mul_apply]
  have hloc0 : ∀ w, ∀ i, pLoc E w (pFin E (y i)) = (cLoc w g).val ℓ i := by
    intro w i
    have := sph_lr hk ((pLoc E w).comp (pFin E)) g i
    simp only [RingHom.comp_apply] at this
    rw [this]; rfl
  have hS' : ∀ w ∈ S, ∀ i, pLoc E w (pFin E (y' i)) = pLoc E w (pFin E (y i)) := by
    intro w hw i
    rw [hloc, hloc0, hκS w hw]
    simp [Matrix.one_apply]
  have hint : (∀ w, w ∉ S → ∀ i, pLoc E w (pFin E (y i)) ∈ Formalism.UG.Ov E w) ↔
      (∀ w, w ∉ S → ∀ i, pLoc E w (pFin E (y' i)) ∈ Formalism.UG.Ov E w) := by
    have hK := fun w => (GLnLocal.mem_integralGL_iff _ _).1 (hκint w)
    constructor
    · intro h w hw i
      rw [hloc, ← sph_memO]
      exact sph_rowint _ (fun c => by rw [← hloc0, sph_memO]; exact h w hw c) _ (hK w).1 i
    · intro h w hw i
      have e : (cLoc w g).val ℓ i = ∑ j, (cLoc w (g * κ)).val ℓ j * (cLoc w κ)⁻¹.val j i := by
        rw [← Matrix.mul_apply, ← Units.val_mul, ← map_inv, ← map_mul, mul_inv_cancel_right]
      rw [hloc0, ← sph_memO, e]
      refine sph_rowint _ (fun c => ?_) _ (by simpa [map_inv] using (hK w).2) i
      have := h w hw c
      rw [hloc, ← sph_memO] at this
      rw [map_mul, Units.val_mul, Matrix.mul_apply]
      exact this
  have hsy : s y' = s y := (hcut.dep y' y hinf hS').1
  have hη : η y' = η y := by
    by_cases h : η y = 0
    · by_contra h'
      have h'' : η y' ≠ 0 := by rw [h] at h'; exact h'
      have := (hcut.dep y' y hinf hS').2 (hint.2 (hcut.int y' h'')) h''
      exact h'' (this.symm.trans h)
    · exact (hcut.dep y y' (fun i => (hinf i).symm) (fun w hw i => (hS' w hw i).symm)).2
        (hint.1 (hcut.int y h)) h
  rw [pos_PW hP2 hP3 hψ, pos_PW hP2 hP3 hψ]
  change (η y' : ℂ) * Wh ψ φ (g * κ * (s y')⁻¹) * conj (Wh ψ φ' (g * κ)) =
    (η y : ℂ) * Wh ψ φ (g * (s y)⁻¹) * conj (Wh ψ φ' g)
  rw [hη, hsy, hW' g κ hκi hκS hκint]
  by_cases h : η y = 0
  · simp [h]
  · have hIn := (hcut.small.choose_spec.2.2 y h).2
    have hc : κ * (s y)⁻¹ = (s y)⁻¹ * κ := by
      refine hext _ _ ?_ fun w => ?_
      · simp only [map_mul, hκi, one_mul, mul_one]
      · by_cases hw : w ∈ S
        · simp only [map_mul, hκS w hw, one_mul, mul_one]
        · simp only [map_mul, map_inv, hIn w hw, inv_one, one_mul, mul_one]
    rw [show g * κ * (s y)⁻¹ = g * (s y)⁻¹ * κ by rw [mul_assoc, hc, ← mul_assoc], hW _ κ hκi hκS hκint]

theorem pre_fC (hP2 : P2) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)} {U : Set (GA E k)}
    {φ : XB E k} {η : (Fin k → Ad E) → ℝ} {s : (Fin k → Ad E) → GA E k} (hcut : Cut ψ S U φ η s)
    (hinv : RatInv (φ : GA E k → ℂ)) : Pre ψ (k - 1) (fC η s φ) := by
  have hP := hP2 E k ψ hψ
  have hlc : Continuous (lastRow : GA E k → _) := hP.2.2.2.2.2.2.2.2.1
  have hlm := hP.2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · have e : fC η s φ = fun g => ((η (lastRow g) : ℂ) • Rt E k (s (lastRow g))⁻¹ φ) g := by
      funext g; simp [fC]
    rw [e]
    exact continuous_eval.comp ((hcut.contV.comp hlc).prodMk continuous_id)
  · intro γ hγ g
    simp only [fC, hlm γ g hγ, mul_assoc, hinv γ]
  · intro j hj y g
    have hE : IsEmpty (UnipotentBlockColumnIndex k j j) := ⟨fun t => by have := t.2.2.1; have := t.1.2.isLt; omega⟩
    have h1 : blkU y = 1 := by
      apply Units.ext
      change 1 + _ = 1
      simp [posM, Finset.univ_eq_empty]
    have h2 : dot (eLast k j) y = 0 := by simp [dot, Finset.univ_eq_empty]
    rw [h1, h2, one_mul, AddChar.map_zero_eq_one, one_mul]

theorem one_fC (hP2 : P2) (hP3 : P3) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)} {U : Set (GA E k)}
    {φ φ' : XB E k} {η : (Fin k → Ad E) → ℝ} {s : (Fin k → Ad E) → GA E k} (hcut : Cut ψ S U φ η s)
    (h1 : ∃ t : ℝ, 0 < t ∧ Wh ψ φ 1 = t) (h1' : Wh ψ φ' 1 = 1) : 0 < (PW ψ (fC η s φ) φ' 1).re := by
  obtain ⟨t, ht, h1⟩ := h1
  rw [pos_PW hP2 hP3 hψ, hcut.one.2, inv_one, one_mul, h1, h1']
  simp only [map_one, mul_one]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_pos hcut.one.1 ht

end PKEq1

theorem kernel_equality_first_of : jumpWindows.G0 → jumpWindows.G5 → D0 → N0 → P2 → P3 → C0 → RowsInCompactSet → K1 → K7 → K8 → LocalHeckeAlgebra → KU → KEq1 := by
  intro hG0 hG5 hD0 hN0 hP2 hP3 hC0 hG5t hK1 hK7 hK8 hK8a hKU
  intro E _ _ _ k hk ψ hψ S hS α α' u φ' hsec
  obtain ⟨U₀, hU₀, hKU'⟩ := hKU E k ψ hψ φ' u hsec.good hsec.one
  obtain ⟨U, hUo, hU1, hUU⟩ := exists_open_nhds_one_mul_subset hU₀
  refine ⟨U, hUo.mem_nhds hU1, fun φ hprep η s hcut => ?_⟩
  have hsph := PKEq1.sph_fC hG0 hP2 hP3 hK8 hk hψ hS hcut hprep.good hprep.sat hsec.good hsec.sat
  obtain ⟨C, hCU, hCb, hB⟩ := hprep.bump
  exact
    { pre := PKEq1.pre_fC hP2 hψ hcut hprep.inv
      supp := ⟨tsupport η, hcut.cpt.isCompact, fun g hg => subset_tsupport _ (fun h => hg (by simp [h]))⟩
      sq := PKEq1.sq_fC hD0 hP2 hG5t hK1 hk hcut hprep.inv hprep.dec
      good := hsec.good
      inv := hsec.inv
      dec := hsec.dec
      law := PKEq1.law_fC hG0 hG5 hP2 hP3 hC0 hK7 hK8a hk hψ hS hcut hprep.good hprep.sat hsec.good hsec.sat
      sph := hsph
      one := PKEq1.one_fC hP2 hP3 hψ hcut hB.2.2.1 hsec.one
      pos := PKEq1.pos_fC hG0 hD0 hP2 hP3 hC0 hk hψ hcut hprep.good hsec.good (fun a ha b hb => hUU (Set.mul_mem_mul ha hb)) hKU' ⟨C, hCU, hCb, hB⟩ hsph }

end PositivityTheory.AdelicQuotientData

end
