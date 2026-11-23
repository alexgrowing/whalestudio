import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.BlockValue
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Top

open MvPolynomial Finset

noncomputable section

theorem tri_add (r a : ℕ) :
    (r + a) * (r + a - 1) / 2 = r * (r - 1) / 2 + a * (a - 1) / 2 + r * a := by
  have h1 : (r + a) * (r + a - 1) = r * (r - 1) + a * (a - 1) + 2 * (r * a) := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; simp
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [show r' + 1 + (a' + 1) - 1 = r' + a' + 1 by omega, Nat.add_sub_cancel, Nat.add_sub_cancel]
    ring
  obtain ⟨x, hx⟩ := Nat.even_mul_pred_self r
  obtain ⟨y, hy⟩ := Nat.even_mul_pred_self a
  generalize r * (r - 1) = A at h1 hx ⊢
  generalize a * (a - 1) = B at h1 hy ⊢
  generalize r * a = P at h1 ⊢
  generalize (r + a) * (r + a - 1) = T at h1 ⊢
  omega

theorem isHomogeneous_yRoot (f r a : ℕ) (c : SmallBlock) (τ : Fin f) (i : Fin r) :
    (yRoot f r a c τ i).IsHomogeneous 1 := by
  have := (isHomogeneous_C (Fin f × Fin (r + a)) c.sign).mul (isHomogeneous_X ℚ (yIndex f r a c τ i))
  simpa [yRoot] using this

theorem isHomogeneous_zRoot (f r a : ℕ) (c : SmallBlock) (τ : Fin f) (i : Fin a) :
    (zRoot f r a c τ i).IsHomogeneous 1 :=
  isHomogeneous_X ℚ _

theorem isHomogeneous_smallBlockMu (f r a : ℕ) (c : SmallBlock) :
    (smallBlockMu f r a c).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_yRoot f r a c τ i

theorem isHomogeneous_smallPowerSum (f r a : ℕ) (c : SmallBlock) (k : ℕ) (τ : Fin f) :
    (smallPowerSum f r a c k τ).IsHomogeneous k := by
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  simpa using (isHomogeneous_yRoot f r a c τ i).pow k

theorem isHomogeneous_fibreClass (hV : VandermondeOfHomogeneous.Statement) (f r a : ℕ)
    (c : SmallBlock) :
    (fibreClass f r a c).IsHomogeneous (f * (r * (r - 1) / 2 + a * (a - 1) / 2)) := by
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin f))
    (fun τ => vandermondeOf (yRoot f r a c τ) * vandermondeOf (zRoot f r a c τ))
    (fun _ => r * (r - 1) / 2 + a * (a - 1) / 2)
    (fun τ _ => (hV _ ℚ r _ (isHomogeneous_yRoot f r a c τ)).mul
      (hV _ ℚ a _ (isHomogeneous_zRoot f r a c τ)))
  simpa [fibreClass, Finset.sum_const, Finset.card_univ, Fintype.card_fin] using h

theorem isHomogeneous_mu_pow_fib (hV : VandermondeOfHomogeneous.Statement) (f r a : ℕ)
    (c : SmallBlock) :
    (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c).IsHomogeneous
      (topDegree f (r + a)) := by
  have h := ((isHomogeneous_smallBlockMu f r a c).pow (f * (r * a))).mul
    (isHomogeneous_fibreClass hV f r a c)
  convert h using 1
  rw [topDegree, tri_add]
  ring

theorem multinomial_const (f x : ℕ) :
    (Nat.multinomial Finset.univ (fun _ : Fin f => x) : ℚ) =
      ((f * x).factorial : ℚ) / (x.factorial : ℚ) ^ f := by
  have h := Nat.multinomial_spec (Finset.univ : Finset (Fin f)) (fun _ => x)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.sum_const,
    smul_eq_mul] at h
  have hx : (x.factorial : ℚ) ^ f ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero x)
  rw [eq_div_iff hx, mul_comm]
  exact_mod_cast h

theorem blockCoeff_rect_eq (hCI : CharacterAtIdentity.Statement) (r a : ℕ) (hra : r * a ≠ 0) :
    blockCoeff 0 (r * a) (rectangle r a) = numStandardTable (rectangle r a) := by
  rw [blockCoeff, if_pos rfl, if_neg hra]
  have h := hCI r (rectangle r a) (fun _ _ _ => le_rfl)
  have hs : ∑ i, rectangle r a i = r * a := by
    simp [rectangle, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [hs] at h
  exact h

theorem kappa_ne_zero {r a : ℕ} {κ : ℚ}
    (h : κ = (r.factorial : ℚ) * a.factorial ∨ κ = -((r.factorial : ℚ) * a.factorial)) : κ ≠ 0 := by
  have : ((r.factorial : ℚ) * a.factorial) ≠ 0 := by positivity
  rcases h with h | h <;> rw [h]
  · exact this
  · exact neg_ne_zero.mpr this

theorem fibreDegree_eq (hF : FrobeniusCharacterFormula.Statement) (hCI : CharacterAtIdentity.Statement)
    (hV : VandermondeOfHomogeneous.Statement) (f r a : ℕ) (c : SmallBlock) (hr : 1 ≤ r)
    (ha : 1 ≤ a) (κ : ℚ)
    (hκ : ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam))
    (c0 : ℚ)
    (hInt : ∀ H : RootRing f (r + a), H.IsHomogeneous (topDegree f (r + a)) →
      algebraMap ℚ (FractionRing (RootRing f (r + a))) (flagIntegral f (r + a) H) =
        algebraMap ℚ (FractionRing (RootRing f (r + a))) c0 * dividedDifference f (r + a) H) :
    fibreDegree f r a c =
      c0 * κ ^ f * (f * (r * a)).factorial / ((r * a).factorial : ℚ) ^ f *
        (numStandardTable (rectangle r a) : ℚ) ^ f := by
  have hra : r * a ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hH : gmf f r a c 0 (f * (r * a)) =
      smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c := by
    simp [gmf, extraFactor]
  have hdd := dividedDifference_eq_of_hasDD (hasDD_gmf hF f r a c κ hκ 0 (f * (r * a)))
  rw [hH, gmfOut_zero] at hdd
  have h := hInt _ (isHomogeneous_mu_pow_fib hV f r a c)
  rw [hdd, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply ℚ (RootRing f (r + a)) (FractionRing (RootRing f (r + a))),
    ← map_mul] at h
  have h2 := (algebraMap ℚ (FractionRing (RootRing f (r + a)))).injective h
  rw [fibreDegree, h2, multinomial_const, blockCoeff_rect_eq hCI r a hra]
  have hx : ((r * a).factorial : ℚ) ^ f ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero _)
  field_simp
  ring

theorem extraFactor_zero (r : ℕ) : extraFactor r 0 = 1 := by simp [extraFactor]

theorem smallPowerSum_mul_restPolynomial (f r a : ℕ) (c : SmallBlock) (k : ℕ) (hk : 2 ≤ k)
    (τ : Fin f) :
    smallPowerSum f r a c (k - 1) τ * restPolynomial f r a c =
      gmf f r a c (fun σ => if σ = τ then k - 1 else 0) (f * (r * a) + 1) := by
  rw [gmf, restPolynomial]
  have : ∏ σ, blockEmb f (r + a) σ
      (yEval r a c (extraFactor r (if σ = τ then k - 1 else 0))) =
      smallPowerSum f r a c (k - 1) τ := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
    rw [Finset.prod_eq_one (fun σ hσ => by
      rw [if_neg (Finset.ne_of_mem_erase hσ), extraFactor_zero, map_one, map_one])]
    rw [if_pos rfl, extraFactor, if_neg (by omega), blockEmb_yEval_psum, mul_one]
  rw [this]
  ring

theorem sum_erase_const (f : ℕ) (τ : Fin f) (x : ℕ) :
    ∑ _σ ∈ Finset.univ.erase τ, x = (f - 1) * x := by
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

end

end Top

open Top MvPolynomial Finset

noncomputable section

theorem SameFactorFormula.proof (hA : LemmaA.Statement) (hB : LemmaB.Statement)
    (hF : FrobeniusCharacterFormula.Statement) (hCI : CharacterAtIdentity.Statement)
    (hV : VandermondeOfHomogeneous.Statement) (hRP : RectangleTablePos.Statement) :
    SameFactorFormula.Statement := by
  intro f r a c hf hr ha
  obtain ⟨κ, hκpm, hκ⟩ := hasDD_schur hB r a c
  obtain ⟨c0, hc0, hInt, hMain⟩ := hA f (r + a)
  have hκ0 := kappa_ne_zero hκpm
  have hra : r * a ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hfR : (numStandardTable (rectangle r a) : ℚ) ≠ 0 := by exact_mod_cast (hRP r a).ne'
  refine ⟨c0 * κ ^ f, mul_ne_zero hc0 (pow_ne_zero _ hκ0),
    fibreDegree_eq hF hCI hV f r a c hr ha κ hκ c0 hInt, ?_⟩
  intro Q hQ k hk2 hkN τ
  set q : Fin f → ℕ := fun σ => if σ = τ then k - 1 else 0 with hqdef
  have hGF := smallPowerSum_mul_restPolynomial f r a c k hk2 τ
  obtain ⟨P, hP, -, S', hS', hI⟩ := hMain _ Q hQ k (by omega) hkN τ _
    (by simpa using isHomogeneous_smallPowerSum f r a c (k - 1) τ)
  have hPeq : P = gmfOut f r a c κ q (f * (r * a) + 1) := by
    apply IsFractionRing.injective (RootRing f (r + a)) (FractionRing (RootRing f (r + a)))
    rw [hP, hGF, dividedDifference_eq_of_hasDD (hasDD_gmf hF f r a c κ hκ q _)]
  have hsum : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') = (f - 1) * (r * a) := by
    rw [← sum_erase_const f τ (r * a)]
    exact Finset.sum_congr rfl fun σ hσ => by simp [hqdef, Finset.ne_of_mem_erase hσ]
  have hle : (f - 1) * (r * a) ≤ f * (r * a) + 1 :=
    (Nat.mul_le_mul_right _ (Nat.sub_le f 1)).trans (Nat.le_succ _)
  have hres := restrict_gmfOut f r a c κ q (f * (r * a) + 1) τ
    (fun σ hσ => by simp [hqdef, hσ]) (by rw [hsum]; exact hle)
  have hmτ : mstar f r a q (f * (r * a) + 1) τ τ = r * a + 1 := by
    simp only [mstar, if_true, hsum]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [Nat.add_sub_cancel, add_mul, one_mul]
    omega
  have hms : mstar f r a q (f * (r * a) + 1) τ = fun σ => if σ = τ then r * a + 1 else r * a := by
    funext σ
    by_cases hσ : σ = τ
    · subst hσ; rw [hmτ, if_pos rfl]
    · simp [mstar, hσ, hqdef]
  have hqτ : q τ = k - 1 := by simp [hqdef]
  rw [hmτ, hqτ, toN_blockOut r a c κ (k - 1) (r * a + 1) k (by omega)] at hres
  have hprod : ∏ σ ∈ Finset.univ.erase τ,
      (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ) =
      ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 1) := by
    rw [Finset.prod_congr rfl fun σ hσ => by
      rw [show q σ = 0 by simp [hqdef, Finset.ne_of_mem_erase hσ], Nat.sub_zero,
        blockCoeff_rect_eq hCI r a hra]]
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ,
      Fintype.card_fin]
  have hmult : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) =
      ((f * (r * a) + 1).factorial : ℚ) /
        (((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f - 1)) := by
    have hp : ∏ σ, (mstar f r a q (f * (r * a) + 1) τ σ).factorial =
        (r * a + 1).factorial * (r * a).factorial ^ (f - 1) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), hmτ]
      congr 1
      rw [Finset.prod_congr rfl (fun σ hσ =>
        show (mstar f r a q (f * (r * a) + 1) τ σ).factorial = (r * a).factorial by
          simp only [hms, if_neg (Finset.ne_of_mem_erase hσ)]), Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ, Fintype.card_fin]
    have hs' := (Finset.mem_piAntidiag.mp
      (mstar_mem f r a q (f * (r * a) + 1) τ (by rw [hsum]; exact hle))).1
    have h := Nat.multinomial_spec (Finset.univ : Finset (Fin f))
      (mstar f r a q (f * (r * a) + 1) τ)
    rw [hp, hs'] at h
    have hden : ((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f - 1) ≠ 0 := by positivity
    rw [eq_div_iff hden, ← h]
    push_cast
    ring
  set K : ℚ := (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) *
    ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 1) * κ with hK
  have hmultpos : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  have hK0 : K ≠ 0 := by
    rw [hK]; exact mul_ne_zero (mul_ne_zero hmultpos (pow_ne_zero _ (mul_ne_zero hfR hκ0))) hκ0
  set T := ∑ nu ∈ partitionsOf r k,
      C (symmetricGroupCharacter (fun i => a + nu i) ((k - 1) :: List.replicate (r * a + 1) 1)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) with hT
  have hTeq : ∑ nu ∈ partitionsOf r k, C (blockCoeff (k - 1) (r * a + 1) (fun i => a + nu i)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) = T := by
    rw [hT]
    refine Finset.sum_congr rfl fun nu _ => ?_
    rw [blockCoeff, if_neg (by omega)]
  rw [hTeq, hprod] at hres
  have hPS : powerSumHom (r + a) S' = K • T := by
    rw [hS', hPeq, hres, hK, smul_eq_C_mul, smul_eq_C_mul]
    simp only [map_mul, map_pow]
    ring
  refine ⟨K⁻¹ • S', ?_, ?_⟩
  · rw [map_smul, hPS, smul_smul, inv_mul_cancel₀ hK0, one_smul]
  · rw [restTerm, hI, coeff_smul, smul_eq_mul]
    rw [hK, hmult]
    have hden : ((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f - 1) ≠ 0 := by positivity
    have hnum : ((f * (r * a) + 1).factorial : ℚ) ≠ 0 := by positivity
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hden ⊢
    field_simp
    ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
