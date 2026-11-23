import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.FactorLeProductSeven

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem vBB_monomial_one {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}
    (nu : σ →₀ ℕ) :
    vBB (O := O) p (monomial nu (1 : KK O)) = (((padicValNat p (expFact nu) : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  unfold vBB
  rw [support_monomial, if_neg one_ne_zero, Finset.inf_singleton, coeff_monomial, if_pos rfl, valuation_one_eq_zero_alt, zero_add]

theorem monomial_mem_pol {Kf : Type} [Field Kf] {ι : Type} {n : ℕ} (d : ι → ℕ) (nu : ι × Fin n →₀ ℕ)
    (hnu : ∀ x, multideg nu x = d x) : (monomial nu (1 : Kf)) ∈ Pol Kf n d := by
  rw [Pol, mem_restrictSupport_iff]
  intro mo hmo
  have : mo = nu := by
    rw [Finset.mem_coe, mem_support_iff, coeff_monomial] at hmo
    by_contra h
    exact hmo (if_neg fun h' => h h'.symm)
  rw [this]
  exact hnu

theorem noAt (D : Formalism.BasicNotions.D7) (p : ℕ) [hpF : Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S : UniformizedDVR p O) (w : O) (hw2 : w ^ 2 = (p : O))
    (hDA : DigAbs p O) (Fr : Frames n' r) {J : ℕ} [NeZero J] (cP : ℕ) (Dt : SignedChainData p O r J) :
    NoAt (K := K) p O Fr cP Dt := by
  intro dNo ka rho e nu hrho hJ hnu
  have hp := hpF.out
  have : CharZero (KK O) := dvr_fraction_field_char_zero hp S
  obtain ⟨_, _, hJ3, hJ4⟩ := hJ
  obtain ⟨W, hW⟩ : ∃ W, W = algebraMap O (KK O) w := ⟨_, rfl⟩
  obtain ⟨n2, hn2⟩ : ∃ n2, n2 = padicValNat p (∏ x, (dNo x).factorial) := ⟨_, rfl⟩
  obtain ⟨vn, hvn⟩ : ∃ vn, vn = padicValNat p (expFact nu) := ⟨_, rfl⟩
  obtain ⟨Dno, hDno⟩ : ∃ Dno, Dno = DnoOf (K := K) p Dt.nL dNo := ⟨_, rfl⟩
  have hvW : ∀ n : ℕ, vK p (W ^ n) = (((n : ℚ) / 2 : ℚ) : WithTop ℚ) := fun n => by
    rw [hW]; exact vK_w_pow hp S w hw2 n
  have hWn0 : ∀ n : ℕ, W ^ n ≠ 0 := by
    intro n h
    have := hvW n
    rw [h, valuation_zero_alt] at this
    exact WithTop.top_ne_coe this
  have hpW : (p : KK O) = W ^ 2 := by rw [hW, ← map_pow, hw2, map_natCast]
  have hmon : (monomial nu (1 : KK O)) ∈ Pol (KK O) K dNo := monomial_mem_pol dNo nu hnu

  have hUpol : (W ^ vn)⁻¹ • (monomial nu (1 : KK O)) ∈ Pol (KK O) K dNo := Submodule.smul_mem _ _ hmon
  have hUBB : InBB (O := O) p ((W ^ vn)⁻¹ • (monomial nu (1 : KK O))) := by
    unfold InBB
    rw [vBB_smul _ (inv_ne_zero (hWn0 vn)), vK_inv _ _ (hvW vn), vBB_monomial_one, ← hvn, ← WithTop.coe_add]
    simp
  obtain ⟨hZ1, hZ2⟩ := hJ3 _ hUpol
  have hZBB := hZ2 hUBB
  rw [← hDno] at hZBB
  have hYint := coefGe_of_inBB S w hw2 dNo _ (Submodule.smul_mem _ ((p : KK O) ^ Dno) hZ1) hZBB
  rw [← hW, ← hn2] at hYint
  obtain ⟨cY, hcY⟩ : ∃ cY, cY = W ^ n2 * (p : KK O) ^ Dno * (W ^ vn)⁻¹ := ⟨_, rfl⟩
  have hY : cY • e (monomial nu 1) = W ^ n2 • (p : KK O) ^ Dno • e ((W ^ vn)⁻¹ • (monomial nu (1 : KK O))) := by
    rw [map_smul, smul_smul, smul_smul, hcY]
  rw [← hY] at hYint
  obtain ⟨Yy, hYy⟩ : ∃ Yy, Yy = cY • e (monomial nu 1) := ⟨_, rfl⟩
  rw [← hYy] at hYint
  have hYpol : Yy ∈ Pol (KK O) K dNo := by
    rw [hYy]
    exact Submodule.smul_mem _ _ (hJ3 _ hmon).1
  obtain ⟨lam, hlam1, hlam2⟩ := (hDA (TL J Dt.nL r × Fin K) (fun v => Fr.dist (segZ v.1.1) (posTL Fr v.1))
    (fun v => rho (v.1, Fin.natAdd r v.2)) (fun v => hrho _ _)).2 true cP
  have hlam3 : ∀ bn : TL J Dt.nL r × Fin K →₀ ℕ,
      geQ (vK p (binomCombF (K := KK O) lam bn - ((gamNo Fr p Dt.nL rho bn : ℚ) : KK O)⁻¹)) (cP : ℝ) := by
    intro bn
    have h := geQ_neg _ (hlam2 bn)
    rw [neg_sub, if_pos rfl] at h
    exact h
  refine ⟨diagK (fun bn => binomCombF (K := KK O) lam bn) Yy, cY, ⟨?_, diagK_mem_pol _ _ hYpol, ?_⟩, ?_, ?_⟩
  · intro bn
    rw [coeff_diagK]
    have := geQ_mul _ _ (geQ_binomCombF S lam bn) (hYint bn)
    rwa [add_zero] at this
  · intro j u hu
    rw [diagK_binomCombF]
    have h1 := (degree_truncation D (KK O) (TL J Dt.nL r) Dt.trueLet K (NSet Dt.nL j u) cP lam.support hlam1
      (fun m => algebraMap O (KK O) (lam m)) Yy).2
    have h2 : lam1S Dt.trueLet (NSet Dt.nL j u) Yy ≤ ((ka j u 0 : ℤ) : WithBot ℤ) := by
      rw [hYy]
      exact lowest_weight_le_of_isotypic D Dt.trueLet (NSet Dt.nL j u) (ka j u) _
        (Submodule.smul_mem _ _ (hJ4 (monomial nu 1) ⟨j, ⟨u, by omega⟩⟩))
    refine le_trans h1 (le_trans (add_le_add_left h2 _) ?_)
    rw [← WithBot.coe_add]
    push_cast
    exact le_rfl
  · refine ⟨(n2 : ℚ) / 2 + (Dno : ℚ) - (vn : ℚ) / 2, ?_, ?_⟩
    · rw [hcY, valuation_mul_alt, valuation_mul_alt, hvW, vK_inv _ _ (hvW vn), hpW, ← pow_mul, hvW, ← WithTop.coe_add,
        ← WithTop.coe_add]
      congr 1
      push_cast
      ring
    · rw [← hn2, ← hvn, ← hDno]
      push_cast
      exact le_rfl
  · rw [← hYy]
    intro bn
    rw [coeff_sub, coeff_diagK, coeff_diagK, ← sub_mul]
    have := geQ_mul _ _ (hlam3 bn) (hYint bn)
    rwa [add_zero] at this

end Formalism.MainNotions.Proposition5Numerics
