import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexMulMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdResQZpow

open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.HL

namespace GlobalTheory.TypeUnifProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem valuation_natCast_prime_eq_one_of_ne_resChar {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {l : ℕ} (hl : l.Prime) (hne : l ≠ Loc.resChar p) : p.valuation F (l : F) = 1 := by
  rw [← map_natCast (algebraMap (𝓞 F) F) l, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem
  apply hne
  have : p.asIdeal.IsPrime := p.isPrime
  have hz : ((l : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hdvd : ringChar (𝓞 F ⧸ p.asIdeal) ∣ l := (ringChar.spec _ l).1 hz
  rcases (Nat.dvd_prime hl).1 hdvd with h | h
  · exfalso
    have h1 : ((1 : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := (ringChar.spec _ 1).2 (by rw [h])
    simp at h1
  · exact h.symm

private theorem vE_algebraMap_ιF_eq_neg_log_valuation {D : D7} (p : PlF D) (L : Loc.LocE (D.s.atP p).Fp (D.s.atP p).Ep)
    {ϖ : 𝒪[(D.s.atP p).Fp]} (hϖ : Irreducible ϖ) {x : D.host.F} (hx : x ≠ 0) :
    vE L ϖ (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF x)) =
      -WithZero.log (p.valuation D.host.F x) := by
  have := (D.s.atP p).lf
  refine GlobalTheory.ResProd.vE_eq_neg_log p L (D.s.atP p).ιF (D.s.atP p).dense ?_ hϖ hx
  intro a b
  rw [← Valuation.Compatible.vle_iff_le]
  exact (D.s.atP p).val a b

private theorem exists_theta_eq_ιF_valuation_eq_g_mul {D : D7} (Z : LocDat D) (p : PlF D) :
    ∃ t : D.host.F, t ≠ 0 ∧ LocNG.theta (Z.M p) = (D.s.atP p).ιF t ∧
      p.valuation D.host.F t = p.valuation D.host.F ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) := by
  obtain ⟨-, -, -, -, -, hsp⟩ := Z.agree p
  have hss := D.s_split p
  have hg0 := D.host.g_prime 0
  have hg1 := D.host.g_prime 1
  have hgne := D.host.g_ne
  unfold LocNG.theta
  cases hM : (Z.M p).split with
  | none =>
    cases hS : (D.s.atP p).split with
    | none =>
      rw [hS] at hss
      have h0 : D.host.g 0 ≠ Loc.resChar p := fun h => by simp [h] at hss
      have h1 : D.host.g 1 ≠ Loc.resChar p := fun h => by simp [h] at hss
      refine ⟨1, one_ne_zero, (map_one _).symm, ?_⟩
      push_cast
      rw [map_mul, valuation_natCast_prime_eq_one_of_ne_resChar p hg0 h0, valuation_natCast_prime_eq_one_of_ne_resChar p hg1 h1, map_one, mul_one]
    | some sg =>
      rw [hM, hS] at hsp
      exact (hsp : False).elim
  | some g =>
    cases hS : (D.s.atP p).split with
    | none =>
      rw [hM, hS] at hsp
      exact (hsp : False).elim
    | some sg =>
      rw [hM, hS] at hsp
      obtain ⟨-, hq⟩ := hsp
      have hl : (Loc.resChar p).Prime := (D.s.atP p).ellPrime.out
      have hmem : Loc.resChar p = D.host.g 0 ∨ Loc.resChar p = D.host.g 1 := by
        have := hss.1 (by rw [hS]; rfl)
        simpa using this
      refine ⟨(Loc.resChar p : D.host.F), Nat.cast_ne_zero.2 hl.ne_zero, ?_, ?_⟩
      · change ((g.q : (D.s.atP p).Fp)) = _
        rw [hq, sg.q_eq, map_natCast]
      · push_cast
        rw [map_mul]
        rcases hmem with h | h
        · rw [valuation_natCast_prime_eq_one_of_ne_resChar p hg1 (by rw [h]; exact hgne.symm), mul_one, h]
        · rw [valuation_natCast_prime_eq_one_of_ne_resChar p hg0 (by rw [h]; exact hgne), one_mul, h]

theorem modK_theta {D : D7} (Z : LocDat D) (p : PlF D) {ϖ : 𝒪[(D.s.atP p).Fp]} (hϖ : Irreducible ϖ) :
    (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) = (resQ ϖ : ℝ) ^
      (-(2 * vE (Z.M p).L ϖ (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))))) := by
  obtain ⟨hOK, -⟩ := Z.agree p
  obtain ⟨t, ht, hθ, hv⟩ := exists_theta_eq_ιF_valuation_eq_g_mul Z p
  have hx : ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  rw [hθ, (GlobalTheory.BaseModule.modK_algebraMap (Z.M p) hOK ϖ hϖ).2 _ ((map_ne_zero _).2 ht),
    vE_algebraMap_ιF_eq_neg_log_valuation p _ hϖ ht, vE_algebraMap_ιF_eq_neg_log_valuation p _ hϖ hx, hv]

noncomputable def placesOf {D : D7} (Z : LocDat D) : Places D.host.F D.host.E D.conjF where
  quad := D.sp.cm.deg2
  loc := D.s.atP
  L := fun p => (Z.M p).L
  L_cj := Z.hcj

theorem card_infinite (D : D7) :
    Fintype.card (InfinitePlace D.host.E) = Module.finrank ℚ D.host.F := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have : IsTotallyComplex D.host.E := IsCMField.to_isTotallyComplex
  have h1 := IsTotallyComplex.finrank (K := D.host.E)
  have h2 := D.sp.cm.deg2
  have h3 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  rw [h2] at h3
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  omega

theorem main : ∀ (D : D7) (Z : LocDat D), (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p)))).Finite ∧ ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) = (((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹ := by
  intro D Z
  have hex : ∀ p : PlF D, ∃ ϖ : 𝒪[(D.s.atP p).Fp], Irreducible ϖ := fun p => by
    have := (D.s.atP p).lf
    exact IsDiscreteValuationRing.exists_irreducible _
  choose ϖ hϖ using hex
  have hx : ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  obtain ⟨hfin, hprod⟩ := GlobalTheory.ResProd.prod_resQ_zpow (placesOf Z) ϖ hϖ _ hx
  have hfin' : {p : PlF D | vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
      ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))) ≠ 0}.Finite := hfin
  have hprod' : ∏ᶠ p : PlF D, (resQ (ϖ p) : ℝ) ^ vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp
      (D.s.atP p).Ep ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))) =
      |((Algebra.norm ℚ ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) : ℚ) : ℝ)| := hprod
  have hterm : ∀ p : PlF D, (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) =
      (((resQ (ϖ p) : ℝ) ^ vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)))) ^ 2)⁻¹ := by
    intro p
    rw [modK_theta Z p (hϖ p), zpow_neg, mul_comm, zpow_mul]
    norm_cast
  have hsub : (Function.mulSupport fun p : PlF D => (resQ (ϖ p) : ℝ) ^ vE (Z.M p).L (ϖ p)
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)))) ⊆
      {p : PlF D | vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))) ≠ 0} := by
    intro p hp
    simp only [Function.mem_mulSupport, ne_eq, Set.mem_ofPred_eq] at hp ⊢
    intro h0
    apply hp
    rw [h0, zpow_zero]
  have hfs := hfin'.subset hsub
  simp_rw [hterm]
  refine ⟨hfs.subset ?_, ?_⟩
  · intro p hp
    simp only [Function.mem_mulSupport, ne_eq] at hp ⊢
    intro h1
    apply hp
    rw [h1, one_pow, inv_one]
  · have hn : Algebra.norm ℚ ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) =
        ((D.host.g 0 * D.host.g 1 : ℕ) : ℚ) ^ Module.finrank ℚ D.host.F := by
      rw [← map_natCast (algebraMap ℚ D.host.F), Algebra.norm_algebraMap]
    rw [finprod_inv_distrib, ← finprod_pow hfs, hprod', card_infinite D, hn]
    push_cast
    rw [abs_of_nonneg (by positivity), ← pow_mul]
    ring

end GlobalTheory.TypeUnifProd
