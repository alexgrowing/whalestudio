import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.UOfSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CharVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftExp
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExistsIdele
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpUnique

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd Matrix
open GlobalTheory.CuspRep (finId locGL finGL)

private theorem fin_scalar {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) x)) = GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))

private theorem hk_read (k N : ℕ) (hN1 : 1 ≤ N) (f : UpperHalfPlane → ℂ) (ω : HChar ℚ) (w : Pl ℚ) (hM : ¬ normV w ∣ N)
    (𝔪 : Ideal (𝓞 ℚ)) :
    Sd.hkCoef k (lev N) ω w (icoef f) 𝔪 = coef f (normV w * Ideal.absNorm 𝔪) + ((ω.val w : ℂˣ) : ℂ) * (normV w : ℂ) ^ (k - 1) *
      (if normV w ∣ Ideal.absNorm 𝔪 then coef f (Ideal.absNorm 𝔪 / normV w) else 0) := by
  obtain ⟨hp, hspan, hN, hlev⟩ := UpperTheory.V.Af.Nf.places w
  have hl : lev N w = 0 := hlev N hN1 hM
  have hchi : chiI ω (lev N) w.asIdeal = ((ω.val w : ℂˣ) : ℂ) := by
    unfold chiI
    rw [finprod_eq_single _ w]
    · rw [if_pos hl]
      have : ordI w w.asIdeal = 1 := by
        unfold ordI
        exact Associates.count_self w.associates_irreducible
      rw [this, pow_one]
    · intro v hv
      have : ordI v w.asIdeal = 0 := by
        unfold ordI
        refine Associates.count_eq_zero_of_ne v.associates_irreducible w.associates_irreducible ?_
        intro h
        exact hv (HeightOneSpectrum.ext (associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp h)))
      rw [this, pow_zero]
  have hdiv : coefDiv (icoef f) w.asIdeal 𝔪 =
      if normV w ∣ Ideal.absNorm 𝔪 then coef f (Ideal.absNorm 𝔪 / normV w) else 0 := by
    unfold coefDiv
    split_ifs with h1 h2 h2
    · have h3 := congrArg Ideal.absNorm h1.choose_spec
      rw [map_mul, hN] at h3
      unfold icoef
      congr 1
      exact (Nat.div_eq_of_eq_mul_right hp.pos h3).symm
    · exfalso
      obtain ⟨𝔫, h⟩ := h1
      exact h2 ⟨Ideal.absNorm 𝔫, by rw [h, map_mul, hN]⟩
    · exfalso
      obtain ⟨P, hP, hu, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp 𝔪 h2
      have hmem : ((normV w : ℕ) : 𝓞 ℚ) ∈ P := by
        have : ((normV w : ℕ) : ℤ) ∈ P.under ℤ := by
          rw [hu]; exact Ideal.mem_span_singleton_self _
        simpa using (Ideal.mem_comap.mp this)
      have hle : w.asIdeal ≤ P := by
        rw [hspan, Ideal.span_le, Set.singleton_subset_iff]; exact hmem
      have heq : w.asIdeal = P := w.isMaximal.eq_of_le hP.ne_top hle
      exact h1 (heq ▸ hd)
    · rfl
  unfold Sd.hkCoef
  rw [hchi, hdiv]
  unfold icoef
  rw [map_mul, hN]

private theorem norm_span (n : ℕ) : Ideal.absNorm (Ideal.span {(n : 𝓞 ℚ)}) = n := by
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  simp

theorem UpperTheory.V.Br.eigOf :
    UpperTheory.V.Br.EigOf := by
  intro k N hk1 hN χ ω hd f φ hL hφ w α β hM hS
  obtain ⟨hU, hZ⟩ := UpperTheory.V.Br.uOfSat ℚ w _ _ φ α β hS
  obtain ⟨hfin, hval⟩ := UpperTheory.V.Af.Nf.charVal N hN χ ω hd
  have hω := hval w hM
  have hl : lev N w = 0 := (UpperTheory.V.Af.Nf.places w).2.2.2 N hN hM
  have hq : (0 : ℝ) < normV w :=
    Nat.cast_pos.2 (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w))
  constructor
  · set lam : ℂ := (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) with hlam
    have hH : hk k w (lev N w) φ = lam • φ := by
      rw [hl]
      change (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) • Uop w (locSm ℚ w) 0 φ = _
      rw [hU, smul_smul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hq, hlam]
      congr 4
      ring
    have hE := UpperTheory.V.Af.Nf.liftExp k N hN f φ.1 hL
    obtain ⟨c₀', hE'⟩ := (UpperTheory.V.Sd.holHk ℚ k hk1 (lev N) ω hfin φ hφ w).2.2 _ _ hE
    obtain ⟨-, h0, -, hlin, -⟩ := UpperTheory.V.Sd.holLin ℚ k (lev N) ω
    have hE2 := hlin 0 φ.1 lam _ _ _ _ h0 hE
    rw [hH] at hE'
    rw [zero_add] at hE2
    intro n hn
    have hne : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
      intro h
      have := norm_span n
      rw [h, Ideal.absNorm_bot] at this
      omega
    have := (UpperTheory.V.Sd.expUnique ℚ _ k _ _ _ _ hE' hE2).2 _ hne
    rw [hk_read k N hN f ω w hM, hω] at this
    simpa only [Pi.add_apply, Pi.zero_apply, zero_add, Pi.smul_apply, smul_eq_mul, icoef, norm_span] using this
  · rw [← hω]
    have h2 : locSm ℚ w (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) φ = ((ω.val w : ℂˣ) : ℂ) • φ := by
      refine Subtype.ext (funext fun g => ?_)
      change φ.1 (g * finGL ℚ 2 (locGL ℚ 2 w _)) = _
      rw [fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent]
      rfl
    exact smul_left_injective ℂ hS.1 (hZ.symm.trans h2)
