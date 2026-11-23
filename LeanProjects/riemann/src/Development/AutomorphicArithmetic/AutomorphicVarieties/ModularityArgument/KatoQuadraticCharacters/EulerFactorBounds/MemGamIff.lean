import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCycZ
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.EvalSmulCong
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem gam_mono {M M' : ℕ} (h : M ∣ M') : CongruenceSubgroup.Gamma M' ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨a, b, c, d⟩ := hγ
  have e := fun (x : ℤ) (y : ZMod M') (hh : (x : ZMod M') = y) => congrArg (ZMod.castHom h (ZMod M)) hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_intCast, map_one] using e _ _ a
  · simpa only [map_intCast, map_zero] using e _ _ b
  · simpa only [map_intCast, map_zero] using e _ _ c
  · simpa only [map_intCast, map_one] using e _ _ d

private theorem gam_le {M N l : ℕ} (hN : N ∣ M) (hl : l ∣ M) : CongruenceSubgroup.Gamma M ≤ Gam N l := by
  intro γ hγ
  have h1 := gam_mono hN hγ
  have h2 := gam_mono hl hγ
  rw [CongruenceSubgroup.Gamma_mem] at h1 h2
  refine ⟨?_, ?_⟩
  · exact (CongruenceSubgroup.Gamma1_mem _ _).2 ⟨h1.1, h1.2.2.2, h1.2.2.1⟩
  · exact CongruenceSubgroup.Gamma0_mem.2 h2.2.2.1

private theorem mem_gam_iff (M : ℕ) (a b : SL(2, ℤ)) : a * b⁻¹ ∈ CongruenceSubgroup.Gamma M ↔
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) a = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) b := by
  rw [CongruenceSubgroup.Gamma_mem', map_mul, map_inv, mul_inv_eq_one]

private theorem map_liftSL (M : ℕ) (γ : SL(2, ZMod M)) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (liftSL M γ) = γ :=
  Classical.epsilon_spec (GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) M γ)

private theorem isTr_img {M N l : ℕ} [NeZero M] (hN : N ∣ M) (hl : l ∣ M) :
    IsTr (CongruenceSubgroup.Gamma M) (Gam N l) (fun γ : {γ // γ ∈ img (Gam N l) M} => liftSL M γ.1) := by
  refine ⟨fun γ => ?_, fun δ hδ => ?_⟩
  · obtain ⟨δ, hδ, e⟩ := (Finset.mem_filter.1 γ.2).2
    have h1 : liftSL M γ.1 * δ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      rw [mem_gam_iff, map_liftSL, e]
    have h2 := mul_mem (gam_le hN hl h1) hδ
    simpa using h2
  · refine ⟨⟨Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) δ,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, δ, hδ, rfl⟩⟩, ?_, fun γ hγ => ?_⟩
    · show _ ∈ _
      rw [mem_gam_iff, map_liftSL]
    · have h1 : δ * (liftSL M γ.1)⁻¹ ∈ CongruenceSubgroup.Gamma M := hγ
      rw [mem_gam_iff, map_liftSL] at h1
      exact Subtype.ext h1.symm

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem recip_mod [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) {σ : Ω ≃ₐ[ℚ] Ω} (hσ : σ ∈ fixMu Ω M)
    (f : X.K) (h : SL(2, ℤ)) : ∃ δ ∈ CongruenceSubgroup.Gamma M,
      X.gal σ (X.sl (ofSL (δ * h)) f) = X.sl (ofSL h) (X.gal σ f) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨M0, hM0, hf⟩ := X.level f
  have hM' : M0 * M ≠ 0 := mul_ne_zero hM0.ne' hM
  haveI : NeZero (M0 * M) := ⟨hM'⟩
  have hζ := isPrimitiveRoot_eOm ε hM'
  set ζ := eOm ε (1 / ((M0 * M : ℕ) : ℚ)) with hζd
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ⁻¹ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hmod : ∀ a b : ℕ, ζ ^ a = ζ ^ b → a ≡ b [MOD M0 * M] := fun a b hab => by
    rw [hζ.eq_orderOf]
    exact (hζ.isOfFinOrder hM').pow_eq_pow_iff_modEq.1 hab
  have hij : (i : ZMod (M0 * M)) * j = 1 := by
    have : ζ ^ (i * j) = ζ ^ 1 := by
      rw [pow_mul, hi, ← map_pow, hj, pow_one, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 (hmod _ _ this)
    simpa using h2
  have hi1 : (i : ZMod M) = 1 := by
    have h1 : σ (ζ ^ M0) = ζ ^ M0 := (mem_fixMu_iff σ).1 hσ _ (by rw [← pow_mul, hζ.pow_eq_one])
    have : ζ ^ (M0 * i) = ζ ^ (M0 * 1) := by
      rw [mul_one, mul_comm, pow_mul, hi, ← map_pow, h1]
    have h2 := Nat.ModEq.mul_left_cancel' hM0.ne' (hmod _ _ this)
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
  let φ := ZMod.castHom (dvd_mul_left M M0) (ZMod M)
  have hj1 : (j : ZMod M) = 1 := by
    have := congrArg φ hij
    rwa [map_mul, map_natCast, map_natCast, map_one, hi1, one_mul] at this
  have hdet : en h 0 0 * en h 1 1 - en h 0 1 * en h 1 0 = 1 := by
    have := h.2
    rwa [Matrix.det_fin_two] at this
  have hdet' : (en h 0 0 : ZMod (M0 * M)) * en h 1 1 - en h 0 1 * en h 1 0 = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ZMod (M0 * M)) hdet
  obtain ⟨γ, hγ⟩ := GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) (M0 * M)
    ⟨!![(en h 0 0 : ZMod (M0 * M)), j * en h 0 1; i * en h 1 0, en h 1 1], by
      rw [Matrix.det_fin_two_of]; linear_combination hdet' - (en h 0 1 : ZMod (M0 * M)) * (en h 1 0) * hij⟩
  have e : ∀ a b, (en γ a b : ZMod (M0 * M)) =
      !![(en h 0 0 : ZMod (M0 * M)), j * en h 0 1; i * en h 1 0, en h 1 1] a b := fun a b =>
    congrArg (fun m : SL(2, ZMod (M0 * M)) => m.1 a b) hγ
  have e00 : (en γ 0 0 : ZMod (M0 * M)) = en h 0 0 := e 0 0
  have e01 : (en γ 0 1 : ZMod (M0 * M)) = j * en h 0 1 := e 0 1
  have e10 : (en γ 1 0 : ZMod (M0 * M)) = i * en h 1 0 := e 1 0
  have e11 : (en γ 1 1 : ZMod (M0 * M)) = en h 1 1 := e 1 1
  refine ⟨γ * h⁻¹, ?_, ?_⟩
  · rw [mem_gam_iff]
    have f00 := congrArg φ e00
    have f01 := congrArg φ e01
    have f10 := congrArg φ e10
    have f11 := congrArg φ e11
    simp only [map_mul, map_intCast, map_natCast, hi1, hj1, one_mul] at f00 f01 f10 f11
    ext a b
    fin_cases a <;> fin_cases b
    exacts [f00, f01, f10, f11]
  · rw [inv_mul_cancel_right]
    refine X.recip (M0 * M) f (Nat.pos_of_ne_zero hM') (fun δ hδ => hf δ (gam_mono (dvd_mul_right _ _) hδ)) ζ hζ σ i
      (by rw [zpow_natCast, hi]) γ h ⟨e00.symm, ?_, ?_, e11.symm⟩
    · rw [e01, Int.cast_natCast, ← mul_assoc, hij, one_mul]
    · rw [e10, Int.cast_natCast]

private theorem trM_eq [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N M w : ℕ) [NeZero M] (g : SL(2, ℤ)) (x : X.Khat l) :
    trM X l N M w g x = trH X l w (fun γ : {γ // γ ∈ img (Gam N l) M} => liftSL M γ.1) ![en g 0 0, en g 0 1]
      (X.kmap l (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv x) := by
  unfold trM trH
  rw [← Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Tower.act_act Ω ε X l _ _ (by simp) (by simp)]
  congr 1
  funext u
  simp [Tower.act, sec, mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sTrM :
    UpperTheory.V.Z.Kato.Nb.STrM := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW a ha hI
  have hlp : l.Prime := Fact.out
  have hNM : N ∣ M := hL.eq ▸ dvd_mul_right _ _
  have hnM : l ^ n ∣ M := hL.eq ▸ hL.dl.mul_left _
  have hlM : l ∣ M := (dvd_pow_self l (by have := hL.pos; omega)).trans hnM
  obtain ⟨hE, hAdd, -, hSum, hDv, -⟩ := sApi Ω ε X l n
  obtain ⟨hR, -, -, hCg, hMap, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, hTo, -, hUn, -, -, hCy⟩ := sSlD Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))
  refine ⟨?_, fun σ hσ => ?_⟩
  · have hle : CongruenceSubgroup.Gamma M ≤ Gam N l ⊓ CongruenceSubgroup.Gamma (l ^ n) :=
      le_inf (gam_le hNM hlM) (gam_mono hnM)
    have hT := isTr_img (l := l) hNM hlM
    have hRep : Rep X l n (slU X (ofSL g) a)
        (X.kmap l (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (a : X.K))) := by
      rw [hTo]; exact hMap _ _ _ (hR a)
    have hU := hUn _ (ofSL g) a ha
    have hH : InvH X (CongruenceSubgroup.Gamma M) (l ^ n) (slU X (ofSL g) a) := by
      intro γ hγ
      obtain ⟨k, hk⟩ := hI _ ((CongruenceSubgroup.Gamma_normal M).conj_mem γ hγ g)
      refine ⟨slU X (ofSL g) k, ?_⟩
      show X.sl (ofSL γ) (X.sl (ofSL g) a) = X.sl (ofSL g) a * (X.sl (ofSL g) k) ^ l ^ n
      rw [← map_pow, ← map_mul, ← hk, ← X.sl_mul, ← X.sl_mul, ← map_mul, ← map_mul, inv_mul_cancel_right]
    obtain ⟨h1, h2, -⟩ := trc ε X l N w n _ hle _ _ hT ![en g 0 0, en g 0 1] _ _ hRep
    rw [trM_eq]
    exact ⟨⟨_, h1 hU, hE.refl _⟩, h2 hH, hW n _ M (Nat.pos_of_ne_zero (NeZero.ne M)) le_rfl hle _ _ hT _ _ _ hU hH hRep⟩
  · haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hlp.ne_zero⟩
    haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow (by have := hL.pos; omega) hlp.one_lt⟩
    have hσ' : σ ∈ fixMu Ω (l ^ n) := by
      rw [mem_fixMu_iff] at hσ ⊢
      intro z hz
      obtain ⟨c, hc⟩ := hnM
      exact hσ z (by rw [hc, pow_mul, hz, one_pow])
    have hχ := (sCycZ Ω l n σ).2
    rw [(hCy (l ^ n) σ).2.2.2.1.1 hσ', Units.val_one, ZMod.val_one, Nat.cast_one] at hχ
    unfold trM
    rw [map_sum]
    refine hSum _ _ _ _ fun γ _ u => ?_
    generalize g * liftSL M γ = h
    obtain ⟨δ, hδ, e⟩ := recip_mod X (NeZero.ne M) hσ (a : X.K) h
    obtain ⟨k, hk⟩ := hI δ hδ
    set A := X.kmap l (X.gal σ) (X.kmap l (X.sl (ofSL h)).toRingEquiv (clsK X l n (a : X.K))) with hA
    set B := X.kmap l (X.sl (ofSL h)).toRingEquiv (clsK X l n (X.gal σ a)) with hB
    have rA : Rep X l n (galU X σ (slU X (ofSL h) a)) A := hMap _ _ _ (hMap _ _ _ (hR a))
    have rB : Rep X l n (slU X (ofSL h) (galU X σ a)) B := hMap _ _ _ (hR (galU X σ a))
    have hBA := hCg _ _ _ _ rB rA ⟨galU X σ (slU X (ofSL h) k), Units.ext (by
      show X.sl (ofSL h) (X.gal σ a) = X.gal σ (X.sl (ofSL h) a) * (X.gal σ (X.sl (ofSL h) k)) ^ l ^ n
      rw [← e, map_mul, X.sl_mul, hk, map_mul, map_pow, map_mul, map_pow])⟩
    set c := (mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, (cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) * u 1]) 0 with hc
    set c' := (mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 with hc'
    have hcc : (l : ℤ_[l]) ^ n ∣ c ^ w - c' ^ w := by
      refine Dvd.dvd.trans ?_ (sub_dvd_pow_sub_pow c c' w)
      obtain ⟨t, ht⟩ := hχ
      refine ⟨mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * t * u 1, ?_⟩
      simp only [hc, hc', Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * u 1) * ht
    have h3 := hDv _ _ A hcc
    show AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.gal σ) (X.kmap l (X.sl (toGQ (h : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (c ^ w • clsK X l n (a : X.K))) - X.kmap l (X.sl (toGQ (h : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (c' ^ w • clsK X l n (X.gal σ a))) = 0
    rw [hTo, map_smul, map_smul, map_smul, ← hA, ← hB]
    have : c ^ w • A - c' ^ w • B = (c ^ w • A - c' ^ w • A) - c' ^ w • (B - A) := by
      rw [smul_sub]; abel
    rw [this, map_sub, h3, map_smul, hBA, smul_zero, sub_zero]
